#!/usr/bin/env python3
"""Decode the serialized macro-scalar tree into explicit per-node data (exact Fractions).

Replays the DFS exactly as verify_macro_scalar_tree.py does and exposes:
  * every quadratic leaf: (box, anchor codes, term codes, tangent margin)
  * every node at a chosen cut depth: (topology cursor, payload cursor, box) before/after
"""
from __future__ import annotations
import json, struct
from fractions import Fraction as F
from pathlib import Path
A=F(1,80);B=F(1094977,5000000000);CUTOFF=A/B
PARTIALS=tuple((i,j) for i in range(5) for j in range(i,5))
VECTORS=tuple(tuple(1 if i<=k<=j else 0 for k in range(5)) for i,j in PARTIALS)
TREE=Path(__file__).resolve().parent.parent/'macro-scalar-tree'
DATA=Path(__file__).resolve().parent.parent/'macro-data-exact.json'

def q(x):return F(x)
def qs(x):
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'

class Piece:
    def __init__(s,lo,hi,q,a,c):s.lo,s.hi,s.q,s.a,s.c=lo,hi,q,a,c
def read_pieces():
    raw=json.loads(DATA.read_text());out=[]
    for p in raw['pieces']:
        lo,hi=q(p['lo']),q(p['hi']);kind=p['kind']
        if kind=='low':out.append(Piece(lo,hi,F(0),F(1,4),F(0)))
        elif kind=='zero':out.append(Piece(lo,hi,F(0),F(0),F(0)))
        elif kind=='barrier':out.append(Piece(lo,hi,F(0),q(p['a']),F(0)))
        elif kind=='well':
            m,v,e=q(p['m']),q(p['v']),q(p['q']);out.append(Piece(lo,hi,e+v/m if p['side']=='left' else e-v/m,F(0),2*m*m))
    return out

def load():
    manifest=json.loads((TREE/'manifest.json').read_text())
    certs=json.loads((TREE/'scalar-certificates.json').read_text())['certificates']
    tc=manifest['token_count'];wc=(tc+19)//20
    words=list(struct.unpack('<'+'Q'*wc,(TREE/'topology-u64le.bin').read_bytes()))
    tokens=[(words[i//20]>>(3*(i%20)))&7 for i in range(tc)]
    kinds=(TREE/'terminal-kinds-u8.bin').read_bytes()
    an=(TREE/'anchors-u16le.bin').read_bytes();tm=(TREE/'term-codes-u16le.bin').read_bytes()
    acodes=list(struct.unpack('<'+'H'*(len(an)//2),an));tcodes=list(struct.unpack('<'+'H'*(len(tm)//2),tm))
    return manifest,certs,words,tokens,kinds,acodes,tcodes

def tangent(M,L,c,box,z):
    value=c+sum(L[i]*z[i] for i in range(5))+sum(M[i][j]*z[i]*z[j] for i in range(5) for j in range(5))
    grad=[L[i]+2*sum(M[i][j]*z[j] for j in range(5)) for i in range(5)]
    return value+sum(min(grad[i]*(box[i][0]-z[i]),grad[i]*(box[i][1]-z[i])) for i in range(5))

def walk(cut_depth=None):
    """Return (leaves, chunks). leaves: list of dict for quadratic leaves in DFS order.
    chunks: list of (t_start,p_start,t_end,p_end,box,depth) for every node at depth==cut_depth,
    plus for shallower terminal nodes (depth<cut_depth)."""
    manifest,certs,words,tokens,kinds,acodes,tcodes=load();pieces=read_pieces()
    # explicit stack DFS replicating replayAffineTree: left child first
    leaves=[];chunks=[]
    tc=kc=qc=0
    root=tuple((F(0),F(59)) for _ in range(5))
    def rec(box,depth):
        nonlocal tc,kc,qc
        t0,p0=tc,kc
        tok=tokens[tc];tc+=1
        if tok:
            axis=tok-1;lo,hi=box[axis];mid=(lo+hi)/2
            left=list(box);right=list(box);left[axis]=(lo,mid);right[axis]=(mid,hi)
            if cut_depth is not None and depth==cut_depth:
                # replay whole subtree without recording chunks below
                rec_sub(tuple(left),depth+1);rec_sub(tuple(right),depth+1)
                chunks.append(dict(t0=t0,p0=p0,t1=tc,p1=kc,box=box,depth=depth,terminal=False))
                return
            rec(tuple(left),depth+1);rec(tuple(right),depth+1)
            return
        kind=kinds[kc];kc+=1
        leaf=terminal(box,kind,depth)
        if cut_depth is not None and depth<=cut_depth:
            chunks.append(dict(t0=t0,p0=p0,t1=tc,p1=kc,box=box,depth=depth,terminal=True))
    def rec_sub(box,depth):
        nonlocal tc,kc,qc
        tok=tokens[tc];tc+=1
        if tok:
            axis=tok-1;lo,hi=box[axis];mid=(lo+hi)/2
            left=list(box);right=list(box);left[axis]=(lo,mid);right[axis]=(mid,hi)
            rec_sub(tuple(left),depth+1);rec_sub(tuple(right),depth+1);return
        kind=kinds[kc];kc+=1
        terminal(box,kind,depth)
    def terminal(box,kind,depth):
        nonlocal qc
        if kind==0:
            assert B*sum((x[0] for x in box),F(0))>=A
            leaves.append(dict(kind=0,box=box,depth=depth));return
        codes=acodes[5*qc:5*qc+5];term=tcodes[15*qc:15*qc+15];qc+=1
        z=[lo+F(code,16384)*(hi-lo) for code,(lo,hi) in zip(codes,box)]
        M=[[F(0)]*5 for _ in range(5)];L=[B]*5;c=F(0)
        for vector,(li,ri),code in zip(VECTORS,PARTIALS,term):
            if code==65535:continue
            if code<56:
                piece=pieces[code];c+=piece.a+piece.c*piece.q*piece.q
                if piece.c:
                    for r in range(5):
                        if not vector[r]:continue
                        L[r]-=2*piece.c*piece.q
                        for col in range(5):
                            if vector[col]:M[r][col]+=piece.c
            else:
                c+=q(certs[code-32768]['a'])
        margin=tangent(M,L,c,box,z)-A;assert margin>=0
        leaves.append(dict(kind=1,box=box,anchor=codes,terms=term,margin=margin,depth=depth))
    import sys;sys.setrecursionlimit(10000)
    rec(root,0)
    assert tc==len(tokens) and kc==len(kinds) and qc==manifest['quadratic_leaves']
    return leaves,chunks,manifest

def lean_box(box):
    los=', '.join(qs(lo) for lo,hi in box);his=', '.join(qs(hi) for lo,hi in box)
    return f'⟨![{los}], ![{his}]⟩'

if __name__=='__main__':
    import sys
    leaves,chunks,manifest=walk(cut_depth=int(sys.argv[1]) if len(sys.argv)>1 else None)
    print('leaves',len(leaves),'quadratic',sum(1 for l in leaves if l['kind']==1),'chunks',len(chunks))
    if chunks:
        sizes=[c['t1']-c['t0'] for c in chunks]
        print('chunk token sizes: max',max(sizes),'min',min(sizes),'mean',sum(sizes)/len(sizes))
