#!/usr/bin/env python3
"""Independent serialized-only exact verifier for the scalar-cache macro tree."""
from __future__ import annotations
import argparse,hashlib,json,struct,time
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
A=F(1,80);B=F(1094977,5000000000);CUTOFF=A/B
PARTIALS=tuple((i,j) for i in range(5) for j in range(i,5));VECTORS=tuple(tuple(F(1) if i<=k<=j else F(0) for k in range(5)) for i,j in PARTIALS)
@dataclass(frozen=True)
class Piece:lo:F;hi:F;q:F;a:F;c:F
def q(x):return F(x)
def read_pieces(path):
 raw=json.loads(path.read_text());out=[]
 for p in raw['pieces']:
  lo,hi=q(p['lo']),q(p['hi']);kind=p['kind']
  if kind=='low':out.append(Piece(lo,hi,F(0),F(1,4),F(0)))
  elif kind=='zero':out.append(Piece(lo,hi,F(0),F(0),F(0)))
  elif kind=='barrier':out.append(Piece(lo,hi,F(0),q(p['a']),F(0)))
  elif kind=='well':
   m,v,e=q(p['m']),q(p['v']),q(p['q']);out.append(Piece(lo,hi,e+v/m if p['side']=='left' else e-v/m,F(0),2*m*m))
 assert len(out)==56 and out[0].lo==0 and out[-1].hi==59 and all(a.hi==b.lo for a,b in zip(out,out[1:]));return out
def model_min(p,lo,hi):
 z=p.q if lo<=p.q<=hi else lo if p.q<lo else hi;return p.a+p.c*(z-p.q)**2
def read_exact(path,n):
 data=path.read_bytes();assert len(data)==n,(path,len(data),n);return data
def tangent(M,L,c,box,z):
 value=c+sum(L[i]*z[i] for i in range(5))+sum(M[i][j]*z[i]*z[j] for i in range(5) for j in range(5));grad=[L[i]+2*sum(M[i][j]*z[j] for j in range(5)) for i in range(5)];return value+sum(min(grad[i]*(box[i][0]-z[i]),grad[i]*(box[i][1]-z[i])) for i in range(5))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--data',type=Path,required=True);ap.add_argument('--tree-dir',type=Path,required=True);ap.add_argument('--report',type=Path,required=True);args=ap.parse_args();started=time.monotonic();manifest=json.loads((args.tree_dir/'manifest.json').read_text());pieces=read_pieces(args.data)
 certpath=args.tree_dir/'scalar-certificates.json';assert hashlib.sha256(certpath.read_bytes()).hexdigest()==manifest['scalar_certificates_sha256'];certs=json.loads(certpath.read_text())['certificates'];assert len(certs)==manifest['scalar_certificate_count']
 for cert in certs:
  lo,hi,a=q(cert['lo']),q(cert['hi']),q(cert['a']);segs=cert['segments'];assert lo<=hi and a>0 and segs
  cur=lo
  for seg in segs:
   L,H,idx=q(seg['lo']),q(seg['hi']),seg['piece_index'];assert L==cur and L<=H and 0<=idx<56;piece=pieces[idx];assert piece.lo<=L and H<=piece.hi;assert q(seg['model_min'])==model_min(piece,L,H);assert a<=q(seg['model_min']);cur=H
  assert cur==hi
 token_count=manifest['token_count'];word_count=(token_count+19)//20;top=read_exact(args.tree_dir/'topology-u64le.bin',8*word_count);words=list(struct.unpack('<'+'Q'*word_count,top));assert all(w<1<<60 for w in words)
 rem=token_count%20
 if rem:assert words[-1] < 1<<(3*rem)
 tokens=[(words[i//20]>>(3*(i%20)))&7 for i in range(token_count)];assert all(t<=5 for t in tokens)
 kinds=read_exact(args.tree_dir/'terminal-kinds-u8.bin',manifest['leaves']);assert all(k<=1 for k in kinds)
 anchors=read_exact(args.tree_dir/'anchors-u16le.bin',manifest['quadratic_leaves']*10);terms=read_exact(args.tree_dir/'term-codes-u16le.bin',manifest['quadratic_leaves']*30)
 acodes=list(struct.unpack('<'+'H'*(len(anchors)//2),anchors));tcodes=list(struct.unpack('<'+'H'*(len(terms)//2),terms));assert all(x<=16384 for x in acodes)
 stack=[(tuple((F(0),F(59)) for _ in range(5)),0)];tc=kc=qc=0;tail=quad=0;maxdepth=0;smallest=None
 while stack:
  box,depth=stack.pop();maxdepth=max(maxdepth,depth);assert tc<token_count;tok=tokens[tc];tc+=1
  if tok:
   axis=tok-1;lo,hi=box[axis];mid=(lo+hi)/2;left=list(box);right=list(box);left[axis]=(lo,mid);right[axis]=(mid,hi);stack.append((tuple(right),depth+1));stack.append((tuple(left),depth+1));continue
  assert kc<len(kinds);kind=kinds[kc];kc+=1
  if kind==0:assert B*sum((x[0] for x in box),F(0))>=A;tail+=1;continue
  assert qc<manifest['quadratic_leaves'];codes=acodes[5*qc:5*qc+5];term=tcodes[15*qc:15*qc+15];qc+=1;z=[lo+F(code,16384)*(hi-lo) for code,(lo,hi) in zip(codes,box)]
  M=[[F(0) for _ in range(5)] for _ in range(5)];L=[B]*5;c=F(0)
  for vector,(li,ri),code in zip(VECTORS,PARTIALS,term):
   dlo=sum((box[k][0] for k in range(li,ri+1)),F(0));dhi=min(sum((box[k][1] for k in range(li,ri+1)),F(0)),CUTOFF)
   if code==65535:continue
   if code<56:piece=pieces[code];assert piece.lo<=dlo and dhi<=piece.hi;c+=piece.a+piece.c*piece.q*piece.q
   elif 32768<=code<32768+len(certs):cert=certs[code-32768];assert q(cert['lo'])<=dlo and dhi<=q(cert['hi']);c+=q(cert['a']);continue
   else:raise AssertionError(('bad term code',code))
   if piece.c:
    for r in range(5):
     if not vector[r]:continue
     L[r]-=2*piece.c*piece.q
     for col in range(5):
      if vector[col]:M[r][col]+=piece.c
  margin=tangent(M,L,c,box,z)-A;assert margin>=0;margin0=margin if smallest is None else min(smallest,margin);smallest=margin0;quad+=1
 assert not stack and tc==token_count and kc==len(kinds) and qc==manifest['quadratic_leaves'];assert tail==manifest['tail_leaves'] and quad==manifest['quadratic_leaves'] and maxdepth==manifest['maximum_depth']
 streams=['topology-u64le.bin','terminal-kinds-u8.bin','anchors-u16le.bin','term-codes-u16le.bin']
 for name in streams:
  key={'topology-u64le.bin':'topology','terminal-kinds-u8.bin':'kinds','anchors-u16le.bin':'anchors','term-codes-u16le.bin':'terms'}[name];assert hashlib.sha256((args.tree_dir/name).read_bytes()).hexdigest()==manifest['stream_sha256'][key]
 out={'status':'PASS','data_sha256':hashlib.sha256(args.data.read_bytes()).hexdigest(),'token_count':tc,'kind_cursor':kc,'quadratic_cursor':qc,'full_topology_exhaustion':tc==token_count,'full_kind_exhaustion':kc==len(kinds),'full_quadratic_exhaustion':qc==manifest['quadratic_leaves'],'maximum_depth':maxdepth,'tail_leaves':tail,'quadratic_leaves':quad,'scalar_certificate_count':len(certs),'smallest_margin':str(smallest),'smallest_margin_float':float(smallest),'elapsed_seconds':time.monotonic()-started}
 args.report.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
