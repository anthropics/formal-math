#!/usr/bin/env python3
"""Serialize exact dyadic-14 tree with globally deduplicated rational scalar seam certificates."""
from __future__ import annotations
import argparse,bisect,hashlib,json,os,struct,time
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from replay_exact_5d_bnb import A,B,CUTOFF,PARTIALS,VECTORS,WEIGHTS,Checker,Piece,model_min

def q(s):return F(s)
def qs(x):return str(x.numerator) if x.denominator==1 else f'{x.numerator}/{x.denominator}'
def read_pieces(path):
 raw=json.loads(path.read_text());out=[]
 for p in raw['pieces']:
  lo,hi=q(p['lo']),q(p['hi']);kind=p['kind']
  if kind=='low':out.append(Piece(lo,hi,F(0),F(1,4),F(0),kind))
  elif kind=='zero':out.append(Piece(lo,hi,F(0),F(0),F(0),kind))
  elif kind=='barrier':out.append(Piece(lo,hi,F(0),q(p['a']),F(0),kind))
  elif kind=='well':
   m,v,e=q(p['m']),q(p['v']),q(p['q']);center=e+v/m if p['side']=='left' else e-v/m
   out.append(Piece(lo,hi,center,F(0),2*m*m,kind))
 assert len(out)==56 and all(a.hi==b.lo for a,b in zip(out,out[1:]));return out
class ScalarChecker(Checker):
 def __init__(self,pieces):super().__init__(pieces,1<<34);self.ids={};self.certs=[]
 def scalar_id(self,lo,hi):
  value=self.scalar_min(lo,hi)
  if value==0:return 65535,value
  key=(lo,min(hi,CUTOFF))
  if key not in self.ids:
   cid=len(self.certs);self.ids[key]=cid;segments=[]
   for idx,p in enumerate(self.pieces):
    L=max(key[0],p.lo);H=min(key[1],p.hi)
    if L<=H:segments.append({'lo':qs(L),'hi':qs(H),'piece_index':idx,'model_min':qs(model_min(p,L,H))})
   assert segments and min(q(s['model_min']) for s in segments)==value
   assert segments[0]['lo']==qs(key[0]) and segments[-1]['hi']==qs(key[1])
   self.certs.append({'lo':qs(key[0]),'hi':qs(key[1]),'a':qs(value),'segments':segments})
  return 32768+self.ids[key],value
 def data(self,box):
  M=[[F(0) for _ in range(5)] for _ in range(5)];L=[B]*5;c=F(0);codes=[]
  for vector,(li,ri) in zip(VECTORS,PARTIALS):
   lo=sum((box[k][0] for k in range(li,ri+1)),F(0));hi=sum((box[k][1] for k in range(li,ri+1)),F(0));clip=min(hi,CUTOFF);piece=self.containing(lo,clip)
   if piece is None:
    code,value=self.scalar_id(lo,clip);codes.append(code);c+=value;continue
   idx=self.pieces.index(piece);codes.append(idx);c+=piece.a+piece.c*piece.q*piece.q
   if piece.c:
    for r in range(5):
     if not vector[r]:continue
     L[r]-=2*piece.c*piece.q
     for col in range(5):
      if vector[col]:M[r][col]+=piece.c
  return M,L,c,codes

def poly(M,L,c,z):return c+sum(L[i]*z[i] for i in range(5))+sum(M[i][j]*z[i]*z[j] for i in range(5) for j in range(5))
def tangent(M,L,c,box,z):
 v=poly(M,L,c,z);grad=[L[i]+2*sum(M[i][j]*z[j] for j in range(5)) for i in range(5)]
 return v+sum(min(grad[i]*(box[i][0]-z[i]),grad[i]*(box[i][1]-z[i])) for i in range(5))
def nearest(x):
 if x<0:return -nearest(-x)
 return (2*x.numerator+x.denominator)//(2*x.denominator)
def anchor14(proposal,box):
 codes=[];z=[]
 for v,(lo,hi) in zip(proposal,box):
  code=0 if lo==hi else min(max(nearest((v-lo)/(hi-lo)*16384),0),16384);codes.append(code);z.append(lo+F(code,16384)*(hi-lo))
 return codes,z
def atomic(path,data):tmp=path.with_suffix(path.suffix+'.new');tmp.write_bytes(data);os.replace(tmp,path)
def pack(tokens):
 words=[]
 for start in range(0,len(tokens),20):
  w=sum(t<<(3*j) for j,t in enumerate(tokens[start:start+20]));assert w<1<<60;words.append(w)
 return b''.join(struct.pack('<Q',w) for w in words),words

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--data',type=Path,required=True);ap.add_argument('--output-dir',type=Path,required=True);ap.add_argument('--max-nodes',type=int,default=1000000);ap.add_argument('--progress',type=int,default=25000);args=ap.parse_args()
 pieces=read_pieces(args.data);ck=ScalarChecker(pieces);root=tuple((F(0),F(59)) for _ in range(5));stack=[(root,0)];tokens=[];kinds=bytearray();anchors=bytearray();terms=bytearray();visited=leaves=tail=quad=maxdepth=0;smallest=None;started=time.monotonic();termhist=Counter()
 while stack:
  box,depth=stack.pop();visited+=1;maxdepth=max(maxdepth,depth)
  if visited>args.max_nodes:raise ArithmeticError('node limit')
  if B*sum((b[0] for b in box),F(0))>=A:tokens.append(0);kinds.append(0);leaves+=1;tail+=1;continue
  M,L,c,tcodes=ck.data(box);pf=ck.float_coordinate_descent(M,L,box,12);p=ck.rationalize(pf,box);ac,z=anchor14(p,box);lower=tangent(M,L,c,box,z)
  if lower>=A:
   tokens.append(0);kinds.append(1);leaves+=1;quad+=1;margin=lower-A;smallest=margin if smallest is None else min(smallest,margin)
   for x in ac:anchors.extend(struct.pack('<H',x))
   for x in tcodes:terms.extend(struct.pack('<H',x));termhist[x]+=1
   continue
  widths=[(hi-lo)*WEIGHTS[i] for i,(lo,hi) in enumerate(box)];axis=max(range(5),key=widths.__getitem__);tokens.append(axis+1);lo,hi=box[axis];mid=(lo+hi)/2;left=list(box);right=list(box);left[axis]=(lo,mid);right[axis]=(mid,hi);stack.append((tuple(right),depth+1));stack.append((tuple(left),depth+1))
  if args.progress and visited%args.progress==0:print(f'progress visited={visited} pending={len(stack)} depth={maxdepth} seconds={time.monotonic()-started:.1f}',flush=True)
 packed,words=pack(tokens);args.output_dir.mkdir(parents=True,exist_ok=True);paths={'topology':args.output_dir/'topology-u64le.bin','kinds':args.output_dir/'terminal-kinds-u8.bin','anchors':args.output_dir/'anchors-u16le.bin','terms':args.output_dir/'term-codes-u16le.bin'}
 for k,d in [('topology',packed),('kinds',bytes(kinds)),('anchors',bytes(anchors)),('terms',bytes(terms))]:atomic(paths[k],d)
 certpath=args.output_dir/'scalar-certificates.json';tmp=certpath.with_suffix('.json.new');tmp.write_text(json.dumps({'data_sha256':hashlib.sha256(args.data.read_bytes()).hexdigest(),'certificates':ck.certs},indent=2,sort_keys=True)+'\n');os.replace(tmp,certpath)
 report={'format':{'topology':'20 3-bit tokens/u64le, zero padding','kinds':'u8 0 tail/1 quadratic','anchors':'5*u16le denominator16384','terms':'15*u16le: 0..55 piece; 32768+scalar cert; 65535 zero'},'data_sha256':hashlib.sha256(args.data.read_bytes()).hexdigest(),'scalar_certificate_count':len(ck.certs),'scalar_certificates_sha256':hashlib.sha256(certpath.read_bytes()).hexdigest(),'token_count':len(tokens),'topology_word_count':len(words),'visited_nodes':visited,'leaves':leaves,'tail_leaves':tail,'quadratic_leaves':quad,'maximum_depth':maxdepth,'fuel':maxdepth+1,'smallest_margin':str(smallest),'smallest_margin_float':float(smallest),'zero_term_count':termhist[65535],'scalar_term_count':sum(v for k,v in termhist.items() if 32768<=k<65535),'stream_bytes':{k:p.stat().st_size for k,p in paths.items()},'stream_sha256':{k:hashlib.sha256(p.read_bytes()).hexdigest() for k,p in paths.items()},'elapsed_seconds':time.monotonic()-started,'trust_note':'All terminals use exact Fraction checks at stored dyadic-14 anchors.'}
 tmp=args.output_dir/'manifest.json.new';tmp.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');os.replace(tmp,args.output_dir/'manifest.json');print(json.dumps(report,indent=2,sort_keys=True))
if __name__=='__main__':main()
