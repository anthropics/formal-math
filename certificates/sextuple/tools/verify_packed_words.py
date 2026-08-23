#!/usr/bin/env python3
"""Independent check that MacroTreeWords.lean encodes exactly the canonical serialized streams.

Parses the two array literals out of the Lean source, decodes them back into the four
physical byte streams, and compares SHA-256 digests with macro-scalar-tree/manifest.json.
"""
from __future__ import annotations
import hashlib, json, re, struct, sys
from pathlib import Path
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;TREE=HERE.parent/'macro-scalar-tree'
LEAF_BITS=321;BLOCK=256
SRC=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'MacroTreeWords.lean'
src=SRC.read_text()
def arr(name):
    m=re.search(r'def '+name+r' : Array ℕ := #\[(.*?)\]',src,re.S);return [int(x) for x in m.group(1).replace('\n',' ').split(',')]
tokenCount=int(re.search(r'def tokenCount : ℕ := (\d+)',src).group(1));leafCount=int(re.search(r'def leafCount : ℕ := (\d+)',src).group(1))
words=arr('topologyWords');blocks=arr('leafBlocks')
manifest=json.loads((TREE/'manifest.json').read_text())
assert tokenCount==manifest['token_count'] and leafCount==manifest['leaves']
assert len(words)==(tokenCount+19)//20 and all(w<1<<60 for w in words)
rem=tokenCount%20
if rem: assert words[-1]<1<<(3*rem)
topo=b''.join(struct.pack('<Q',w) for w in words)
assert len(blocks)==(leafCount+BLOCK-1)//BLOCK and all(b<1<<(LEAF_BITS*BLOCK) for b in blocks)
lw=[]
for b in blocks:
    for j in range(BLOCK):
        lw.append((b>>(LEAF_BITS*j))&((1<<LEAF_BITS)-1))
assert all(w==0 for w in lw[leafCount:]);lw=lw[:leafCount]
kinds=bytearray();anchors=bytearray();terms=bytearray()
for w in lw:
    if w==0: kinds.append(0);continue
    assert w&1==1;kinds.append(1)
    for i in range(5): anchors+=struct.pack('<H',(w>>(1+16*i))&65535)
    for i in range(15): terms+=struct.pack('<H',(w>>(1+16*(5+i)))&65535)
    assert w>>(1+16*20)==0
digests={'topology':hashlib.sha256(topo).hexdigest(),'kinds':hashlib.sha256(bytes(kinds)).hexdigest(),'anchors':hashlib.sha256(bytes(anchors)).hexdigest(),'terms':hashlib.sha256(bytes(terms)).hexdigest()}
ok=all(digests[k]==manifest['stream_sha256'][k] for k in digests)
sizes={'topology':len(topo),'kinds':len(kinds),'anchors':len(anchors),'terms':len(terms)}
assert sizes==manifest['stream_bytes'],sizes
report={'lean_source':str(SRC),'status':'PASS' if ok else 'FAIL','lean_source_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'decoded_stream_sha256':digests,'manifest_stream_sha256':manifest['stream_sha256'],'stream_bytes':sizes,'token_count':tokenCount,'leaf_count':leafCount,'topology_words':len(words),'leaf_blocks':len(blocks),'leaf_word_bits':LEAF_BITS,'leaf_block_size':BLOCK}
print(json.dumps(report,indent=2,sort_keys=True))
sys.exit(0 if ok else 1)
