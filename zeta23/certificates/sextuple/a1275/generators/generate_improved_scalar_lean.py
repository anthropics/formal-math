#!/usr/bin/env python3
# Deterministically emit fail-closed Lean scalar certificates for A=51/4000.
from __future__ import annotations
import hashlib, json
from fractions import Fraction
from pathlib import Path

HERE=Path(__file__).resolve().parent
SOURCE=Path("/Users/mdumitrean/Desktop/dev/aigent/math/prime/post-anthropic-rh-artifacts/checkers/sextuple-improvement/refined-A-0p01275/scalar-certificates.json")
OUT=HERE/"ImprovedScalarData.lean"
REPORT=HERE/"improved-scalar-lean-generation-report.json"
EXPECTED_SOURCE_SHA256="66264d3d9bc6cd0cde88f4d1bdb946ad3c8a64053d73d45a29176cdb8611dfe7"
TABLE_COUNT=272
EXPECTED_COUNT=1383
EXPECTED_SEGMENTS=2979

def sha(p:Path)->str:return hashlib.sha256(p.read_bytes()).hexdigest()
def q(x:str)->Fraction:return Fraction(x)
def fmt(x:Fraction)->str:
    return str(x.numerator) if x.denominator==1 else f"({x.numerator}/{x.denominator})"
def box(lo:Fraction,hi:Fraction)->str:return f"⟨{fmt(lo)}, {fmt(hi)}⟩"
def canonical(obj)->bytes:return (json.dumps(obj,sort_keys=True,separators=(",",":"))+"\n").encode()

def validate(obj):
    assert obj["schema"]==1 and obj["A"]=="51/4000"
    assert obj["B"]=="1094977/5000000000" and obj["cutoff"]=="63750000/1094977"
    certs=obj["certificates"];assert len(certs)==EXPECTED_COUNT
    seg_count=0
    for c in certs:
        assert set(c)=={"a","lo","hi","segments"}
        lo,hi,a=q(c["lo"]),q(c["hi"]),q(c["a"]);assert lo<=hi
        segs=c["segments"];assert segs
        assert q(segs[0]["lo"])==lo and q(segs[-1]["hi"])==hi
        for j,s in enumerate(segs):
            assert set(s)=={"lo","hi","model_min","piece_index"}
            slo,shi,mm=q(s["lo"]),q(s["hi"]),q(s["model_min"])
            assert slo<=shi and a<=mm
            if j:assert q(segs[j-1]["hi"])==slo
            idx=s["piece_index"]
            assert type(idx) is int and 0<=idx<TABLE_COUNT
            seg_count+=1
    assert seg_count==EXPECTED_SEGMENTS
    return certs

def emit_cert(i,c):
    segs=[]
    for s in c["segments"]:
        idx=s["piece_index"]
        # Explicit proof-bearing constructor is required: bare Fin numerals wrap modulo the bound.
        segs.append(f'    {{ box := {box(q(s["lo"]),q(s["hi"]))}, pieceIndex := ⟨{idx}, by decide⟩ }}')
    return f'''def improvedScalarCert{i} : MacroScalarCert {TABLE_COUNT} := {{
  box := {box(q(c["lo"]),q(c["hi"]))}
  a := {fmt(q(c["a"]))}
  segments := [
{",\n".join(segs)}
  ]
}}'''

def emit_check(i,c):
    used=sorted({s["piece_index"] for s in c["segments"]})
    defs=", ".join(f"macroPiece{x}" for x in used)
    return f'''lemma improvedScalarCert{i}_check : improvedScalarCert{i}.check improvedCatalog = true := by
  norm_num [improvedScalarCert{i}, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, improvedCatalog, stableMacroTable, {defs}]'''

def main():
    assert sha(SOURCE)==EXPECTED_SOURCE_SHA256
    obj=json.loads(SOURCE.read_text());certs=validate(obj)
    defs="\n".join(emit_cert(i,c) for i,c in enumerate(certs))
    checks="\n".join(emit_check(i,c) for i,c in enumerate(certs))
    table="\n".join([f"  | {i} => improvedScalarCert{i}" for i in range(EXPECTED_COUNT-1)]+[f"  | _ => improvedScalarCert{EXPECTED_COUNT-1}"])
    bullets="\n".join(f"  · exact improvedScalarCert{i}_check" for i in range(EXPECTED_COUNT))
    source=f'''import ImprovedCatalog

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple
open RatInterval

set_option maxRecDepth 1000000

{defs}

{checks}

/-- Frozen exact scalar seam certificates for A=51/4000. -/
def improvedScalarTable (i : Fin {EXPECTED_COUNT}) : MacroScalarCert {TABLE_COUNT} :=
  match i.val with
{table}

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem improvedScalarTable_check (i : Fin {EXPECTED_COUNT}) :
    (improvedScalarTable i).check improvedCatalog = true := by
  fin_cases i
{bullets}

#print axioms improvedScalarTable_check

end Zeta23.ThmD.Sextuple.MacroPrototype
'''
    OUT.write_text(source)
    assert "pieceIndex := ⟨" in source and "pieceIndex := 0" not in source
    assert source.count("pieceIndex := ⟨")==EXPECTED_SEGMENTS
    report={"schema":1,"status":"PASS","generator_sha256":sha(Path(__file__)),
      "input_sha256":EXPECTED_SOURCE_SHA256,"output_sha256":sha(OUT),"output_bytes":OUT.stat().st_size,
      "table_count":TABLE_COUNT,"certificate_count":EXPECTED_COUNT,"segment_count":EXPECTED_SEGMENTS,
      "fin_encoding":"explicit-constructor-with-decide-proof"}
    REPORT.write_bytes(canonical(report));print(json.dumps(report,indent=2,sort_keys=True))
if __name__=="__main__":main()
