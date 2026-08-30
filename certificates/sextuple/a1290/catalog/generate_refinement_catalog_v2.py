#!/usr/bin/env python3
"""Refinement catalog v2/v3: the 216 narrow wells of v1 (unchanged, indices 56..271 of the catalog) plus
  * 24 narrow-well cells on stable well piece 36 (38.138..38.513), proposed exactly as in v1;
  * constant-barrier cells of width 1/64 over stable barrier piece 43 (44.787..49.564), each with
    a = (floor to 1e-15 of Lean's own kernelRange lower bound for 2K^2 on the cell) - 1e-15.
Every emitted piece is re-checked by Lean (`WellCert.check` / `LowerPiece.check`); the JSON is not authority.
Outputs: refinement-catalog-v2.json (v2 pieces only, with their catalog indices starting at 272) and a Lean
module defining refinement2PieceN and refinement2Table."""
from __future__ import annotations
import hashlib, json, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1])); sys.path.insert(0, str(Path(__file__).resolve().parent))
import mpmath as mp
from generate_refinement_catalog import propose_piece, SIMP as WELL_SIMP, lean_q, qs, q
from kernel_interval import barrier_bound, cellCheck_ok
mp.mp.dps = 100
HERE = Path(__file__).resolve().parent
DATA = HERE.parents[1] / "lean-sextuple-certificate-prototype/macro-data-exact.json"
BARRIER_SIMP = ("MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,\n"
    "    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,\n"
    "    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,\n"
    "    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,\n"
    "    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,\n"
    "    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil")
Q = 10**15
EXTRA_WELLS = (36,)
BARRIERS = (43,)
EXTRA_RANGES = ((F(59), F(60)),)   # beyond the stable domain [0,59]: lets the root-box limit be 60 (A <= 60 B)
CELL = F(1, 64)
def main(out_json: Path, out_lean: Path, ns_module: str) -> None:
    src = json.loads(DATA.read_text())["pieces"]
    pieces = []
    for si in EXTRA_WELLS:
        for sub in range(24):
            p = propose_piece(si, src[si], sub); p["kind"] = "well"; pieces.append(p)
    for si in BARRIERS:
        lo0, hi0 = q(src[si]["lo"]), q(src[si]["hi"])
        n = int((hi0 - lo0) / CELL) + 1
        edges = [lo0 + CELL * k for k in range(n)] + [hi0]
        edges = [e for e in edges if e <= hi0]
        if edges[-1] != hi0: edges.append(hi0)
        for lo, hi in zip(edges, edges[1:]):
            if hi <= lo: continue
            turn, bound = barrier_bound(lo, hi)
            a = F(int(bound * Q) - 1, Q)
            if a < 0: a = F(0)
            if not cellCheck_ok(lo, hi, turn, a): raise SystemExit(f"replica rejects cell {lo}..{hi}")
            pieces.append({"kind": "barrier", "stable_piece_index": si, "lo": qs(lo), "hi": qs(hi), "a": qs(a),
                           "cells": [{"lo": qs(lo), "hi": qs(hi), "turn": turn}]})
    for lo0, hi0 in EXTRA_RANGES:
        n = int((hi0 - lo0) / CELL)
        edges = [lo0 + CELL * k for k in range(n + 1)]
        if edges[-1] != hi0: edges.append(hi0)
        for lo, hi in zip(edges, edges[1:]):
            turn, bound = barrier_bound(lo, hi)
            a = F(int(bound * Q) - 1, Q)
            if a < 0: a = F(0)
            if not cellCheck_ok(lo, hi, turn, a): raise SystemExit(f"replica rejects cell {lo}..{hi}")
            pieces.append({"kind": "barrier", "stable_piece_index": -1, "lo": qs(lo), "hi": qs(hi), "a": qs(a),
                           "cells": [{"lo": qs(lo), "hi": qs(hi), "turn": turn}]})
    base = 272
    for k, p in enumerate(pieces): p["catalog_index"] = base + k
    L = ["import Zeta23.ThmD.Sextuple.Macro.EnvelopeData", "", "namespace Zeta23.ThmD.Sextuple.MacroPrototype", "", "open RatInterval", "",
         "/-! Generated refinement catalog v2: narrow wells on stable piece 36 and 1/64-width constant barriers on stable",
         "piece 43. The stable 56-piece table and the v1 216-well catalog are unchanged. Every piece is Lean-checked. -/", ""]
    for k, p in enumerate(pieces):
        if p["kind"] == "well":
            L.append(f"def refinement2Piece{k} : MacroPiece := .well {{ box := ⟨{lean_q(q(p['lo']))}, {lean_q(q(p['hi']))}⟩, "
                     f"side := .{p['side']}, positive := {'true' if p['positive'] else 'false'}, q := {lean_q(q(p['q']))}, "
                     f"v := {lean_q(q(p['v']))}, m := {lean_q(q(p['m']))}, turn := {p['turn']} }}")
        else:
            c = p["cells"][0]
            L.append(f"def refinement2Piece{k} : MacroPiece := .base {{ box := ⟨{lean_q(q(p['lo']))}, {lean_q(q(p['hi']))}⟩, q := 0, a := {lean_q(q(p['a']))}, c := 0, kind := .numeric [\n"
                     f"      {{ box := ⟨{lean_q(q(c['lo']))}, {lean_q(q(c['hi']))}⟩, turn := {c['turn']} }}\n    ] }}")
    L.append("")
    for k, p in enumerate(pieces):
        simp = WELL_SIMP if p["kind"] == "well" else BARRIER_SIMP
        L.append(f"lemma refinement2Piece{k}_check : refinement2Piece{k}.check = true := by\n  norm_num [refinement2Piece{k}, {simp}]")
    n = len(pieces); G = 64
    L += ["", f"/-- The v2 refinement table (two-level match; catalog indices {base}..{base + n - 1}). -/",
          f"def refinement2Table (i : Fin {n}) : MacroPiece :=", f"  match i.val / {G}, i.val % {G} with"]
    L += [f"  | {k // G}, {k % G} => refinement2Piece{k}" for k in range(n)]
    L += ["  | _, _ => refinement2Piece0", "", f"theorem refinement2Table_check (i : Fin {n}) : (refinement2Table i).check = true := by", "  fin_cases i"]
    L += [f"  · exact refinement2Piece{k}_check" for k in range(n)]
    L += ["", "#print axioms refinement2Table_check", "", "end Zeta23.ThmD.Sextuple.MacroPrototype", ""]
    out_lean.write_text("\n".join(L))
    payload = {"schema": 2, "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "source_data_sha256": hashlib.sha256(DATA.read_bytes()).hexdigest(), "base_catalog_index": base,
               "extra_well_pieces": list(EXTRA_WELLS), "barrier_pieces": list(BARRIERS), "extra_ranges": [[qs(a), qs(b)] for a, b in EXTRA_RANGES], "barrier_cell_width": qs(CELL),
               "piece_count": n, "pieces": pieces}
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"v2 pieces: {n} (wells {sum(p['kind']=='well' for p in pieces)}, barriers {sum(p['kind']=='barrier' for p in pieces)}); catalog size {base + n}")
if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else "")
