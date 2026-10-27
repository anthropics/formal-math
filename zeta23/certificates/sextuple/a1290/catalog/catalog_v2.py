#!/usr/bin/env python3
"""Catalog v2 loader for the exact B&B: stable 56 + v1 216 wells + v2 pieces (wells and constant barriers).
Provides read_refinements_v2 (list of Piece, list of stable indices) and RefinedCheckerV2."""
from __future__ import annotations
import json, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from generate_exact_macro_tree import Piece, model_min, q
from generate_exact_refined_scalar_tree import RefinedChecker, read_refinements
V1_STABLE = (3, 9, 17, 23, 24, 27, 29, 35, 42)
def read_refinements_v2(v1_path: Path, v2_path: Path):
    v1 = read_refinements(v1_path)
    owners = [V1_STABLE[k // 24] for k in range(len(v1))]
    raw = json.loads(v2_path.read_text())
    if raw.get("schema") != 2 or raw["base_catalog_index"] != 56 + len(v1):
        raise SystemExit("catalog v2: schema/base index mismatch")
    v2 = []
    for k, item in enumerate(raw["pieces"]):
        if item["catalog_index"] != 56 + len(v1) + k: raise SystemExit("catalog v2: index gap")
        lo, hi = q(item["lo"]), q(item["hi"])
        if item["kind"] == "well":
            m, v, endpoint = q(item["m"]), q(item["v"]), q(item["q"])
            center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
            v2.append(Piece(lo, hi, center, F(0), 2 * m * m, "refinement"))
        elif item["kind"] == "barrier":
            v2.append(Piece(lo, hi, F(0), q(item["a"]), F(0), "refinement-barrier"))
        else:
            raise SystemExit(f"catalog v2: unknown kind {item['kind']}")
        owners.append(int(item["stable_piece_index"]))
    pieces = v1 + v2
    if not all(p.lo < p.hi and p.c >= 0 and p.a >= 0 for p in pieces): raise SystemExit("catalog v2: bad piece")
    return pieces, owners
class RefinedCheckerV2(RefinedChecker):
    def __init__(self, stable, refinements, owners, A, B):
        super().__init__(stable, refinements[:216], A, B)  # v1 part builds the base structures
        self.refinements = refinements
        self.catalog = stable + refinements
        groups: dict[int, list] = {}
        for k, (piece, owner) in enumerate(zip(refinements, owners)):
            groups.setdefault(owner, []).append((56 + k, piece))
        self.refinements_by_stable = groups
