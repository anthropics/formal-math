#!/usr/bin/env python3
"""Exact B&B with the v2 catalog. Same CLI as generate_exact_refined_scalar_tree.py plus --refinements2."""
from __future__ import annotations
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1])); sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_exact_refined_scalar_tree_limit as G
from catalog_v2 import read_refinements_v2, RefinedCheckerV2
if "--refinements2" not in sys.argv: raise SystemExit("--refinements2 PATH required")
i = sys.argv.index("--refinements2"); V2 = Path(sys.argv[i + 1]); del sys.argv[i:i + 2]
_state = {}
def _read(path: Path):
    pieces, owners = read_refinements_v2(path, V2); _state["owners"] = owners; return pieces
def _checker(stable, refinements, A, B):
    return RefinedCheckerV2(stable, refinements, _state["owners"], A, B)
G.read_refinements = _read
G.RefinedChecker = _checker
G.main()
