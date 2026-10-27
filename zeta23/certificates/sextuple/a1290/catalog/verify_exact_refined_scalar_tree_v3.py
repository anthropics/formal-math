#!/usr/bin/env python3
"""Independent exact verifier for v2-catalog trees. Same CLI as verify_exact_refined_scalar_tree.py plus
--refinements2 PATH; the v2 catalog SHA-256 is recorded alongside the report."""
from __future__ import annotations
import hashlib, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1])); sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exact_refined_scalar_tree_limit as V
from catalog_v2 import read_refinements_v2
if "--refinements2" not in sys.argv: raise SystemExit("--refinements2 PATH required")
i = sys.argv.index("--refinements2"); V2 = Path(sys.argv[i + 1]); del sys.argv[i:i + 2]
def _read(path: Path):
    pieces, _owners = read_refinements_v2(path, V2); return pieces
V.read_refinements = _read
V.main()
rep = Path(sys.argv[sys.argv.index("--report") + 1])
d = json.loads(rep.read_text())
d["refinements2_sha256"] = hashlib.sha256(V2.read_bytes()).hexdigest()
d["refinements2_path"] = str(V2)
rep.write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
print("v2 verifier: refinements2_sha256 recorded", d["refinements2_sha256"][:16])
