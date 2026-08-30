# `A = 257/20000 = 0.01285` sextuple certificate: provenance, generators, audits, logs

Supporting material for the refined unconditional sextuple improvement
`Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple` (`0.67279494…`, public fixed constant
`6727949489/10^10`) and its kernel-checked five-dimensional certificate
`Zeta23.ThmD.Sextuple.A1285.Certificate.sextuple_affine`
(`257/20000 ≤ E₆(g) + B₆·(g₀+…+g₄)` for all nonnegative gaps, `B₆ = 1094977/5000000000`).
Nothing here is proof authority: the proof is the Lean code under `Zeta23/ThmD/Sextuple/A1285/` (plus the
shared `A1275/Catalog`, `A1275/RefinementData`, `Macro/` and `AffineTree.lean` layers) and the axioms it
depends on.

## What it is

The same sextuple argument as the baseline (`A₆ = 1/80`) and the `A1275` target (`A = 51/4000`), with the
affine coefficient pushed to `A = 0.01285` over the unchanged 272-model catalog (56 stable pieces + the
216 Lean-checked refinement cells of `A1275/RefinementData.lean`). The exact tree was produced by the
refined *scalar-cache* branch-and-bound (`certificates/sextuple/a1275/generators/generate_exact_refined_scalar_tree.py`),
whose scalar seam certificates may reference any of the 272 models:

| quantity | value |
|---|---|
| `A`, `B`, cutoff `A/B` | `257/20000`, `1094977/5000000000`, `64250000/1094977` |
| topology tokens / leaves | 1,771,973 / 885,987 (884,314 quadratic, 1,673 affine tails) |
| maximum depth / fuel | 73 / 74 |
| scalar certificates / segments | 3,365 / 17,697 (13,675 segments on refinement pieces) |
| smallest quadratic / tail margin | `3.4×10⁻¹¹` / `7.07×10⁻⁵` (exact values in `macro-scalar-tree/manifest.json`) |
| chunks (≤ 100 tokens) / assembly nodes / parts | 30,153 / 30,152 / 302 |
| word data | 3,461 leaf-block words in 139 `WordData` groups; 88,599 topology words in 633 blocks of 140 |
| exact comparator | `(6·HD(1) − 10π·B₆)/(6 − 257/20000) > 201406213933795020896911983481/299357500000000000000000000000 > 6727949489/10^10`, margin `18463270896911983481/299357500000000000000000000000` |

## Layout

| path | content |
|---|---|
| `macro-scalar-tree/` | canonical exact streams (`topology-u64le.bin`, `terminal-kinds-u8.bin`, `anchors-u16le.bin`, `term-codes-u16le.bin`), the 3,365 scalar certificates, `manifest.json` (stream SHA-256, counts, margins), generator log, and the independent exact replay (`exact-replay-report.json`, `verifier.stdout.log`: status PASS, full exhaustion) |
| `generation-report.json` | report of `certificates/sextuple/tools/gen_sextuple_target_lean.py` for namespace `A1285` (counts, exact bound, public decimal, generator SHA-256) |
| `frontier/` | the neighbouring frontier points: `A = 0.0128 = 8/625` closed (772k tokens, verifier PASS; manifest and replay report kept, streams not committed) and `A = 0.0129 = 129/10000` did **not** close within a 6,000,000-node cap (≈ 40 boxes still pending at depth 91 with no obstruction; generator log kept) |
| `SHA256SUMS` | SHA-256 of every file here and of the non-generated `A1285` Lean sources, plus concatenated digests of the chunk, part and word-data sources |

Generators and verifiers are shared with the `A1275` target: `certificates/sextuple/a1275/generators/`
(exact branch-and-bound and its independent verifier), `certificates/sextuple/tools/gen_sextuple_target_lean.py`
(all Lean modules of a target from its tree directory; validated by regenerating the committed `A1275`
artifacts byte-for-byte), `certificates/sextuple/a1275/tools/build_a1275_chunks.py --ns A1285`
(batched, memory-shaped Lake driver), `certificates/sextuple/a1275/tools/verify_a1275_packed_words.py`
(stream decoder; parameterise the paths for `A1285`).

## Design notes specific to this target

* Scalar check lemmas are `decide +kernel` (the `norm_num` route of the A1275 module overflows the
  recursion depth on refinement-piece segments).
* `improvedScalarTable` is a two-level `match` on `(i / 64, i % 64)`: a flat Nat-literal `match`
  compiles to a linear `casesOn` chain, so lookups cost O(index) kernel steps (measured ≈ 54 ms at
  index 3300, fifteen lookups per leaf: 99-token chunks went from 20 s early in the tree to 86 s / 24 GB
  late); with the nested table the same chunks take 18–24 s at ≤ 12 GB and the scalar module itself
  elaborates in 455 s instead of 1,701 s.
* `TreeWords` / `WordData` carry `maxHeartbeats 0` (the 633-block topology literal exceeds the default
  elaboration budget) and `Layout` is `noncomputable` (the literal is not code-generable at this size).

## Reproduction (from the repository root)

```bash
PY=python3
$PY certificates/sextuple/a1275/generators/verify_exact_refined_scalar_tree.py \
    --data certificates/sextuple/macro-data-exact.json \
    --refinements certificates/sextuple/a1275/refinement-catalog/refinement-catalog-exact.json \
    --tree-dir certificates/sextuple/a1285/macro-scalar-tree --report /path/to/report.json
$PY certificates/sextuple/tools/gen_sextuple_target_lean.py \
    --tree-dir certificates/sextuple/a1285/macro-scalar-tree --ns A1285 --repo /path/to/scratch
LEAN_NUM_THREADS=6 lake build +Zeta23.ThmD.Sextuple.A1285.FlatEquivalence +Zeta23.ThmD.Sextuple.A1285.Assembly
python3 certificates/sextuple/a1275/tools/build_a1275_chunks.py --ns A1285 --max-workers 9 --mem-base 11
LEAN_NUM_THREADS=4 lake build +Zeta23.ThmD.Sextuple.A1285.LineDecimal
lake env lean Zeta23/ThmD/Sextuple/A1285/AxiomAudit.lean
```
