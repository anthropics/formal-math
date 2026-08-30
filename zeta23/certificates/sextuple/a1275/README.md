# `A = 51/4000` sextuple certificate: provenance, generators, audits, logs

Supporting material for the refined unconditional sextuple improvement
`Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple` (`0.67278371…`, public fixed constant
`6727837118/10^10`) and its kernel-checked five-dimensional certificate
`Zeta23.ThmD.Sextuple.A1275.Certificate.sextuple_affine`
(`51/4000 ≤ E₆(g) + B₆·(g₀+…+g₄)` for all nonnegative gaps, `B₆ = 1094977/5000000000`).
Nothing here is proof authority: the proof is the Lean code under `Zeta23/ThmD/Sextuple/A1275/`
(plus the shared `Macro/` and `AffineTree.lean` layers) and the axioms it depends on. These
files let a reader regenerate the data modules and re-run every external consistency check.

## What changed relative to the baseline `A₆ = 1/80` certificate

* The one-dimensional kernel envelope is the unchanged audited 56-piece stable table
  (`Macro/EnvelopeData.lean`, now exposed as a bounded table by `Macro/StableCatalog.lean`)
  **plus** a separately Lean-checked 216-piece refinement catalog (`A1275/RefinementData.lean`,
  `A1275/Catalog.lean`: 272 selectable models) that subdivides stable pieces 3, 9, 17, 23, 24,
  27, 29, 35, 42 into 24 cells of width 1/64 each.
* 1,383 exact scalar seam certificates with 2,979 segments (`A1275/ScalarData.lean`,
  proof-bearing `Fin` constructors only).
* A 385,967-node dyadic tree with 192,984 leaves (191,474 quadratic, 1,510 affine tails,
  depth ≤ 89, fuel 90), split into 8,953 subtree chunks of ≤ 100 topology tokens
  (`A1275/Chunks/`), assembled by 8,952 applications of the generic split lemma
  `replayAffineTree_split_step` in 90 modules (`A1275/Assembly/`) and `A1275/TreeAssembly.lean`
  (`improvedRootReplay`).
* The generic checker layer is reused unchanged: `Macro/ParametricAdapter.lean` promotes the
  audited leaf checker and its soundness theorem to arbitrary exact `A`, `B`, cutoff, table
  size and scalar count; `AffineTree.lean` (`checkAffineTree_sound`) is stated for arbitrary
  streams.

## Layout

| path | content |
|---|---|
| `macro-scalar-tree/` | the canonical serialized tree (exact-rational branch-and-bound output): `topology-u64le.bin` (20 three-bit tokens per word), `terminal-kinds-u8.bin`, `anchors-u16le.bin`, `term-codes-u16le.bin`, the 1,383 scalar certificates, `manifest.json` (SHA-256 of every stream, counts, minimum margins), the generator log and the independent exact replay report |
| `refinement-catalog/` | the 216-cell refinement catalog (`refinement-catalog-exact.json`), its exact structural replay, the Lean build report and audit of `refinementCatalog.all MacroPiece.check = true` |
| `tree-artifacts/` | the bounded replay plan (8,953 chunks / 8,952 assembly nodes), tree-artifact generation and independent verification reports, hostile-generator matrix, word-data build report, the two-level word generation report and the packed-words decode verification |
| `generators/` | the exact-rational generators and independent verifiers: refinement catalog (`generate_refinement_catalog.py`, `verify_refinement_catalog.py`), refined 5D tree (`generate_exact_refined_tree.py`, `verify_exact_refined_tree.py`), Lean scalar data (`generate_improved_scalar_lean.py`), tree artifacts / word data (`generate_improved_tree_artifacts.py`), chunk + assembly sources (`generate_a1275_full_sources.py`, `publish_a1275_full_sources.py`, hostile test) |
| `tools/gen_a1275_blocked_words.py` | regenerates `A1275/TreeWords.lean` from `macro-scalar-tree/` in the two-level layout (140 topology words per block; the 31 `WordData` groups of 25 leaf-block words), cross-checked against the frozen single-level literal |
| `tools/verify_a1275_packed_words.py` | independent decoder: reconstructs the four byte streams from the Lean literals of `TreeWords.lean` + `WordData/` and compares SHA-256 with `manifest.json` |
| `tools/build_a1275_chunks.py` | batched, memory-shaped Lake driver for the 8,953 chunk modules (restart-safe; Lake decides what is up to date) |
| `tools/fix_a1275_assembly_statements.py` | regenerates the 90 `A1275/Assembly/PartNNN.lean` node lemmas with explicit statements from the bounded plan (node paths derived from the root and cross-checked against every chunk source); the frozen publication's parts had no statements and had never been compiled |
| `SHA256SUMS` | SHA-256 of every file in this directory and of every non-generated `A1275` Lean source, plus concatenated digests of the 8,953 chunk and 90 part sources |
| `manifests/` | the frozen-source manifests: foundation freeze (44 sources), full-source freeze and publish manifest (9,044 generated sources, normal/`-O` byte-identical, hostile matrix) |
| `audits/tree/` | independent audits of the data/plan, foundation, source freeze, resolved import closure, source delta, Lean sample/hostile gate, and the architecture/patch acceptance notes |
| `audits/scalar/` | independent exact-rational re-verification of all 1,383 scalar certificates / 2,979 segments and the Lean scalar module |
| `audits/assembly/` | independent audit of the conditional assembly `A1275/Assembly.lean` |
| `audits/integration-plan/` | the integration plan, module graph, comparator arithmetic and planned path manifest |
| `external-certificate-report.md`, `feedback-bounds.json`, `frontier-summary.json` | the external exact-rational certificate report, the directed comparator bounds (`HD(1) > 672500703679/10^12`, `π < 314159265358979323847/10^20`) and the frontier summary |

## Exact comparator

```text
sextupleLowerConstant = (6·HD(1) − 10π·B₆)/(6 − 51/4000)
                      = (3000000000·HD(1) − 1094977·π)/2993625000
                      > 201406213933795020896911983481/299362500000000000000000000000
                      > 6727837118/10^10   (margin 10067520896911983481/299362500000000000000000000000)
```

(`ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118`, from `HD_one_decimal.1` and
`Real.pi_lt_d20` only.)

## Deviations from the frozen generated sources

The 8,953 chunk sources and the 31 `WordData` modules are byte-identical to the frozen publication
(`manifests/FULL-SOURCE-PUBLISH-MANIFEST.json`, `manifests/FOUNDATION-FREEZE-MANIFEST.json`). Three
foundation modules were replaced by the two-level layout (`TreeWords.lean` regenerated by
`tools/gen_a1275_blocked_words.py`, `TreeReader.lean` with the two-level readers added, `Layout.lean`
stated on the concatenations) and the 90 assembly parts were regenerated with explicit node statements
and without an explicit `(box := …)` argument (passing the box explicitly makes Lean's unifier blow up
exponentially in the path depth: depth 29 ≈ 1 s, depth 33 > 150 s; inferred from the statement, a
100-node part builds in 4–10 s at any depth up to 73). `FlatEquivalence.lean`, `Certificate.lean`,
`Unconditional.lean`, `LineDecimal.lean`, `AxiomAudit.lean` and the comparator topic are new.

## Build record (2026-08-27, 18-core / 128 GiB host)

| phase | result |
|---|---|
| foundations (`…A1275.ChunkCalibration` and dependencies) | success; `A1275.ScalarData` 227 s, `A1275.RefinementData` 182 s, `Macro.ScalarData` 152 s, calibration chunk 13 s |
| 8,953 chunks (`tools/build_a1275_chunks.py`, 45 batches × 200, 10 builders) | 8,953/8,953, 0 failures, 10,552 s wall (2.93 h), 98,753 s CPU, longest chunk 50 s |
| 90 assembly parts → `TreeAssembly` → `Certificate` → `Unconditional` → `LineDecimal` | ≈ 662 s for the parts (≤ 9.6 s each), then 3.3 / 3.3 / 3.5 / 3.3 s; 17,962 jobs |
| baseline chain rebuilt on the refactored foundation | 2,969 chunks, 30 parts, endpoints; 11,881 jobs |
| root `lake build` | 21,145 jobs, success |
| `Challenge.SextupleA1275`, `Solution.SextupleA1275`, `PrintAxioms/SextupleA1275` | success; 11/11 declarations on `[propext, Classical.choice, Quot.sound]` |
| `A1275/AxiomAudit.lean` (29 declarations) | 27 on the three standard axioms, the two layout lemmas on `[propext, Quot.sound]` |

Logs: `../logs/a1275-*.log`, `../logs/lake_comparator_sextuple_a1275.log`, `../logs/printaxioms_sextuple_a1275.log`,
`../logs/audit-report.txt`.

## Two-level word layout (why the chunks are cheap)

A kernel lookup `a[i]?` in an `Array` literal walks `i` list cells and Lean's kernel does not
share that walk across the reads of one `decide +kernel` term. With the 19,299 topology words in
one flat array, a 99-token chunk near the end of the stream cost ≈ 90–165 s and ≈ 39 GB (the
frozen single-level layout, measured); with 140-word blocks and the 31 leaf groups the same
chunk costs ≈ 10 s and ≈ 7 GB. `Layout.lean` proves the audited flat layout predicates for the
concatenated arrays and `verify_a1275_packed_words.py` decodes the literals back to the canonical
streams.

## Regeneration / re-verification (Python 3, standard library only; from the repository root)

```bash
PY=python3
$PY certificates/sextuple/a1275/generators/verify_exact_refined_tree.py --help      # exact serialized-only replay of the 5D tree
$PY certificates/sextuple/a1275/tools/gen_a1275_blocked_words.py \
    --tree-dir certificates/sextuple/a1275/macro-scalar-tree \
    --out /path/to/TreeWords.lean                                                     # byte-identical to the committed module
$PY certificates/sextuple/a1275/tools/verify_a1275_packed_words.py                   # decodes the Lean literals, compares stream SHA-256
```

Building the chain (Lake throttled via `LEAN_NUM_THREADS`; each `lean` process loads ~6 GB of
oleans, a chunk needs ~2–8 GB of kernel working memory; `A1275/ScalarData` alone needs ~20 GB):

```bash
LEAN_NUM_THREADS=4 lake build +Zeta23.ThmD.Sextuple.A1275.ChunkCalibration      # foundations + one 99-token calibration chunk
python3 certificates/sextuple/a1275/tools/build_a1275_chunks.py --max-workers 10 # the 8,953 chunks, memory-shaped batches
LEAN_NUM_THREADS=4 lake build +Zeta23.ThmD.Sextuple.A1275.LineDecimal           # assembly parts, root replay, certificate, endpoints
lake env lean Zeta23/ThmD/Sextuple/A1275/AxiomAudit.lean                         # #print axioms over the whole chain
```
