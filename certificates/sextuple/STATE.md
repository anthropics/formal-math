# Lean25 concrete certificate state

Updated: 2026-08-22 (session resumed from `post-anthropic-rh-project-handoff.md` on explicit user instruction; manifest security probing remains PAUSED and was not touched).

## Summary

The sole Lean blocker of the handoff — a kernel-checked
`Certificate.sextuple_affine : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) → A6 ≤ sextupleEnergy g + B6 * sextupleSpan g`
— is CLOSED (see RESULTS below) by replaying the audited serialized dyadic-16384 tree
(99,507 topology tokens, 49,754 leaves, 48,260 quadratic leaves, 871 scalar certificates)
with the Lean kernel, through the independently audited generic layer
`Zeta23.ThmD.Sextuple.AffineTree` (`checkAffineCertificate_sound`, `affineTree_A6_global_of_root`).

Design: the tree is partitioned into subtree chunks; each chunk is one Lean module whose
single theorem `replayAffineTree concreteLeafCheck topologyStream payloadStream fuel t p (pathBox rootBox path) = some (t', p')`
is proved by `decide +kernel`; generated assembly modules prove every internal node by applying the
once-proved generic lemma `replayAffineTree_split_step` to its two children, up to `rootReplay`;
`Certificate.lean` turns `rootReplay` plus exact stream lengths into `checkAffineTree … = true`
and applies the audited soundness theorems.

## Step 4 of the resume order: full `MacroScalarData.lean` rebuild (DONE)

Command (from the Lean worktree, prototype dir on `LEAN_PATH`):
`/usr/bin/time -lp lake env lean -R <proto> -o <proto>/bench/MacroScalarData.rebuild.olean <proto>/MacroScalarData.lean`

- wall 108.22 s, user 1055.04 s (parallel elaboration), max RSS 12,924,289,024 bytes
- `#print axioms`: `stableMacroTable_check`, `scalarCertTable_check` → `[propext, Classical.choice, Quot.sound]`
- rebuilt olean SHA-256 `def0a84f988f03d11291daa783c07df9b5b2ee9b5559fefc968847fd9b6d2867` — **byte-identical** to the previously unverified `MacroScalarData.olean`
- durable log: `checkers/lean-sextuple-certificate-prototype/MacroScalarData.rebuild.build.log`
  SHA `18d4349caf1e037cb9aa5f4cddc10a9a1465590f4a4c441f958526015784194d`

## Step 5: deterministic regeneration (DONE, byte-for-byte)

`checkers/lean-sextuple-certificate-prototype/bench/regen/regenerate_macro_lean_data.py --check`
regenerates, from `macro-data-exact.json` and `macro-scalar-tree/scalar-certificates.json`:

| file | SHA-256 | status |
|---|---|---|
| `MacroEnvelopeData.lean` | `632d72144a0a62258b68e94a9da93b889a6b67c8f242e6fce1eaaa8ce26690b5` | PASS |
| `MacroScalarData.lean` | `532dc8f4a8abd2bebc99d0de968dea271bbcf74ee7d5e012829215e36e42e359` | PASS |
| `MacroScalarDataPrefix.lean` | `9c22df713526d13512c988fd64e9dbafa630f42615bf08eea3e91da7b1492604` | PASS |

Derivation rules are in `bench/regen/README.md`. The stream serializer
(`serialize_macro_scalar_cache_tree.py`) and raw-byte verifier (`verify_macro_scalar_tree.py`)
were already persisted. The packed Lean data module is cross-checked against the canonical
streams by `bench/verify_packed_words.py` (decodes the Lean literals back to the four byte
streams and compares SHA-256 with `macro-scalar-tree/manifest.json`): **PASS** for
`Zeta23/ThmD/Sextuple/Macro/TreeWords.lean` (SHA `8af2f1794f39dfbf36ec676da19c949979a3c93f24a038d0c8aa3c10fb508bd2`).

## Correction to the prototype adapter

`MacroScalarAdapter.lean`'s `macroScalarTermsFit` is defined by `by classical; exact decide …`.
The `classical` tactic can select `Classical.propDecidable`, which the kernel cannot evaluate;
the prototype `macroScalarDyadic14LeafCheck` therefore could never have been closed by
`decide`. `Macro/LeafCheck.lean` adds an explicit Boolean fit check (`termRefFits`,
`leafTermsFit`, `fastLeafCheck`) and proves `fastLeafCheck = true → macroScalarDyadic14LeafCheck = true`
(`macroScalarDyadic14LeafCheck_of_fastLeafCheck`, via an instance-agnostic `decideEqTrueOf`),
so the audited soundness proof `macroScalarDyadic14LeafCheck_sound` is reused unchanged.
The immutable analytic inputs (`MacroAnalytic.lean`, `MacroEnvelopeData.lean`, report JSON)
are untouched; hashes re-verified at session start.

## Worktree module layout (all new, untracked)

| module | source | note |
|---|---|---|
| `Zeta23.ThmD.Sextuple.Macro.Analytic` | byte-identical copy of `MacroAnalytic.lean` (`c0757a93…`) | |
| `Zeta23.ThmD.Sextuple.Macro.EnvelopeData` | `MacroEnvelopeData.lean`, only the import line changed | |
| `Zeta23.ThmD.Sextuple.Macro.AffineAdapter` | `MacroAffineAdapter.lean`, import line changed | |
| `Zeta23.ThmD.Sextuple.Macro.ScalarAdapter` | `MacroScalarAdapter.lean`, import line changed | |
| `Zeta23.ThmD.Sextuple.Macro.ScalarData` | `MacroScalarData.lean`, only the two import lines changed | |
| `Zeta23.ThmD.Sextuple.Macro.LeafCheck` | new | kernel-reducible leaf check |
| `Zeta23.ThmD.Sextuple.Macro.TreeReader` | new | packed readers, layout checks, `concreteLeafCheck`, `pathBox` |
| `Zeta23.ThmD.Sextuple.Macro.TreeWords` | generated | 4,976 topology words + 195 leaf blocks (321-bit leaf words, 256 per block) |
| `Zeta23.ThmD.Sextuple.Macro.Chunks.ChunkNNNN` | generated | one `decide +kernel` subtree replay each |
| `Zeta23.ThmD.Sextuple.Macro.AssemblyStep` | new | generic `replayAffineTree_split_step` |
| `Zeta23.ThmD.Sextuple.Macro.Assembly.PartNNN` | generated | 30 chained modules of internal-node lemmas |
| `Zeta23.ThmD.Sextuple.Macro.TreeAssembly` | generated | `rootReplay` |
| `Zeta23.ThmD.Sextuple.Macro.Layout` | new | linear Boolean layout checks + soundness |
| `Zeta23.ThmD.Sextuple.Certificate` | new | layout checks, `treeCheck`, `sextuple_affine` |
| `Zeta23.ThmD.Sextuple.Unconditional`, `LineDecimal` | from `lean24b-final-wrapper-plan.md` | |
| `Zeta23.ThmD.Sextuple.AxiomAudit` | audit only, not imported by the root | |

Generator: `checkers/lean-sextuple-certificate-prototype/bench/gen_packed.py`
(`data`, `chunks --max-tokens N`, `assembly --max-tokens N`, `stats`).

Leaf word layout: bit 0 kind (0 tail / 1 quadratic); bits 1..80 five 16-bit anchor codes
(denominator 16384); bits 81..320 fifteen 16-bit term codes (0..55 piece, 32768+n scalar n,
65535 zero); tail words are exactly 0. Out-of-range codes decode to `none` (replay fails).

## Kernel cost measurements (single `lean` process, `decide +kernel`)

| chunk tokens | leaves | user s | max RSS (incl. ~6 GB olean) | s/leaf |
|---|---|---|---|---|
| 97 | ~49 | 8.7 | 7.5 GB | ~0.10 |
| 195 | ~98 | 15.8 | 9.4 GB | ~0.12 |
| 391 | ~196 | 57.2 | 20.1 GB | ~0.27 |
| 399 | ~200 | 78.2 | 27.9 GB | ~0.37 |

Memory and time grow superlinearly with chunk size (kernel whnf caches live for one
declaration), so chunks of ≤100 tokens (2,969 modules) are used. Each `lean` process carries
~6 GB of privately loaded oleans; Lake 5.0 (Lean 4.33.0-rc2) has no `-j` flag, and an 18-wide
build swap-thrashed the 128 GB machine. `LEAN_NUM_THREADS=N` caps Lake at exactly `N`
concurrent builders (verified by sampling); the production build uses `N = 10`.

## Build / audit commands

```bash
cd _exp_rh89_zeta23_lean
LEAN_NUM_THREADS=10 lake build Zeta23.ThmD.Sextuple.LineDecimal   # log: <proto>/bench/lake_main_build.log
lake env lean Zeta23/ThmD/Sextuple/AxiomAudit.lean                # #print axioms for all public theorems
<proto>/bench/forbidden_scan.sh                                    # sorry/admit/axiom/unsafe/native_decide/ofReduceBool/…
```

## Status of the remaining handoff obligations

1. standalone deterministic generator — DONE (byte-for-byte, see above)
2. independent audit of `MacroScalarAdapter` and the 871 checks — owner rerun DONE (byte-identical olean); independent audit still open
3. packed readers in Lean — DONE (`Macro/TreeReader.lean`)
4. exact sizes / ranges / bounded indices / cursors / fuel / padding — DONE in `TreeReader`/`Certificate` (`packedTopologyLayoutCheck`, `packedLeafLayoutCheck`, exact exhaustion via `checkAffineTree`)
5. model covers its pair-distance interval — `leafTermsFit` (proved to imply the audited fit)
6. orientation / 15 pairwise lifts with cross terms — reused audited `macroScalarDyadic14LeafCheck_sound`
7. root check reduced to `true` — DONE (`treeCheck`)
8. `Certificate.sextuple_affine` — DONE
9. ledger instantiation — DONE (`Unconditional.lean`)
10. decimal wrapper, root imports, full build, axiom scans — DONE (see RESULTS)

## RESULTS (2026-08-22 22:10 UTC) — `Certificate.sextuple_affine` is kernel-checked

- Final chunking: 2,969 chunk modules of ≤100 topology tokens; all built by `lake` 10-wide
  (`LEAN_NUM_THREADS=10`), 0 errors, ~60 chunks/min, ~50 min wall for the chunk phase.
  (The chunk-phase stdout log was overwritten by the relaunch that built the assembly; the
  durable evidence is the 2,969 `.olean`/`.trace` artifacts under
  `.lake/build/lib/lean/Zeta23/ThmD/Sextuple/Macro/Chunks/` plus the final up-to-date `lake build`.)
- Assembly: the first design (per-node `rw [replayAffineTree, htok]; simp only [hl, hr]`) made the
  kernel re-evaluate subtree replays (4–136 s per node, 72 GB) and was abandoned. Final design:
  one generic lemma `replayAffineTree_split_step` (`Macro/AssemblyStep.lean`, proved once) applied
  at every internal node; 2,968 node lemmas in 30 chained modules `Macro/Assembly/PartNNN.lean`
  (~12–26 s each), `TreeAssembly.lean` (`rootReplay`) 3.3 s, `Certificate.lean` 22 s.
- Final build log: `bench/lake_final_build.log` (SHA `8a46b8b3e0db67f5e54156998d5f3b9f066f42d726e3533c66589352c5adbe4c`), exit 0.
- Root: `Zeta23.lean` now imports `Zeta23.ThmD.Sextuple.LineDecimal`; default `lake build` = 12,057 jobs, success.
- Axiom audit (`bench/audit-report.txt`, SHA `02785b5527db03ed85fff33e11682403b1eef8a8803aa7bc9200a414e03c79a2`):
  all 18 listed theorems use exactly `[propext, Classical.choice, Quot.sound]`
  (`topologyLayout`/`leafLayout` use only `[propext]`). Forbidden scan: clean over 3,013 files.
- Independent static audit: `audits/lean25-concrete-certificate-static-audit.md`
  (SHA `0d07c64ec53527d18938678913097fdd96759e123e02d973584c3cd9a3e42a98`), verdict PASS-WITH-NOTES;
  its only blocking note (build/axiom scan outstanding) is now discharged above.
- Public theorems now unconditional in Lean:
  `Zeta23.ThmD.Sextuple.Certificate.sextuple_affine`,
  `Zeta23.ThmD.Sextuple.zetaSextupleLedgerInterface`, `thmD₀_sextuple`, `thmD₀_sextuple_cumulative`,
  `thmD₀_sextuple_6727556`, `thmD₀_sextuple_cumulative_6727556`,
  `thmD₀_sextuple_672755620655`, `thmD₀_sextuple_cumulative_672755620655`.
- Final source hashes: `Certificate.lean` `740cae7354fd36d52921ea40136dd15e41992db96c9f947f3e729b3cc90089ed`,
  `Macro/AssemblyStep.lean` `b714f09932210bb1374e550f3ce747316e477afc19a7fcc476580cefe239aa35`,
  `Macro/TreeAssembly.lean` `70c20df3fdb2da92a0f034ae51b77d09287003c4f318de6ff9e7d5c151aefb08`,
  `Macro/Layout.lean` `a81a80f869716c2ef47580d97eb352b1ed7bb386692a772b00d4ee90d58893b9`,
  chunks concatenated `20bd57f81e81f5edc8b5ab715456da7390097b2fba0be318a6f60e89ebcc1a32`;
  generator `bench/gen_packed.py` `f26271aba88c4cceefc7f4fe66a332dec05ddce38b73a1df30c953f9a315c24e`.
- Still open (non-blocking): independent audit of `ScalarAdapter`/`LeafCheck` beyond the static pass;
  dead duplicated `packedLeafLayoutCheck` in `TreeReader.lean` (cosmetic; left to avoid a 50-min rebuild);
  manifest-security work remains PAUSED pending separate user authorization.

## COMPLETION PASS (2026-08-22 23:45 UTC)

- Dead `packedLeafLayoutCheck` removed from `Macro/TreeReader.lean`; `LineDecimal.lean` linter warnings fixed.
- Clean from-scratch rebuild of the whole chain (TreeReader → TreeWords → 2,969 chunks → 30 assembly parts →
  TreeAssembly → Certificate → Unconditional → LineDecimal), `LEAN_NUM_THREADS=10`:
  exit 0, **4,397.21 s wall, 27,934.53 s CPU, 16.5 GB max RSS** (Lake process tree); durable log
  `bench/lake_clean_rebuild.log`. Chunk phase ≈ 60 min at ~50 chunks/min.
- Independent scalar-adapter audit: `audits/lean25-scalar-adapter-audit.md`, PASS-WITH-NOTES; exact-rational replay
  of the Lean definitions on all 56 pieces / 871 certificates / 1,932 segments: 0 failures
  (`bench/audit2/verify_scalar_adapter.py`).
- Comparator topic `Sextuple` added (`comparator/Challenge/Sextuple.lean`, `Solution/Sextuple.lean`,
  `config-sextuple.json`, `PrintAxioms/Sextuple.lean`): `lake build Challenge.Sextuple Solution.Sextuple` success;
  `PrintAxioms/Sextuple.lean` → all 14 declarations on `[propext, Classical.choice, Quot.sound]`
  (log `bench/printaxioms_sextuple.log`).
- Post-rebuild audit (`bench/audit-report.txt`): 18/18 theorems standard axioms; forbidden scan clean (3,013 files);
  `sorry` census: 0 under `Zeta23/`, 0 in `Solution`, 45 deliberate challenge `sorry`s; no `axiom` declarations.
- Default `lake build`: 12,057 jobs, success.
- `README.md`, `comparator/README.md`, `AUDIT.md` amended; research ledger `post-anthropic-rh.md` §5 records the result.
- Not done (requires tools not on this machine): a Comparator/nanoda run of `config-sextuple.json`.

## A = 51/4000 REFINED CERTIFICATE (2026-08-27)

- `Zeta23/ThmD/Sextuple/A1275/`: `Certificate.sextuple_affine` at `A = 51/4000`, `B = B₆`, kernel-checked;
  `A1275.thmD₀_sextuple(_cumulative)` and the fixed `thmD₀_sextuple(_cumulative)_6727837118` endpoints
  (`0.6727837118`, exact endpoint `0.67278371…`), all on `[propext, Classical.choice, Quot.sound]`.
- Design numbers: 272-model catalog (56 stable + 216 refinement cells), 1,383 scalar certificates / 2,979 segments,
  385,967-node tree, 192,984 leaves, depth ≤ 89, fuel 90; 8,953 chunks (≤ 100 tokens) in `A1275/Chunks/`,
  8,952 split-step nodes in 90 parts, root `improvedNode8951`.
- Words stored two levels deep (140 topology words per block; 31 leaf groups of 25 block words): with the frozen
  flat 19,299-word array a 99-token chunk near the end of the stream cost 90–165 s and ≈ 39 GB (kernel array
  lookups are linear in the index and not shared across reads), and the 31-way `Array.append` leaf chain added
  ≈ 9 s to every chunk; two-level literals give ≈ 10 s / 7 GB for the same chunk. `FlatEquivalence.lean` proves the
  two-level streams equal the audited flat packed streams.
- Assembly parts: never pass `(box := improvedPathBox improvedRootBox [...])` (or an explicit path list) to
  `replayAffineTree_split_step` — the elaborator's unification then blows up exponentially in the path depth
  (depth 29 ≈ 1 s, depth 33 > 150 s); with the box inferred from the theorem statement a 100-node part builds in
  4–10 s even at depth 73.
- Build record: chunks 10,552 s wall / 98,753 s CPU at ten builders (max chunk 50 s); 90 parts ≈ 662 s; root
  replay, certificate, endpoints ≈ 3.5 s each; baseline chain rebuilt (11,881 jobs); default `lake build` 21,145
  jobs; comparator topic `SextupleA1275` built, 11/11 print-axioms standard; audit report
  `logs/audit-report.txt`; forbidden scan clean over 12,105 files.
- Provenance, generators, verifiers, manifests and independent audits: `certificates/sextuple/a1275/`.

## A = 257/20000 REFINED CERTIFICATE (2026-08-28)

- `Zeta23/ThmD/Sextuple/A1285/`: `Certificate.sextuple_affine` at `A = 257/20000`, `B = B₆`, kernel-checked;
  `A1285.thmD₀_sextuple(_cumulative)` and the fixed `thmD₀_sextuple(_cumulative)_6727949489` endpoints
  (`0.6727949489`, exact endpoint `0.67279494…`), all on `[propext, Classical.choice, Quot.sound]`.
- Design numbers: 272-model catalog (shared with A1275), 3,365 scalar certificates / 17,697 segments, 1,771,973-node
  tree, 885,987 leaves, depth ≤ 73, fuel 74; 30,153 chunks (≤ 100 tokens), 30,152 split-step nodes in 302 parts.
- All modules generated by `tools/gen_sextuple_target_lean.py` (validated against the committed A1275 artifacts).
  New kernel-cost lesson: a flat Nat-literal `match` table is O(index) per lookup (54 ms at index 3300; 15 lookups
  per leaf) — `improvedScalarTable` is a two-level match on `(i / 64, i % 64)`, which also cut the scalar module's
  elaboration from 1,701 s to 455 s. Scalar check lemmas are `decide +kernel` (`norm_num` overflows the recursion
  depth on refinement-piece segments); big word modules need `maxHeartbeats 0`; `Layout` is `noncomputable`.
- Build record: chunks 48,654 s wall / 420,042 s CPU at nine builders (max chunk 27 s); 302 parts ≈ 3,334 s;
  root replay 4.5 s, certificate 30 s, endpoints ≤ 30 s; default `lake build` 51,748 jobs; comparator topic
  `SextupleA1285` 11/11 standard axioms; forbidden scan clean over 42,712 files.
- Frontier: `A = 0.0128` closes (not integrated); `A = 0.0129` does not close within 6,000,000 nodes (32 boxes
  pending, no obstruction). Provenance under `certificates/sextuple/a1285/`.
