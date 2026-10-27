# Exact post-replay integration plan: `A = 51/4000`

## 0. Status and authority

- Frozen repository: `/Users/mdumitrean/Desktop/dev/aigent/math/prime/_exp_rh89_zeta23_lean`
- Frozen HEAD: `5e9617d84ece3aeecdf983a8e7e9bfa50f413e5a`
- Repository status during this audit: clean.
- Selected closure design: TreeFormat architecture gate v2, SHA-256 `29df7d74599ed437b685a3bc476f3dd53eb6648ddfc3b0273827b70198334a93`.
- Immutable fallback gate v1 remains SHA-256 `18e023b1ceafd677cfa2e9dc849f68181572bf24eb947b17c5ae8cc14a3d858f`.
- This directory contains plans and explicit-hypothesis probes only. It does **not** contain the owner 8,953-chunk replay, `rootReplay`, the concrete certificate, or an unconditional theorem claim.
- No repository or frozen owner/audit input was edited. No file was written to `/tmp`.

Current evidence is `PASS_PRE_REPLAY`; integration remains blocked on the owner full Lean replay and the independent tree audit's final PASS.

## 1. Gate summary

| Gate | Current result | Integration consequence |
|---|---|---|
| Improved scalar source | PASS: 1,383 certificates, 2,979 segments, 2,979 explicit `Fin` constructors; source SHA `1ae4e940ffa5860768c7756ac4b60a0bde643db3140ad14c070f94e3a8a94adc` | May promote after deterministic generator hardening |
| Raw exact tree and bounded plan | PASS data/plan: 385,967 tokens, 192,984 leaves, 8,953 chunks, 8,952 assembly nodes | Does not authorize the concrete theorem |
| Stable catalog extraction | PASS audit-local compile; extracted declaration block SHA `89ce97c74298da79185a0b7067ea08339a8593aaa586484778c9f6b89a040a78` | Do before all improved builds |
| TreeFormat v2 refactor | PASS independent exact-module, API, closure, and resource probes | Preferred over a second parameterized/local Layout implementation |
| Conditional affine certificate template | PASS under explicit `hrootReplay`; axioms are only `propext`, `Classical.choice`, `Quot.sound` | Template only; no root theorem claimed |
| Conditional ledger/final endpoints | PASS under explicit certificate hypothesis; same allowed axioms | `ImprovedAssembly` can land before replay |
| Exact `6727837118/10^10` comparator | PASS with a positive rational margin | Arithmetic is not blocked on replay |
| Baseline bare-`Fin` hardening | PASS independently: 1,932 explicit constructors, normal/`-O` equivalence, hostile rejection, full scalar build | Not in the improved closure; apply as a separate release/regression change |
| Owner full chunks/assembly/root | PENDING | Blocks certificate and public endpoints |
| Independent full tree audit | `PASS_DATA_PLAN_PENDING_FULL_LEAN` | Blocks certificate/public-result commit and documentation claim |

The independent baseline audit is PASS, but it must never be presented as evidence for the improved tree. Conversely, after the closure gates below pass, baseline `Macro.ScalarData` is not a logical dependency of A1275. The audit also found a 40-segment bare-`Fin` prefix artifact outside the closure; harden it before it is ever imported or published.

## 2. Selected minimal import graph

The machine-readable graph is `module-graph.json`. Use the exact qualified module names there.

### 2.1 Shared API-preserving extractions

1. Add `Zeta23.ThmD.Sextuple.Macro.StableCatalog`, importing only `Macro.EnvelopeData`.
   Move `stableMacroTable` and `stableMacroTable_check` unchanged from `Macro.ScalarData`.
   Preserve their fully qualified names, 56-way dispatch, statement, proof, reducibility, and axiom set.
2. Make baseline `Macro.ScalarData` import `Macro.StableCatalog` and delete only those moved declarations before applying the separate explicit-`Fin` regeneration.
3. Add `Zeta23.ThmD.Sextuple.Macro.TreeFormat`, importing `Zeta23.ThmD.Sextuple.AffineTree` and owning exactly:
   ```lean
   def leafWordBits : ℕ := 321
   def leafBlockSize : ℕ := 256
   ```
4. Baseline `Macro.TreeReader` adds the `Macro.TreeFormat` import and deletes only those two local definitions. All decoder, stream, checker, path, and soundness text stays unchanged.
5. Baseline `Macro.Layout` changes only its direct import:
   ```text
   Macro.TreeWords  ->  Macro.TreeFormat
   ```
   Its declarations and proof bodies remain byte-identical.

The exact audit-local before/after hashes and normalized diff are in `v2-treeformat-audit.json` and `v2-source-delta.patch`:

| Source | Before SHA-256 | Accepted v2 after SHA-256 |
|---|---|---|
| `Macro.TreeReader.lean` | `c97d8d9c5614dbd3f19fe34cd23b25dc813e04ca43885f9b20b5b173c388178e` | `83a2d50fc8dce74c30dd74b22e5a7ec07805d7bc6f8aa774928113ccab6269e6` |
| `Macro.Layout.lean` | `a81a80f869716c2ef47580d97eb352b1ed7bb386692a772b00d4ee90d58893b9` | `4146c8be0788f3b5adbade43f322ba34960af93f4775730e1d271cbf7f2efc7c` |
| new `Macro.TreeFormat.lean` | — | `6fccdd766b799e520969a71ee8194c3811f714f90f2e52b751f562968ff526cc` |
| frozen/planned `TreeWords.lean` | `0cfb2ab70bff047ab462e59353f8ab7527ddd36fadbf0e571e34b9f8a43add39` | `ca120e6bcd30931ec47187234942cf2786c08072e11d4b3a9f58585c0ad54e3e` |
| frozen/v2 `Layout.lean` | `c8d6874294bb87cc6309d372f2a3c5f8b08a9dd63df7b849f65045eda340fb2f` | `c8d6874294bb87cc6309d372f2a3c5f8b08a9dd63df7b849f65045eda340fb2f` (unchanged) |

Final repository qualification changes only import-module text. Under the confirmed `Zeta23.ThmD.Sextuple.A1275` paths, the audit-local qualified candidates hash to `1407a17502b086957d5af7d2c1f24fde0897b93c18adb0903dbbbac85c33da27` for TreeWords and `77e3152d78fc4871bb790e9775f7f02e256265975cd84b1cfdb857c6fa3ca911` for Layout; freeze their final hashes again after owner generation and before building chunks. Their bodies after imports must be byte-identical to the frozen sources.

The moved constant block is byte-equal after normalization. Its SHA-256 is `5a3cff17f78a7690f2e25262525de1a6329dbf4af288f2d6fc0ea19c125b1b53`. The exact-module probes rebuilt TreeFormat, baseline TreeReader, and refactored Layout, and reduced the APIs to `321` and `256`. The improved Layout v2 probe rebuilt with axioms `[propext, Quot.sound]`.

The independent baseline/v2 audit accepted these additional exact sources: `StableCatalog.lean` `a1a1c09382864916874d5445763793c24b0431e68ee918ad76f8cb8d2cbcc527`, extracted explicit-Fin `ScalarData.lean` `aa43ed4fc1598611b6537076a8e53a7e36fed05c0aeb935d0f6ccbbe1f50153e`, and import-only `Catalog.lean` `f3d6b6b69df120c390628b3cbccc79b343c68961c13138f9b728ae886ff89a7b`. Its current final report is `AUDIT-REPORT.md` SHA `819f1466155510f3ce54c0e2c224bd56b94e379efe3b1fad43cbcb1a78e40e03`. `VERDICT.json` is `26f1635bb64a52ad9b74615842d10147fcb9644763661f1dd6bbfe1e8c8db91a` and its complete `SHA256SUMS` is `782296e7821d8ac7057f53c10a972bd6a0259b0d6affd20bc4bd837e00f751bb`. The refactored Layout `.olean` used by the resolved audit has SHA `7267932cf8f6b0a163bb5355832719e782c5b3c4c9b6351964c4011d287a405d`.

If any production delta exceeds these import changes and exact declaration moves, reject v2 and return to immutable gate v1. Do not silently weaken either architecture gate.

### 2.2 Improved proof modules

```text
Macro.EnvelopeData -> Macro.StableCatalog ----------------------┐
        |                                                        |
        +-> A1275.RefinementData -> A1275.Catalog               |
                                                                 v
Macro.LeafCheck -> Macro.ParametricAdapter -> A1275.ScalarData
                                                   |
                                                   v
                                           A1275.TreeReader
                                                   |
AffineTree --------------------------------> A1275.TreeWords
A1275.WordData.LeafBlocks000..030 --------->        |
                                                   v
TreeFormat -> lightweight Macro.Layout ----> A1275.Layout
                                                   |
                 A1275.ChunkCalibration (v2 pre-owner gate)
                                                   |
                 A1275.Chunks.Chunk0000..Chunk8952
                                                   |
                 A1275.Assembly.Part000..Part089
                                                   |
                 A1275.TreeAssembly -> A1275.Certificate

Ledger + Final -> A1275.Assembly (conditional)
Base + Certificate + Assembly -> A1275.Unconditional
A1275.Unconditional -> A1275.LineDecimal -> root Zeta23
A1275.LineDecimal -> A1275.AxiomAudit (audit only, not root-imported)
```

`Macro.ParametricAdapter` promotes the audited `macroScalarLeafCheckAt` and its soundness theorem. Do not copy or specialize the proof core unnecessarily.

`Ledger.lean`, `Final.lean`, `Feedback.lean`, and `Base.lean` stay unchanged. `ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate` consumes the explicit certificate hypothesis and reuses the existing parameterized core.

### 2.3 Required closure exclusions

For every improved Catalog/Reader/Words/Layout module, every chunk and assembly module, `TreeAssembly`, and `A1275.Certificate`, recursively exclude:

- `Zeta23.ThmD.Sextuple.Macro.ScalarData`
- `Zeta23.ThmD.Sextuple.Macro.TreeReader`
- `Zeta23.ThmD.Sextuple.Macro.TreeWords`

The refactored `Macro.Layout` is allowed only at the frozen production source and fresh `.olean` hashes. Its closure must be exactly data-independent through `Macro.TreeFormat`/`AffineTree` and deliberate analytic dependencies. A stale pre-refactor `Macro.Layout.olean` is forbidden.

Direct import rules:

- `Catalog` imports `Macro.StableCatalog`, never `Macro.ScalarData`.
- `TreeWords` imports `AffineTree` directly, never baseline `Macro.TreeReader` or `Macro.TreeWords`.
- `Layout` imports qualified `TreeWords` and the refactored `Macro.Layout`; it directly imports no baseline data/reader module.
- `A1275.Assembly` retains the audited `ImprovedAssembly.A1275` theorem namespace, remains conditional, and never imports `A1275.Certificate`.

The preliminary StableCatalog/Catalog source walk contained 16 local files and no baseline `Macro.ScalarData`. Final authority requires the complete qualified closure after fresh production builds.

## 3. Generated source and provenance contract

### 3.1 Frozen numerical invariants

- `A = 51/4000`
- `B = 1094977/5000000000`
- cutoff `= 63750000/1094977`
- table size `272 = 56 + 216`
- scalar certificates `1,383`; scalar segments `2,979`
- fuel `90`; maximum depth `89`
- topology tokens/nodes `385,967`
- leaves/payloads `192,984` (`191,474` quadratic, `1,510` tail)
- chunks `8,953`, each at most `100` topology tokens
- assembly internal nodes `8,952`, grouped in `90` modules
- root DAG reference `node 8951`
- final replay cursor `some (385967, 192984)`

Any change to a numeric array, path, cursor, chunk partition, root DAG, theorem statement, or frozen raw hash reopens the data/plan audit.

The generator writes exactly `A1275/WordData/LeafBlocks000..030.lean`, `TreeWords.lean`, `ChunkCalibration.lean`, `Chunks/Chunk0000..8952.lean`, `Assembly/Part000..089.lean`, and `TreeAssembly.lean`. Definitions stay in `MacroPrototype`: `improved*`, `improvedChunk0000..8952`, `improvedNode0000..8951`, then `improvedRootReplay`. Do not introduce a new definition namespace during path qualification.

### 3.2 Fail-closed `Fin` generation

Every generated bounded value is proof-bearing. Never emit an inferred bare numeral of type `Fin n`.

- Improved scalar segments: exactly `2,979` `pieceIndex : Fin 272` constructors.
- Chunk paths: exactly `397,456` `Fin 5` axis constructors.
- Assembly split nodes: exactly `8,952` additional `Fin 5` axis constructors, one per internal node.
- Total path/assembly `Fin 5` constructors: `406,408`.
- Use `⟨n, by decide⟩` (or an equally fail-closed explicit constructor) in generated Lean.

The renderer must validate each integer in Python before formatting. It must reject negative and one-past values. Specifically test `pieceIndex = -1, 272`, path axis `-1, 5`, and assembly-node axis `-1, 5`. The assembly axis test is mandatory; testing chunk paths alone is insufficient. The Lean hostile fixture `⟨5, by decide⟩ : Fin 5` must fail elaboration and create no `.olean`.

### 3.3 Python admission and determinism

All certificate/data generators and authoritative verifiers must:

1. use explicit `if ...: raise ...`/`require(...)`, never Python `assert` for admission or semantics;
2. validate schemas, exact counts, ranges, cursor continuity, source hashes, and full stream exhaustion before writing proof data;
3. stage outputs under the project-local certificate directory, write with atomic replacement, and publish `status: PASS` last and atomically;
4. remove or invalidate a stale PASS report before a run;
5. leave prior canonical outputs untouched on any failure;
6. produce canonical sorted JSON and deterministic UTF-8/newline output;
7. record repo-relative paths, generator/verifier SHA-256, interpreter/version, all input/output hashes, counts, and mode;
8. generate byte-identical valid outputs in normal Python and `python -O`.

The current packed-tree candidate has SHA `423b71327008ecad9c97583d8d777a484eab751d28f24df23bb5ce6e82069d50`, while the frozen generation report records an older generator SHA. Therefore, do not promote that report as-is. Rerun the accepted hardened generator and issue a fresh report bound to the current script and qualified outputs. The authoritative independent verifier must also be hardened and rerun under normal and optimized Python before its PASS is admitted.

Hostile matrix, in both normal and `-O` modes:

- stale/mismatched manifest or generator hash;
- truncated and extra bytes in every physical stream;
- invalid topology tokens `5`/`6`, nonzero padding, kind byte `2`;
- anchor code `16385`;
- invalid term codes `272` and `34151`;
- scalar negative/one-past piece index, overlapping/gapped/reordered segments;
- chunk cursor gap/overlap/duplicate, more than 100 tokens, fuel/depth underflow;
- chunk path and assembly node axis `-1`/`5`;
- root reference/cursor/count mismatch.

Each invalid case must exit nonzero, emit no Lean output, and emit no PASS report in both modes. Valid normal/optimized outputs must be byte-identical to each other and to the frozen expected hashes after only allowed qualification/import changes.

### 3.4 Committed provenance

Use the exact paths in `git-file-manifest.txt`. Commit canonical refinement/scalar/tree inputs, the bounded plan, fresh normal/`-O` hostile report, independent verification report, Fin audit, exact replay report, generator report, build logs, and sorted `a1275-SHA256SUMS`. Do not commit `.olean`, `.ilean`, staging directories, absolute audit paths, or wall-clock fields that make canonical output nondeterministic.

Maintain `certificates/sextuple/a1275-build-state.json` by atomic replacement. Record the frozen input hashes, selected v2 gate/hash, generator modes, last completed build group, exact blocker, and final source/olean/log hashes. Update it before compaction, long builds, or a blocker change.

## 4. Theorem assembly after replay

### 4.1 Root replay and soundness

The generated root module must expose:

```lean
theorem improvedRootReplay :
  replayAffineTree improvedConcreteLeafCheck improvedTopologyStream
    improvedPayloadStream 90 0 0 improvedRootBox = some (385967, 192984)

theorem improvedTreeCheck :
  checkAffineTree improvedConcreteLeafCheck improvedTopologyStream
    improvedPayloadStream 90 improvedRootBox = true

theorem improvedRootBox_predicate :
  BoxPredicate (affineEnergyGoal improvedA improvedB) improvedRootBox
```

Derive `improvedTreeCheck` by unfolding `checkAffineTree`, rewriting with `improvedRootReplay`, and closing the exact stream-length reduction. Derive the predicate with `checkAffineTree_sound improvedConcreteLeafCheck_sound`. Do not insert an axiom or copy the root statement into a hypothesis in production.

Every chunk path axis and every generated assembly split axis must use a proof-bearing `Fin 5` constructor. Assembly proofs combine already-built child replay theorems; they must not repeat large kernel reductions.

### 4.2 Concrete affine certificate

`Zeta23.ThmD.Sextuple.A1275.Certificate.sextuple_affine` has statement:

```lean
∀ (g : Fin 5 → ℝ), (∀ i, 0 ≤ g i) →
  (51 / 4000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g
```

Instantiate the existing `affineTree_global_at` with `A = 51/4000`, `B = 1094977/5000000000`, and limit `59`; discharge exact rational side conditions with `norm_num`; finish by `simpa [affineEnergyGoal, B6]`. `CertificateFromReplayProbe.lean` compiles this exact proof shape while retaining `hrootReplay` explicitly.

### 4.3 Conditional reusable assembly

Place the audited source unchanged at `Zeta23/ThmD/Sextuple/A1275/Assembly.lean` (module `Zeta23.ThmD.Sextuple.A1275.Assembly`). Keep its existing theorem namespace and APIs:

- `ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate`
- `ImprovedAssembly.A1275.sextupleLowerConstant_exact`
- `ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118`
- both exact-feedback and `...6727837118_of_interfaces` endpoint theorems

The module remains conditional and imports only reused Ledger/Final core, never Certificate.

### 4.4 Certificate, Unconditional, and LineDecimal templates

After accepted `improvedRootReplay`, `A1275.Certificate.sextuple_affine` supplies the sole concrete certificate. Only after independent final tree PASS:

1. `A1275.Unconditional` imports `Base`, `Certificate`, and conditional `Assembly`; it defines `zetaSextupleLedgerInterface`, its exact-constants form, and the exact-feedback dyadic/cumulative epsilon endpoints.
2. `A1275.LineDecimal` imports `Unconditional`; it defines only the fixed `thmD₀_sextuple_6727837118` and cumulative endpoint using the audited `...of_interfaces` theorems.
3. `A1275.AxiomAudit` imports `LineDecimal` and prints the full inventory.
4. `Zeta23.lean` adds exactly `import Zeta23.ThmD.Sextuple.A1275.LineDecimal` after the baseline sextuple import. It does not import AxiomAudit.

`PostCertificateModulesProbe.lean` compiles the Assembly -> Unconditional -> LineDecimal proof terms while retaining an explicit certificate hypothesis. `CertificateFromReplayProbe.lean` separately compiles the Certificate proof shape under explicit `hrootReplay`. Neither claims the root theorem. Exact draft bytes/hashes are in `qualified-repo-shadow-manifest.json`.

## 5. Exact comparator audit

The feedback constant is

```text
(6*HD(1) - 10*pi*B)/(6-A)
 = (3000000000*HD(1) - 1094977*pi)/2993625000.
```

Use the directed bounds

```text
HD(1) > 672500703679/10^12
pi    < 314159265358979323847/10^20.
```

The coefficient of `HD(1)` is positive and the coefficient of `pi` is negative. Also `6-A = 23949/4000 > 0`. The exact directed lower bound is

```text
201406213933795020896911983481/299362500000000000000000000000
```

and its exact positive margin above `6727837118/10^10` is

```text
10067520896911983481/299362500000000000000000000000
```

The cross-multiplied positive numerator is `50337604484559917405000000000`. See `comparator-arithmetic.json`. Do not reuse the older `6727668568` artifact comparator or the repository's baseline `6727556` headline.

## 6. Direct generation and build order

Run only in a dedicated project-local feature worktree. Never use `/tmp`, never clean the shared worktree, and never change the frozen input directory. Use:

```bash
set -euo pipefail
REPO=<dedicated-project-local-A1275-worktree>
LAKE=/Users/mdumitrean/.elan/bin/lake
PY=/Users/mdumitrean/Desktop/dev/aigent/agi/.venv/bin/python
cd "$REPO"
test "$(git rev-parse HEAD)" = "5e9617d84ece3aeecdf983a8e7e9bfa50f413e5a"
test -z "$(git status --porcelain)"
export LC_ALL=C TZ=UTC PYTHONHASHSEED=0
```

### Phase A: architecture and baseline regressions

1. Apply StableCatalog and TreeFormat exact moves first.
2. Apply the separate baseline explicit-`Fin` generator/source patch.
3. Run normal/`-O` hostile generator tests and byte-equality checks.
4. Rebuild the shared and baseline graph before any improved chunk build:

```bash
export LEAN_NUM_THREADS=2
$LAKE --rehash build   +Zeta23.ThmD.Sextuple.Macro.StableCatalog   +Zeta23.ThmD.Sextuple.Macro.TreeFormat   +Zeta23.ThmD.Sextuple.Macro.TreeReader   +Zeta23.ThmD.Sextuple.Macro.Layout   +Zeta23.ThmD.Sextuple.Macro.ScalarData
$LAKE --rehash build   +Zeta23.ThmD.Sextuple.Macro.TreeAssembly   +Zeta23.ThmD.Sextuple.Certificate   +Zeta23.ThmD.Sextuple.LineDecimal
```

This baseline rebuild is mandatory because declaration ownership/import hashes changed, even though APIs are preserved.

### Phase B: improved foundations and frozen data

Generate into project-local staging directories twice, once with `$PY` and once with `$PY -O`. The new CLIs must use explicit input/output/report arguments. Compare complete sorted file/hash manifests, then atomically promote only the verified normal output.

Build in dependency order:

```bash
$LAKE --rehash build   +Zeta23.ThmD.Sextuple.Macro.ParametricAdapter   +Zeta23.ThmD.Sextuple.A1275.RefinementData
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.Catalog
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.ScalarData
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.TreeReader
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.TreeWords
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.Layout
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.ChunkCalibration
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.Assembly
```

Before the owner full build, run the v2 qualified closure, calibration, representative chunk, hostile layout/reader/cursor, and one-past `Fin 5` gates in `ARCHITECTURE-ACCEPTANCE-v2.md`.

### Phase C: long owner replay

Only after the architecture gate passes, start the owner build. The observed worst representative chunk used about 39.2 GB maximum resident size. On the 128 GiB host, cap Lake/Lean concurrency at two:

```bash
export LEAN_NUM_THREADS=2
/usr/bin/time -lp "$LAKE" --rehash build   +Zeta23.ThmD.Sextuple.A1275.TreeAssembly   > certificates/sextuple/logs/a1275-owner-tree-build.log 2>&1
```

Keep the full output. Do not use `tail`. Treat this as long-running work: start it nonblocking, record its handle/log path and source hashes in the atomic recovery ledger, and inspect the result later. Do not poll with `sleep`.

After it exits zero, verify all `8,953` chunk sources/oleans, all `90` part sources/oleans containing `8,952` node lemmas, and `improvedRootReplay`. Then run the independent audit over every source, log, olean, cursor edge, path axis, and assembly axis. `rootReplay` alone is not independent PASS.

### Phase D: certificate, endpoint, full clean build

Only after both owner and independent PASS:

```bash
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.Certificate
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.Unconditional
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.LineDecimal
$LAKE --rehash build +Zeta23.ThmD.Sextuple.A1275.AxiomAudit
$LAKE --rehash build Zeta23
```

Then repeat the ordered build from a clean build directory in the dedicated worktree (`$LAKE clean` there only), including the baseline root before the improved root. Run `Challenge`/`Solution` as a regression if comparator files or imports are touched. Do not delete build outputs in any shared worktree.

## 7. Closure, axiom, and forbidden scans

### 7.1 Resolved closure

For qualified Catalog/Reader/Words/Layout, every chunk, every part, TreeAssembly, and Certificate:

1. recursively walk source imports;
2. run Lean `--deps` and `--src-deps` with both `LEAN_PATH` and `LEAN_SRC_PATH` bound to the fresh build/source roots;
3. recursively resolve each direct dependency output, rather than treating one `--deps` call as transitive;
4. reject all banned modules and duplicate declaration collisions;
5. hash every first-party source and resolved `.olean`;
6. require the refactored Layout source/olean hashes, not a stale v1 olean.

Commit the sorted closure report. The final root closure must cover every chunk/assembly dependency, not only the top-level import header.

### 7.2 Axioms

Add prints for at least:

- `stableMacroTable_check`, `refinementTable_check`, `improvedMacroTable_check`
- `improvedScalarTable_check`, `improvedConcreteLeafCheck_sound`
- `improvedTopologyLayoutValid`, `improvedLeafLayoutValid`
- representative chunks and assembly nodes, `improvedRootReplay`, `improvedTreeCheck`
- `A1275.Certificate.sextuple_affine`
- conditional ledger/comparator/endpoints
- final unconditional ledger and both public endpoints

Parse the output and require the axiom set to be a subset of exactly:

```text
propext
Classical.choice
Quot.sound
```

Fail on `sorryAx` or any extra axiom. The audit-local certificate and endpoint probes both produced only that allowlist; improved layout produced `[propext, Quot.sound]`.

### 7.3 Forbidden constructs and admission scans

Update the repository audit tools so they cover the full improved transitive closure and generator set. Use a lexical Lean scanner that removes comments and strings before token checks. Reject:

```text
sorry, admit, axiom declarations, unsafe, native_decide, ofReduceBool,
implemented_by, partial def, opaque, extern, sorryAx
```

`decide +kernel` is allowed. Also require zero admission-critical Python `assert` occurrences and run the structured explicit-`Fin` audit over scalar indices, chunk path axes, and assembly split axes.

Required cross-checks:

```bash
$PY certificates/sextuple/tools/scan_forbidden.py --closure <final-closure.json>
$PY certificates/sextuple/tools/test_a1275_generators.py --python "$PY" --also-optimized
$PY certificates/sextuple/tools/verify_a1275_scalar.py --mode admission
$PY certificates/sextuple/tools/verify_a1275_tree.py --check-fin --check-assembly-axes
```

The scanner report must state exact file counts, hashes, and zero hits. Never interpret an unhandled `grep` exit code as a PASS.

## 8. Work that may proceed now vs blocked work

May proceed before owner replay:

- StableCatalog exact extraction and qualified Catalog closure.
- TreeFormat v2 exact move, baseline rebuild, and v2 architecture probes.
- Baseline explicit-`Fin` hardening as a separate regression change.
- ParametricAdapter, improved refinement/catalog/scalar/reader/word/layout promotion.
- Python fail-closed hardening, normal/`-O` hostile tests, provenance normalization.
- Conditional `ImprovedAssembly`, exact comparator, certificate/root templates with explicit hypotheses.

Must wait for the owner full replay and independent final tree PASS:

- committing/claiming `improvedRootReplay` as accepted authority;
- concrete `A1275.Certificate.sextuple_affine`;
- unconditional A1275 ledger interface;
- both `6727837118/10^10` public endpoints;
- root `Zeta23.lean` exposure and public headline documentation.

If owner `rootReplay` passes but the independent audit is still pending, keep the sources on the feature branch as unaccepted build candidates. Do not merge, expose, or claim the theorem.

## 9. Git and commit plan

`git-file-manifest.txt` expands every planned path: 9,128 paths total (9,116 added, 12 modified). It includes all 8,953 chunk files and all 90 assembly-part files explicitly. It excludes `.olean`, `.ilean`, staging, and audit-local probes.

Use seven reviewable commits:

1. `refactor(sextuple): extract stable catalog and tree format`
   - StableCatalog, TreeFormat, exact TreeReader/Layout import/declaration moves, baseline regeneration support.
2. `fix(sextuple): harden generated baseline Fin values`
   - separate explicit-Fin baseline source/generator change and full baseline regression evidence.
3. `feat(sextuple): add conditional A1275 scalar core`
   - ParametricAdapter, refinement/catalog/scalar, fail-closed scalar tools/data, conditional `A1275.Assembly`.
4. `feat(sextuple): add A1275 packed tree data`
   - reader, 31 word modules, TreeWords/Layout, raw/provenance tools and hostile reports.
5. `feat(sextuple): replay the A1275 affine tree`
   - 8,953 chunks, 90 assembly parts, root replay, independent final tree report. Create only after all owner/independent gates pass.
6. `feat(sextuple): prove the A1275 affine certificate`
   - concrete certificate after accepted root replay.
7. `feat(sextuple): expose the 0.6727837118 endpoints`
   - final ledger/endpoints, root import, docs, audit logs, scans, hashes.

Stage only the exact phase subset from the reviewed manifest, in bounded explicit batches. Never use `git add .` or `git add -A`. Before each commit, compare `git diff --cached --name-only` byte-for-byte with that phase's manifest subset. Commit no other agent's file.

There is no changelog mechanism in this math repository, so do not invent a changelog file. Update `README.md`, `AUDIT.md`, and certificate README/state only in commit 7. The existing comparator challenge remains valid and is outside the minimal graph; adding new comparator statements is an optional separate follow-up.

Do not push. Do not merge. Report the final commit IDs and audit hashes to the owner for review.

## 10. Audit-local evidence

- `StableCatalogProbe.lean`: PASS.
- `CatalogClosureProbe.lean`: PASS; 16-file local closure; no baseline ScalarData.
- `TreeFormatProbe`/exact v2 TreeFormat, TreeReader, Layout/API probes: PASS.
- `DirectImprovedTreeWordsProbe.lean`: PASS with direct AffineTree import.
- `TreeFormatImprovedLayoutProbe.lean`: PASS; axioms `[propext, Quot.sound]`.
- `CertificateFromReplayProbe.lean`: PASS with explicit `hrootReplay`; allowed axioms only.
- `EndpointCompositionProbe.lean`: PASS with explicit certificate hypothesis; allowed axioms only.
- `PostCertificateModulesProbe.lean`: PASS for Assembly/Unconditional/LineDecimal templates under the same explicit hypothesis.
- `comparator-arithmetic.json`: PASS.

See `probe-report.json`, `v2-treeformat-audit.json`, `module-graph.json`, and `input-hashes.json` for machine-readable evidence. None of these probes replaces the pending full replay or independent final tree audit.
