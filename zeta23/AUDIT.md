# Audit record

This file records the checks that were run on exactly the sources in this repository and how to reproduce them. Nothing here is part of the trusted base: a reader can re-run everything below, and can run the [comparator](https://github.com/leanprover/comparator) tool against the trusted statement files `Challenge.lean` and `Challenge/XiPrime.lean` (see README.md, "Verifying the statements with Comparator"). Paths and configuration names in the revision notes below are those of the revision they describe; since the Palomar-layout revision (last section) the challenge, solution and configuration files live at the top level of this directory (`comparator/config.json` → `comparator.json`, `comparator/config-xiprime.json` → `comparator-xiprime.json`, `comparator/PrintAxioms*.lean` → `scripts/PrintAxioms*.lean`).

Toolchain: Lean `leanprover/lean4:v4.33.0-rc2`; Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (the commit Mathlib's tag `v4.33.0-rc2` points to, read from the tag archive; pinned in `lake-manifest.json`). Library name: `Zeta23`. Repository: <https://github.com/anthropics/formal-math/tree/main/zeta23>.

## How to reproduce

```bash
lake exe cache get            # optional: prebuilt Mathlib for the pinned commit; otherwise Mathlib builds from source
lake build                    # the Zeta23 library (default target: the headline modules imported by Zeta23.lean)
lake build Solution && lake env lean scripts/PrintAxioms.lean
lake build Solution.XiPrime && lake env lean scripts/PrintAxioms/XiPrime.lean
lake env lean scripts/PrintAxioms/PairCeiling.lean
lake build Challenge          # the trusted statement files; expect only the deliberate sorry placeholders
```

## Recorded results at this commit

* `lake build`: completed successfully (8890 jobs, counting the Mathlib dependency closure); no errors and no `sorry` warnings.
* `lake build Solution` and `lake build Solution.Multiplicity`: completed successfully; no errors and no `sorry` warnings.
* `lake build Challenge` and the topic challenge files: complete with `declaration uses 'sorry'` warnings **only** in the trusted statement files, which state each theorem with a placeholder proof by design (`Challenge.lean`: 15, `Challenge/Multiplicity.lean`: 12), and with no other warnings or errors.
* Declarations of new axioms (`axiom ...`) anywhere in the repository, counted on the sources with comments and docstrings stripped: **0**.
* Occurrences of the `sorry` token outside comments: **27**, all in the trusted challenge statement files (`Challenge.lean`: 15, `Challenge/Multiplicity.lean`: 12); none under `Zeta23/` and none in any `Solution` file.
* Axiom audit: every line printed by the `#print axioms` commands below is exactly `[propext, Classical.choice, Quot.sound]`, Lean's three standard axioms; in particular no `sorryAx` and no project-specific axiom.

### `#print axioms` for the 27 comparator statements (`scripts/PrintAxioms*.lean`), verbatim

```
'two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_thirds_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'half_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'half_simple_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'three_quarters_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'three_quarters_distinct_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_half_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_three_quarters_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_thirds_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_thirds_simple_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'five_sixths_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'five_sixths_distinct_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_on_critical_line_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_on_critical_line_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_distinct_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_distinct_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_two_thirds_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_five_sixths_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_simple_on_critical_line_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_distinct_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `#print axioms` for the 28 `Zeta23` library theorems behind them (the theorems the comparator statements delegate to, plus the further results listed in README), verbatim

Each `Solution` theorem is a short delegation to the corresponding `Zeta23` theorem, so the two lists necessarily agree; the library names are the ones a reader of the library (or of the paper's appendix) will look for.

```
'Zeta23.thmA₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_A₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_B₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_C₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_simple_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_simple_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_dist_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_dist_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_B₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_C₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_simple_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_dist_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ZeroSide.TightMult.lemmaR_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparator

The trusted statement files and configurations for the comparator tool are in `comparator/`: `config-multiplicity.json` (12 statements), `config.json` (15 statements), `config-xiprime.json` (6 statements). `comparator/README.md` explains what is trusted (`ChallengeDeps*.lean`, `Challenge*.lean`: Mathlib-only definitions and the statements) and what is not (`Solution*.lean` and the whole library), and how to run the tool, which independently re-checks that every `Solution` theorem has exactly the statement of its `Challenge` namesake and re-verifies the proofs in an external kernel.

## Amendment: the zeros of ξ′ and the bandwidth-one ceiling

This revision adds `Zeta23/XiPrime/` (comparator topic `XiPrime`, six statements) and `Zeta23/PairCeiling/` (no comparator topic), and replaces 69 shared modules by later versions with the same public statements (the trusted files `ChallengeDeps.lean`, `Challenge.lean`, `Challenge/Multiplicity.lean` are unchanged byte for byte). The checks above were re-run on exactly these sources:

* `lake build` (default target): completed successfully (9010 jobs); no errors and no `sorry` warnings.
* `lake build Solution Solution.Multiplicity Solution.XiPrime Challenge Challenge.Multiplicity Challenge.XiPrime ChallengeDeps ChallengeDeps.XiPrime`: complete, with `declaration uses 'sorry'` warnings **only** in the trusted statement files (`Challenge.lean`: 15, `Challenge/Multiplicity.lean`: 12, `Challenge/XiPrime.lean`: 6) and no other warnings or errors.
* Occurrences of the `sorry` token outside comments: **33**, all in the three trusted challenge files; none under `Zeta23/` and none in any `Solution` file. No `axiom` declarations anywhere in the repository outside the trusted challenge files' deliberate `sorry`s (the word `axiom` occurs in `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean` only inside a commented-out upstream test block, unchanged from upstream and from the previous revision; it declares nothing).
* `#print axioms`, 15 + 12 + 6 comparator statements (`scripts/PrintAxioms.lean`, `PrintAxioms/Multiplicity.lean`, `PrintAxioms/XiPrime.lean`): every line `[propext, Classical.choice, Quot.sound]`. The six ξ′ lines:

```
'xiPrime_zeros_in_open_critical_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_over_xi_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_quartic_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `#print axioms`, the ceiling theorems (`scripts/PrintAxioms/PairCeiling.lean`). All of these except the two kernel checks carry the displayed hypothesis `EnclOK` described in the README:

```
'Zeta23.PairCeiling.ceiling_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_nearCUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.lawN256_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_law256' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_law256_decimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_nearCUE_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_law256_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.D1_nonneg_of_edgeNonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.LawN256_check' depends on axioms: [propext]
'Zeta23.PairCeiling.LawN256_edge' does not depend on any axioms
```

* Comparator (statement equality against the trusted files + kernel replay, with the independent `nanoda` kernel enabled): `config.json` — "Your solution is okay!" (343 s); `config-multiplicity.json` — okay (335 s); `config-xiprime.json` — okay (345 s).

## Revision note: ChallengeDeps minimized to the statements' dependency closure

This revision removes from `ChallengeDeps.lean` the four counting functions that no
challenge statement depends on (`N0`, `Nsimple`, `N0L`, `NsimpleL` — previously kept for
block-parity with the Zeta23 statement layer) and updates the README notes accordingly.
`Challenge.lean`, `Challenge/Multiplicity.lean` and `Challenge/XiPrime.lean` are unchanged byte
for byte, nothing under `Zeta23/` changes, and the removed names were outside every statement's
dependency closure, so the three comparator configurations are unaffected. The checks above were
re-run on exactly these sources:

* `lake build` (default target): completed successfully (9016 jobs, counting the Mathlib
  dependency closure); no errors and no `sorry` warnings.
* `lake build Solution Solution.Multiplicity Solution.XiPrime Challenge Challenge.Multiplicity
  Challenge.XiPrime ChallengeDeps ChallengeDeps.XiPrime`: complete, with `declaration uses 'sorry'`
  warnings **only** in the trusted statement files (`Challenge.lean`: 15,
  `Challenge/Multiplicity.lean`: 12, `Challenge/XiPrime.lean`: 6). One
  informational lint surfaced during the Solution build in an untouched library file
  (`Zeta23/XiPrime/ExplicitFormula/EntryError.lean:121`: "Variable name `hb` is not explicitly
  referenced"), unrelated to this revision; no other warnings and no errors.
* Occurrences of the `sorry` token outside comments: **33**, all in the three trusted challenge
  files (15 + 12 + 6); none under `Zeta23/` and none in any `Solution` file. Declarations of new
  axioms (`axiom ...`), counted the same way: **0**.
* `#print axioms`: all 15 + 12 + 6 comparator statements print exactly
  `[propext, Classical.choice, Quot.sound]`; the PairCeiling list matches the previous revision
  verbatim, including its two deliberate exceptions (`LawN256_check`: `[propext]`;
  `LawN256_edge`: no axioms).
* Comparator (statement equality against the trusted files + axiom audit + kernel replay of the
  solution): `config.json` — "Your solution is okay!" (220 s); `config-multiplicity.json` — okay
  (209 s); `config-xiprime.json` — okay (214 s). Run-mode caveats for this revision's runs: executed
  without the landrun sandbox (a pass-through stub) and with `enable_nanoda` set to false; the
  comparator binary and a matching `lean4export` were rebuilt under this repository's toolchain
  (v4.33.0-rc2), which required a one-line update to comparator's `Lean4Checker` dependency for a
  kernel-API signature change (`Kernel.Environment.addDeclCore` gained a `maxRecDepth` parameter;
  set to Lean's default, 512). The comparator test suite (11 projects, including every negative
  case — statement mismatches, illegal axioms, kind mismatches, olean tampering — all correctly
  rejected) passes under this rebuild. A fully sandboxed run with nanoda enabled, on an era-matched
  comparator build, remains the authoritative check.

## Revision note: Mathlib-only challenge modules; one statement set at the paper's constants

This revision makes two changes to `comparator/`, neither touching anything under `Zeta23/`.

**The challenge modules import only Mathlib.** Each trusted statement module (`Challenge.lean`,
`Challenge/XiPrime.lean`) now has `import Mathlib` as its single import, with the definition layer
(`ChallengeDeps.lean`, resp. `ChallengeDeps/XiPrime.lean`) inlined character-for-character
inside an anonymous section reproducing the layer's exact open context, so each trusted file can be
read completely on its own. The inlined block is the COMPLETE definition layer, not just the
constants the statements mention: elaborating the layer as a whole keeps the auxiliary lemmas it
generates (e.g. `N0star._proof_1`, which later definitions reuse) named identically on the challenge
and solution sides, which the comparator requires. `ChallengeDeps*.lean` continue to exist unchanged
for the Solution build, and the comparator re-checks that every definition elaborates identically to
its Solution-side namesake.

**One statement set, at the constants stated in the paper.** `Challenge.lean` now carries seventeen
statements — Theorems A–E with the multiplicity-aware constants (the previous `Challenge.lean`'s
Theorem A and optimal-window N₀* statements together with all twelve statements of the previous
`Challenge/Multiplicity.lean`) — and `config.json` lists exactly these seventeen names. Every kept
theorem (doc comment and statement) is byte-identical to its counterpart in the previous revision;
no statement was reworded and no theorem was renamed. The ten Cauchy–Schwarz-form statements of the
previous `Challenge.lean` (`half_simple_on_critical_line`(`_cumulative`),
`three_quarters_distinct`(`_cumulative`), `montgomery_taylor_simple_on_critical_line`,
`montgomery_taylor_distinct`, and the four Dirichlet analogues) are removed as statements: each is
implied by a kept statement with the same counting function and a strictly larger constant
(1/2 < 2/3, 3/4 < 5/6, 2c₁* − 1 < 2 − 1/c₁*, c₁* < (3 − 1/c₁*)/2), so nothing claimed by the previous
revision is lost. The underlying Cauchy–Schwarz theorems remain proved in the library
(`Zeta23/Final.lean`, `Zeta23/ThmD/Final.lean`, `Zeta23/ThmE/Final.lean`, `Zeta23/ThmDE/Final.lean`).
The files `Challenge/Multiplicity.lean`, `Solution/Multiplicity.lean`, `config-multiplicity.json` and
`PrintAxioms/Multiplicity.lean` are removed; `Solution.lean` proves all seventeen statements (its
Zeta23 imports are the union of the two previous solution modules'); the XiPrime topic is unchanged.

The checks above were re-run on exactly these sources:

* `lake build` (default target): completed successfully (9016 jobs, counting the Mathlib
  dependency closure); no errors and no `sorry` warnings.
* `lake build ChallengeDeps ChallengeDeps.XiPrime Challenge Challenge.XiPrime` and `lake build
  Solution Solution.XiPrime`: complete, with `declaration uses 'sorry'` warnings **only** in the two
  trusted statement files (`Challenge.lean`: 17, `Challenge/XiPrime.lean`: 6); informational deprecation warnings surfaced in untouched library files (same pinned Mathlib, unrelated to this revision), and no errors.
* Occurrences of the `sorry` token outside comments: **23**, all in the two trusted challenge files
  (17 + 6); none under `Zeta23/` and none in any `Solution` file. Declarations of new axioms
  (`axiom ...`), counted the same way: **0**.
* Statement identity across the consolidation, checked mechanically: each of the seventeen theorem
  blocks (doc comment + statement) in the merged `Challenge.lean` is byte-identical to its
  counterpart in the previous revision; the inlined definition section is byte-identical; the ten
  removed names appear nowhere.
* `#print axioms`: all 17 + 6 comparator statements print exactly
  `[propext, Classical.choice, Quot.sound]`; the PairCeiling list matches the previous revision
  verbatim, including its two deliberate exceptions (`LawN256_check`: `[propext]`;
  `LawN256_edge`: no axioms).
* Comparator (statement equality against the trusted file + axiom audit + kernel replay of the
  solution; comparator built from its v4.33.0-rc2 tag with a matching `lean4export`, both native to
  this repository's toolchain; real `landrun` sandbox; `nanoda` second kernel enabled; the repo's
  configs unmodified; Challenge/Solution artifacts scrubbed first so comparator builds both in its
  own sandbox): `config.json` (17 statements) — "Your solution is okay!" (299 s);
  `config-xiprime.json` — okay (301 s).
* Independent re-run by a second party on a separate machine (warm Mathlib; the actual comparator
  binary from the mixed-era trial kit with fake landrun and nanoda off, Lean default-kernel replay
  on): both configurations "Your solution is okay!", exit 0; all 23 `#print axioms` lines
  standard-three; per-name theorem-type comparison against the previous revision identical for all
  seventeen statements.

## Revision note: comment simplification; arXiv citation

Comment- and README-only; no statement, definition, or import bytes change (checked mechanically:
the Lean sources with all comments stripped are byte-identical before and after this revision).
`Challenge.lean`'s module header and two Theorem-D doc comments drop the
Cauchy–Schwarz-constant mentions (those forms are no longer stated in this file), the header is
tightened, and the quoted paper title — with the README's title and citation — is updated to the
arXiv version, "More than two thirds of the zeros of the Riemann zeta function are simple and on
the critical line" (arXiv:2608.13637). The cMT docstring edit is applied identically in
`ChallengeDeps.lean`, keeping the inlined definition layer a character-for-character
copy. Because the comment-stripped sources are byte-identical to the previous revision, that
revision's recorded results — the build, `#print axioms` (23/23 standard-three) and the comparator
runs on both configurations — carry over to these sources unchanged; the pull request that carried
this revision additionally records an independent warm-cache build of them.

## Revision note: Palomar template layout

Layout- and metadata-only; no statement, definition, proof or import bytes change (the Lean sources with all comments
stripped are byte-identical before and after this revision; the only edits inside `.lean` files are path mentions in
comment headers). Following the layout of
[PalomarRegistry/PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate), the former `comparator/`
directory is dissolved: `comparator/Challenge.lean`, `comparator/Solution.lean`, `comparator/ChallengeDeps.lean` and
their `XiPrime` submodules move to the top level of this directory (`Challenge.lean`, `Challenge/XiPrime.lean`, …),
`comparator/config.json` becomes `comparator.json` and `comparator/config-xiprime.json` becomes
`comparator-xiprime.json` (each gains the explicit `"definition_names": []` of the template; the theorem lists and
permitted axioms are unchanged), `comparator/PrintAxioms*.lean` move to `scripts/`, and `comparator/README.md` is
merged into `README.md`. `lakefile.toml` replaces the three `srcDir = "comparator"` stanzas by root-level libraries
(`roots = ["Challenge"]` etc.) and adds `Challenge` and `Solution` to the default targets, so `lake build` now
also builds the trusted files (expect their deliberate `sorry` warnings there). Added from the template:
`scripts/verify-comparator.sh` (Comparator and lean4export pinned at their `v4.33.0-rc2` tags; Landrun and NanoDa at
the template's commits), `scripts/landrun-wrapper.sh`, `scripts/validate-formalization.rb`, `test/`, `Gemfile`,
`docbuild/` (doc-gen4 at `v4.33.0-rc2`), and a CI workflow at the repository root
(`.github/workflows/zeta23-ci.yml`). `formalization.yaml` gains the required `project.description` (the registry
abstract), the template's automation/cost fields, per-statement alignment notes, the Palomar source-type vocabulary
(`paper`), and records that the Palomar submission is `comparator.json` only. The previous revision's recorded
results — the build, `#print axioms` (23/23 standard-three) and the Comparator runs on both configurations — carry
over to these sources unchanged. Checked in this revision: that Lake resolves every module in the new layout
(`lake build <module> --no-build` for `Challenge`, `Challenge.XiPrime`, `ChallengeDeps`, `ChallengeDeps.XiPrime`,
`Solution`, `Solution.XiPrime` and `Zeta23` reports each target as merely out of date, while a nonexistent module
name is rejected with the path Lake looked for), and that the comment-stripped Lean sources are byte-identical to
the previous revision's. No full build or Comparator run was performed for this revision (the Mathlib build cache for
the pinned commit was not reachable from the machine that prepared it); the CI workflow's manually dispatched
`build` and `comparator` jobs perform them on demand.
