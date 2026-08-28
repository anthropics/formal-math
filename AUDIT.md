# Audit record

This file records the checks that were run on exactly the sources in this repository and how to reproduce them. Nothing here is part of the trusted base: a reader can re-run everything below, and can run the [comparator](https://github.com/leanprover/comparator) tool against the trusted statement files in `comparator/` (see `comparator/README.md`).

Toolchain: Lean `leanprover/lean4:v4.33.0-rc2`; Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (the commit Mathlib's tag `v4.33.0-rc2` points to, read from the tag archive; pinned in `lake-manifest.json`). Library name: `Zeta23`. Repository: <https://github.com/anthropics/zeta-23-lean>.

## How to reproduce

```bash
lake exe cache get            # optional: prebuilt Mathlib for the pinned commit; otherwise Mathlib builds from source
lake build                    # the Zeta23 library (default target: the headline modules imported by Zeta23.lean)
lake build Solution && lake env lean comparator/PrintAxioms.lean
lake build Solution.XiPrime && lake env lean comparator/PrintAxioms/XiPrime.lean
lake build Challenge.Union Solution.Union && lake env lean comparator/PrintAxioms/Union.lean
lake build Challenge.LineDecimal Solution.LineDecimal && lake env lean comparator/PrintAxioms/LineDecimal.lean
lake env lean comparator/PrintAxioms/UnionConditional.lean
lake env lean comparator/PrintAxioms/LineConditional.lean
lake env lean comparator/PrintAxioms/PairCeiling.lean
lake build Challenge Challenge.Multiplicity Challenge.XiPrime Challenge.Union Challenge.LineDecimal
                                # all trusted statement files; expect only deliberate sorry placeholders
```

## Recorded results at this commit

* `lake build`: completed successfully (8890 jobs, counting the Mathlib dependency closure); no errors and no `sorry` warnings.
* `lake build Solution` and `lake build Solution.Multiplicity`: completed successfully; no errors and no `sorry` warnings.
* `lake build Challenge` and the topic challenge files: complete with `declaration uses 'sorry'` warnings **only** in the trusted statement files, which state each theorem with a placeholder proof by design (`comparator/Challenge.lean`: 15, `comparator/Challenge/Multiplicity.lean`: 12), and with no other warnings or errors.
* Declarations of new axioms (`axiom ...`) anywhere in the repository, counted on the sources with comments and docstrings stripped: **0**.
* Occurrences of the `sorry` token outside comments: **27**, all in the trusted challenge statement files (`comparator/Challenge.lean`: 15, `comparator/Challenge/Multiplicity.lean`: 12); none under `Zeta23/` and none in any `Solution` file.
* Axiom audit: every line printed by the `#print axioms` commands below is exactly `[propext, Classical.choice, Quot.sound]`, Lean's three standard axioms; in particular no `sorryAx` and no project-specific axiom.

### `#print axioms` for the 27 comparator statements (`comparator/PrintAxioms*.lean`), verbatim

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

The trusted statement files and configurations for the comparator tool are in `comparator/`: `config-multiplicity.json` (12 statements), `config.json` (15 statements), `config-xiprime.json` (6 statements), `config-union.json` (4 statements), and `config-line-decimal.json` (4 statements). `comparator/README.md` explains what is trusted (`ChallengeDeps*.lean`, `Challenge*.lean`: Mathlib-only definitions and the statements) and what is not (`Solution*.lean` and the whole library), and how to run the tool, which independently re-checks that every `Solution` theorem has exactly the statement of its `Challenge` namesake and re-verifies the proofs in an external kernel.

## Amendment: the zeros of ξ′ and the bandwidth-one ceiling

This revision adds `Zeta23/XiPrime/` (comparator topic `XiPrime`, six statements) and `Zeta23/PairCeiling/` (no comparator topic), and replaces 69 shared modules by later versions with the same public statements (the trusted files `comparator/ChallengeDeps.lean`, `Challenge.lean`, `Challenge/Multiplicity.lean` are unchanged byte for byte). The checks above were re-run on exactly these sources:

* `lake build` (default target): completed successfully (9010 jobs); no errors and no `sorry` warnings.
* `lake build Solution Solution.Multiplicity Solution.XiPrime Challenge Challenge.Multiplicity Challenge.XiPrime ChallengeDeps ChallengeDeps.XiPrime`: complete, with `declaration uses 'sorry'` warnings **only** in the trusted statement files (`comparator/Challenge.lean`: 15, `comparator/Challenge/Multiplicity.lean`: 12, `comparator/Challenge/XiPrime.lean`: 6) and no other warnings or errors.
* Occurrences of the `sorry` token outside comments: **33**, all in the three trusted challenge files; none under `Zeta23/` and none in any `Solution` file. No `axiom` declarations anywhere in the repository outside the trusted challenge files' deliberate `sorry`s (the word `axiom` occurs in `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean` only inside a commented-out upstream test block, unchanged from upstream and from the previous revision; it declares nothing).
* `#print axioms`, 15 + 12 + 6 comparator statements (`comparator/PrintAxioms.lean`, `PrintAxioms/Multiplicity.lean`, `PrintAxioms/XiPrime.lean`): every line `[propext, Classical.choice, Quot.sound]`. The six ξ′ lines:

```
'xiPrime_zeros_in_open_critical_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_over_xi_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_quartic_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `#print axioms`, the ceiling theorems (`comparator/PrintAxioms/PairCeiling.lean`). All of these except the two kernel checks carry the displayed hypothesis `EnclOK` described in the README:

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

This revision removes from `comparator/ChallengeDeps.lean` the four counting functions that no
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
  warnings **only** in the trusted statement files (`comparator/Challenge.lean`: 15,
  `comparator/Challenge/Multiplicity.lean`: 12, `comparator/Challenge/XiPrime.lean`: 6). One
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
(`comparator/ChallengeDeps.lean`, resp. `ChallengeDeps/XiPrime.lean`) inlined character-for-character
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
  trusted statement files (`comparator/Challenge.lean`: 17, `comparator/Challenge/XiPrime.lean`: 6); informational deprecation warnings surfaced in untouched library files (same pinned Mathlib, unrelated to this revision), and no errors.
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
`comparator/Challenge.lean`'s module header and two Theorem-D doc comments drop the
Cauchy–Schwarz-constant mentions (those forms are no longer stated in this file), the header is
tightened, and the quoted paper title — with the README's title and citation — is updated to the
arXiv version, "More than two thirds of the zeros of the Riemann zeta function are simple and on
the critical line" (arXiv:2608.13637). The cMT docstring edit is applied identically in
`comparator/ChallengeDeps.lean`, keeping the inlined definition layer a character-for-character
copy. Because the comment-stripped sources are byte-identical to the previous revision, that
revision's recorded results — the build, `#print axioms` (23/23 standard-three) and the comparator
runs on both configurations — carry over to these sources unchanged; the pull request that carried
this revision additionally records an independent warm-cache build of them.

## Amendment: the simple-or-on-line endpoint

This revision adds direct-bandwidth-one dyadic and cumulative endpoints (`Zeta23.ThmD.thmD₀_union`, `_cumulative`) and certified decimal corollaries (`thmD₀_union_decimal`, `_cumulative_decimal`). Comparator topic `Union` contains all four statements. The trusted statements spell the union count as the natural-number inclusion-exclusion expression `N0 + Nsimple - N0simple`: `Ncount` and `N0` count with multiplicity, while the simple counts count points. The exact constant is `1 - (cMT⁻¹ - 1)/(3/2 + Real.sqrt 2)`. A kernel-checked Taylor-remainder argument proves that it lies strictly between 0.887620008173 and 0.887620008174. The definitions in `ChallengeDeps.lean` remain unchanged; only the `N0` and `Nsimple` docstrings were updated to record their use by the Union topic.

* `lake build` (default target): completed successfully (9,019 jobs); no errors and no `sorry` warnings from `Zeta23/`.
* `lake build Challenge.Union Solution.Union`: completed successfully; the only new warnings are the four deliberate `sorry`s in `comparator/Challenge/Union.lean`.
* Occurrences of the `sorry` token outside comments are now **37**, all in the four trusted challenge files; none under `Zeta23/` and none in any `Solution` file. No `axiom` declaration was added.
* `lake env lean comparator/PrintAxioms/Union.lean` prints the same permitted basis for all four statements:

```
'montgomery_taylor_simple_or_on_critical_line_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_or_on_critical_line_union_cumulative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'montgomery_taylor_simple_or_on_critical_line_union_decimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_or_on_critical_line_union_cumulative_decimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

* A local Comparator integration run of `comparator/config-union.json` completed with `Your solution is okay!`: statement comparison succeeded and both nanoda 0.4.13 and Lean's default kernel accepted the solution. The run used Comparator commit `75c730e` and lean4export commit `9fb131bb100eb32ccf6836f14e4f8328d13b6792`, matching Lean `v4.33.0-rc2`, with Comparator's official `scripts/fake-landrun.sh` because the host is macOS. It therefore exercises the previously missing statement-equality and independent-kernel pipeline, but is explicitly **not** a sandbox-trust result.
* `Zeta23.ThmD.UnionConditional` separately proves dyadic and cumulative coefficient
  `1 - ((cStar 1)⁻¹ - 1)/3 = 0.890833567893…` conclusions from either the explicit factorial
  ordinary-ordinate collision cap or a nonnegative pair-energy cap. A second Taylor certificate proves this
  coefficient lies strictly between 0.890833567893 and 0.8908335678932. The arithmetic caps are hypotheses,
  not consequences of `PaperInputs`; `comparator/PrintAxioms/UnionConditional.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for the certified numerical enclosure and all four
  conditional declarations.

## Amendment: certified critical-line decimal endpoint

`Zeta23.ThmD.LineDecimal` reuses the exact Taylor-remainder certificate to prove

```
0.672500703679 < HD(1) < 0.6725007036796.
```

It exports canonical epsilon-form dyadic and cumulative bounds with the certified lower coefficient for both
`N0star` and the stronger `N0simple` count. It also exports fixed-coefficient theorems at `0.6725`, giving a direct
formal witness that the asymptotic critical-line proportion is strictly greater than `0.672`. All denominators are
`Ncount`, counted with multiplicity; `N0star` counts distinct on-line points and `N0simple` counts simple on-line
points.

* `lake build` completed successfully (9,020 jobs); the new `Zeta23.ThmD.LineDecimal` module introduces no warning.
* `lake build Zeta23.ThmD.LineDecimal Challenge.LineDecimal Solution.LineDecimal`: completed successfully; the only
  new warnings are the four deliberate challenge `sorry`s.
* Occurrences of the `sorry` token outside comments are now **41**, all in the five trusted challenge files; none under
  `Zeta23/` and none in any `Solution` file. No `axiom` declaration was added.
* `comparator/PrintAxioms/LineDecimal.lean` reports only `[propext, Classical.choice, Quot.sound]` for the numerical
  enclosure, both strict constant lemmas, all four fixed-coefficient theorems, and all four comparator statements.
* A local run of `comparator/config-line-decimal.json` with the same version-matched Comparator, lean4export, nanoda,
  and official `fake-landrun.sh` setup recorded above completed with `Your solution is okay!`: statement equality
  succeeded and both nanoda and Lean's default kernel accepted. As above, this is a complete non-sandboxed integration
  replay, not a sandbox-trust result.

## Amendment: unconditional sextuple simple-critical-line improvement

`Zeta23.ThmD.Sextuple` (modules `Base`, `Interior`, `SpanAsymptotic`, `BlockPenalty`, `Transfer`, `Packing`, `Ledger`,
`AffineTree`, `Macro/*`, `Certificate`, `Unconditional`, `LineDecimal`) proves, with the six-translate Montgomery--Taylor
spectral penalty retained with positive sign and the exact rational constants `A₆ = 1/80`, `B₆ = 1094977/5000000000`,

```
liminf N₀ˢ(T,2T)/N(T,2T) ≥ (6·B_MT − 10π·B₆)/(6 − A₆) = 0.67275562065609…
```

(`Zeta23.ThmD.Sextuple.thmD₀_sextuple`, cumulative form `thmD₀_sextuple_cumulative`), together with the certified
strict enclosure `672755620655/10^12 < sextupleLowerConstant` and fixed-coefficient theorems at `0.6727556` and
`0.672755620655` in dyadic and cumulative windows. The only numerical ingredient is the five-dimensional affine
inequality `Certificate.sextuple_affine : ∀ g ≥ 0, A₆ ≤ E₆(g) + B₆·Σg`, proved by kernel replay (`decide +kernel`) of
an exact rational certificate: an audited 56-piece one-dimensional kernel envelope (`Macro/EnvelopeData.lean`, analytic
soundness in `Macro/Analytic.lean`), 871 exact scalar seam certificates (`Macro/ScalarData.lean`), and a dyadic-16384
branch-and-bound tree with 99,507 nodes / 49,754 leaves (packed data `Macro/TreeWords.lean`, 2,969 subtree modules
`Macro/Chunks/`, assembled by the once-proved generic lemma `replayAffineTree_split_step`). The soundness layer
`AffineTree.lean` is stated for arbitrary cursor streams, so no decoder is load-bearing; out-of-range codes make the
replay fail. No floating point, `native_decide`, `ofReduceBool`, or external result enters the proof.

* Clean from-scratch `lake build Zeta23.ThmD.Sextuple.LineDecimal` (Lake throttled to ten concurrent builders via
  `LEAN_NUM_THREADS=10`; Lake 5.0 has no `-j`): completed with exit 0 in 4,397 s wall, 27,935 s CPU, 16.5 GB peak
  RSS of the Lake process tree; every chunk module type-checks in 4–30 s with 1–3 GB of kernel working memory.
  The scalar-data module alone takes 108 s and 12.9 GB.
* `lake build` (default target, which now imports `Zeta23.ThmD.Sextuple.LineDecimal`): 12,057 jobs, success.
* `lake build Challenge.Sextuple Solution.Sextuple`: success; the only warnings are the four deliberate challenge
  `sorry`s. `comparator/PrintAxioms/Sextuple.lean` reports only `[propext, Classical.choice, Quot.sound]` for
  `Certificate.sextuple_affine`, the ledger instantiation, both strict constant lemmas, all six unconditional
  sextuple theorems, and all four comparator statements.
* Occurrences of the `sorry` token outside comments are now **45**, all in the six trusted challenge files; none under `Zeta23/` and none
  in any `Solution` file. No `axiom` declaration was added; a forbidden-construct scan
  (`sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|partial|opaque|extern`) over the 3,013
  new files is empty.
* Independent audits (read-only, separate agents): the generic affine-tree layer
  (`certificates/sextuple/audits/lean24c-affine-tree-audit.md`), the one-dimensional envelope
  (`lean24c-macro-analytic-audit.md`), the concrete tree/certificate modules
  (`lean25-concrete-certificate-static-audit.md`, PASS-WITH-NOTES, all notes discharged), and the scalar adapter with an
  exact-rational re-verification of all 871 certificates (`lean25-scalar-adapter-audit.md`, PASS-WITH-NOTES), all under
  `certificates/sextuple/audits/`. The Lean data modules regenerate byte-for-byte from their JSON sources, and the packed
  tree literals decode back to the serialized streams with matching SHA-256 digests (generators, canonical streams, and
  logs under `certificates/sextuple/`).
* No Comparator run has been performed for this topic yet; as for the other topics, a run with the version-matched
  tools is the next independent check.

## Amendment: conditional simple-critical-line collision and energy endpoints

`Zeta23.ThmD.LineConditional` isolates the exact new arithmetic input required to improve the unconditional
simple-critical-line result. The combinatorial theorem `ZeroConfig.N_le_N0s_add_collision` proves, with multiplicity
and on half-open windows,

```
N(T₁,T₂) ≤ N0simple(T₁,T₂) + Σγ M(γ)(M(γ)-1).
```

Consequently an explicitly assumed collision cap with coefficient `κ` gives dyadic and cumulative coefficient
`1-κ`; an explicitly assumed nonnegative ordinary-ordinate pair-energy cap with `K(0)=1` and coefficient `R` gives
coefficient `2-R`. Fixed 70% wrappers require the strict hypotheses `κ < 3/10` or `R < 13/10`. No collision or
energy cap is asserted by `PaperInputs`, so these theorems are conditional and intentionally have no trusted
Comparator challenge topic.

* `lake build` completed successfully (9,021 jobs); the changed and new Lean modules introduced no warning.
* The combined `Challenge`/`Solution` topic build completed successfully (9,018 jobs); its only `sorry` warnings are
  the 41 deliberate placeholders in the five trusted challenge files.
* A source scan with comments and strings stripped found no `axiom` declaration, no `sorryAx`, and exactly **41**
  `sorry` tokens, all in those five challenge files; there is no `sorry` under `Zeta23/` or `Solution`.
* `comparator/PrintAxioms/LineConditional.lean` audits the pointwise counting theorem, both abstract certificates,
  the four generic dyadic/cumulative endpoints, and the four fixed-70% endpoints. All eleven report only
  `[propext, Classical.choice, Quot.sound]`.

## Revision note: fork branch merged with upstream `main` (comparator restructuring)

This revision merges upstream's "Mathlib-only challenge modules; one statement set at the paper's constants"
and "ChallengeDeps minimized" revisions into the fork branch carrying the `Union`, `LineDecimal`, and `Sextuple`
topics. Nothing under `Zeta23/` changed in the merge. The three fork topics were brought to the upstream
convention: each of `Challenge/Union.lean`, `Challenge/LineDecimal.lean`, `Challenge/Sextuple.lean` now has
`import Mathlib` as its only import, with the complete definition layer of `ChallengeDeps.lean` inlined
character-for-character (the same block, in the same anonymous section, as in `Challenge.lean`). The two counting
functions the Union statements need and upstream removed from `ChallengeDeps.lean` (`N0`, `Nsimple`) now live in
`comparator/ChallengeDeps/Union.lean` (verbatim from `Zeta23/Statement.lean` §1), imported by `Solution/Union.lean`
and inlined as a second block in `Challenge/Union.lean`. No statement was reworded or renamed.
`formalization.yaml` lists the twelve fork statements under `main_results`.

* `lake build Zeta23 ChallengeDeps ChallengeDeps.XiPrime ChallengeDeps.Union Challenge Solution Challenge.XiPrime
  Solution.XiPrime Challenge.Union Solution.Union Challenge.LineDecimal Solution.LineDecimal Challenge.Sextuple
  Solution.Sextuple`: completed successfully (12,073 jobs); `declaration uses 'sorry'` warnings **only** in the five
  trusted challenge files (`Challenge.lean`: 17, `Challenge/XiPrime.lean`: 6, `Challenge/Union.lean`: 4,
  `Challenge/LineDecimal.lean`: 4, `Challenge/Sextuple.lean`: 4) — 35 in total.
* Occurrences of the `sorry` token outside comments: **35**, all in those five files; none under `Zeta23/` and none in
  any `Solution` file. No `axiom` declaration was added by the fork; the only `axiom` lines in the tree are the two
  pre-existing ones in the ported tactic test section of `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean`
  (identical to upstream), which no theorem depends on.
* `#print axioms` over all eight audit files (`PrintAxioms.lean`, `XiPrime`, `Union`, `LineDecimal`, `Sextuple`,
  `UnionConditional`, `LineConditional`, `PairCeiling`): 79 declarations, 77 exactly `[propext, Classical.choice,
  Quot.sound]`, and the two deliberate PairCeiling exceptions recorded above (`LawN256_check`: `[propext]`;
  `LawN256_edge`: no axioms).
* Comparator runs for the fork topics under the new Mathlib-only challenge modules have not been performed yet.

## Amendment: refined sextuple certificate at `A = 51/4000` (`0.6727837118`)

`Zeta23.ThmD.Sextuple.A1275` (modules `RefinementData`, `Catalog`, `ScalarData`, `TreeReader`, `TreeWords`,
`WordData/LeafBlocks000..030`, `Layout`, `FlatEquivalence`, `ChunkCalibration`, `Chunks/Chunk0000..8952`,
`Assembly/Part000..089`, `TreeAssembly`, `Certificate`, `Assembly`, `Unconditional`, `LineDecimal`, `AxiomAudit`;
shared new/refactored layers `Macro/StableCatalog`, `Macro/TreeFormat`, `Macro/ParametricAdapter`, and the
import-only/declaration-move changes to `Macro/ScalarData`, `Macro/TreeReader`, `Macro/Layout`) proves the same
sextuple improvement with the stronger affine coefficient `A = 51/4000 = 0.01275` and the unchanged
`B₆ = 1094977/5000000000`: `liminf N₀ˢ/N ≥ (6·B_MT − 10π·B₆)/(6 − 51/4000) = 0.67278371…` in dyadic and cumulative
windows (`Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple`, `thmD₀_sextuple_cumulative`), the certified strict enclosure
`6727837118/10^10 < sextupleLowerConstant` (`ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118`, from
`HD_one_decimal.1` and `Real.pi_lt_d20` only; exact margin `10067520896911983481/299362500000000000000000000000`),
and the fixed-coefficient theorems `thmD₀_sextuple_6727837118`, `thmD₀_sextuple_cumulative_6727837118`. The only
numerical ingredient is `A1275.Certificate.sextuple_affine : ∀ g ≥ 0, 51/4000 ≤ E₆(g) + B₆·Σg`, proved by kernel
replay (`decide +kernel`) of an exact rational branch-and-bound certificate: the unchanged audited 56-piece
envelope plus a Lean-checked 216-cell refinement catalog (272 one-dimensional models), 1,383 exact scalar seam
certificates (2,979 segments, proof-bearing `Fin` constructors only), and a 385,967-node dyadic tree with 192,984
leaves (191,474 quadratic, 1,510 affine tails, depth ≤ 89) replayed as 8,953 subtree chunks of ≤ 100 topology
tokens and assembled by 8,952 applications of the generic split lemma `replayAffineTree_split_step` in 90 modules.
The words are stored two levels deep (`Array (Array Nat)`: 140 topology words per block; the 31 `WordData`
groups of 25 leaf-block words) so that every kernel array lookup is short; `A1275/Layout.lean` proves the audited
flat layout predicates for the concatenations and `A1275/FlatEquivalence.lean` proves the replayed streams are
extensionally the audited flat packed streams. No floating point, `native_decide`, or external oracle enters the
proof; the checker soundness layer is unchanged and stated for arbitrary streams.

Checks run at this commit (logs under `certificates/sextuple/logs/`):

* Foundation build (`lake build +…A1275.ChunkCalibration` and dependencies): success; `A1275.ScalarData` 227 s,
  `A1275.RefinementData` 182 s, `Macro.ScalarData` 152 s, the 99-token calibration chunk 13 s (logs
  `a1275-foundation-1.log`, `a1275-foundation-2-blocked.log`).
* The 8,953 chunk modules, built by `certificates/sextuple/a1275/tools/build_a1275_chunks.py` (45 Lake batches of
  200, ten concurrent builders): 8,953/8,953 built, zero failures, **10,552 s wall (2.93 h), 98,753 s CPU, longest
  single chunk 50 s** (`a1275-chunks-driver.log`, `a1275-chunks-state.json`).
* Assembly (`lake build +…A1275.LineDecimal +…A1275.FlatEquivalence`): the 90 part modules in ≈ 662 s total
  (≤ 9.6 s each), `TreeAssembly` (`improvedRootReplay`) 3.3 s, `Certificate` 3.3 s, `Unconditional` 3.5 s,
  `LineDecimal` 3.3 s; 17,962 jobs, success (`a1275-assembly-build.log`).
* Baseline sextuple chain rebuilt on the refactored foundation (`lake build Zeta23.ThmD.Sextuple.LineDecimal`,
  three builders): 2,969 chunks, 30 parts, root replay, certificate, endpoints; 11,881 jobs, success
  (`a1275-baseline-rebuild.log`).
* Default `lake build` (root `Zeta23`, now importing `Zeta23.ThmD.Sextuple.A1275.LineDecimal`): 21,145 jobs,
  success (`a1275-root-build.log`).
* `lake build Challenge.SextupleA1275 Solution.SextupleA1275`: success; the only warnings are the four deliberate
  challenge `sorry`s (`lake_comparator_sextuple_a1275.log`). `comparator/PrintAxioms/SextupleA1275.lean`: all
  eleven printed declarations depend on exactly `[propext, Classical.choice, Quot.sound]`
  (`printaxioms_sextuple_a1275.log`).
* `Zeta23/ThmD/Sextuple/A1275/AxiomAudit.lean` (29 declarations: analytic tables and adapters, layout, the
  two-level/flat reader bridge, representative chunks and nodes, `improvedRootReplay`, `improvedTreeCheck`,
  `improvedRootBox_predicate`, `Certificate.sextuple_affine`, the conditional ledger/comparator layer, the
  unconditional ledger and both public endpoints): every line is `[propext, Classical.choice, Quot.sound]` except
  the two physical-layout lemmas, which use only `[propext, Quot.sound]` (`a1275-axiom-audit.log`,
  `audit-report.txt`).
* Forbidden-construct scan (`certificates/sextuple/tools/forbidden_scan.sh`, now covering `A1275/` and both
  comparator solution files): clean over 12,106 files. `sorry` census: 0 under `Zeta23/`, 0 in any `Solution`
  file, 39 deliberate challenge placeholders; `axiom` declarations: 0.
* External consistency: `certificates/sextuple/a1275/tools/verify_a1275_packed_words.py` decodes the Lean word
  literals back to the four canonical byte streams and reproduces the SHA-256 values of
  `certificates/sextuple/a1275/macro-scalar-tree/manifest.json` (`tree-artifacts/packed-words-verification.json`);
  the generated `TreeWords.lean` is byte-identical to the output of `tools/gen_a1275_blocked_words.py` on those
  streams and its flat word list equals the frozen single-level literal; the import closure of the A1275 chain
  contains none of the baseline data modules `Macro.ScalarData`, `Macro.TreeReader`, `Macro.TreeWords`.
* Provenance: the exact-rational generators and independent verifiers of the refinement catalog, the 5D tree,
  the scalar data, the word data and the chunk/assembly sources, the frozen-source manifests, and the independent
  audits of the data/plan, foundation, source freeze, resolved closure, scalar layer and conditional assembly are
  under `certificates/sextuple/a1275/` (see its `README.md`). Two deviations from the frozen generated sources
  are recorded there: the 90 assembly part modules were regenerated with explicit node statements (the frozen
  files had `theorem improvedNodeNNNN :=` with no statement and had never been compiled), and `TreeWords.lean`,
  `TreeReader.lean`, `Layout.lean` use the two-level word layout; the 8,953 chunk sources and the 31 `WordData`
  modules are byte-identical to the frozen publication.

## Amendment: refined sextuple certificate at `A = 257/20000` (`0.6727949489`)

`Zeta23.ThmD.Sextuple.A1285` (the same module layout as `A1275`: `ScalarData`, `TreeReader`, `TreeWords`,
`WordData/LeafBlocks000..138`, `Layout`, `FlatEquivalence`, `Chunks/Chunk00000..30152`, `Assembly/Part000..301`,
`TreeAssembly`, `Certificate`, `Assembly`, `Unconditional`, `LineDecimal`, `AxiomAudit`; the catalog and refinement
data are shared with `A1275`) proves the sextuple improvement at `A = 257/20000 = 0.01285`, `B₆` unchanged:
`liminf N₀ˢ/N ≥ (6·B_MT − 10π·B₆)/(6 − 257/20000) = 0.67279494…` in dyadic and cumulative windows
(`Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple`, `_cumulative`), the certified strict enclosure
`6727949489/10^10 < sextupleLowerConstant` (`ImprovedAssembly.A1285.sextupleLowerConstant_gt_6727949489`, from
`HD_one_decimal.1` and `Real.pi_lt_d20` only; exact margin `18463270896911983481/299357500000000000000000000000`),
and the fixed-coefficient theorems `thmD₀_sextuple_6727949489`, `thmD₀_sextuple_cumulative_6727949489`. The only
numerical ingredient is `A1285.Certificate.sextuple_affine : ∀ g ≥ 0, 257/20000 ≤ E₆(g) + B₆·Σg`, a `decide +kernel`
replay of an exact rational branch-and-bound certificate over the same 272-model catalog: 3,365 exact scalar seam
certificates (17,697 segments, proof-bearing `Fin` constructors only, each check lemma `decide +kernel`) and a
1,771,973-node dyadic tree with 885,987 leaves (884,314 quadratic, 1,673 affine tails, depth ≤ 73), replayed as
30,153 subtree chunks of ≤ 100 topology tokens and assembled by 30,152 applications of the generic split lemma in
302 modules. Every Lean module of the target is emitted by `certificates/sextuple/tools/gen_sextuple_target_lean.py`
from the canonical streams (the generator was validated by regenerating every committed `A1275` artifact); the words
are two-level literals, `improvedScalarTable` is a two-level `match`, and `A1285/FlatEquivalence.lean` proves the
replayed streams are extensionally the audited flat packed streams.

Checks run at this commit (logs under `certificates/sextuple/logs/`):

* Exact external replay of the serialized tree by the independent verifier
  (`certificates/sextuple/a1275/generators/verify_exact_refined_scalar_tree.py`): status PASS, full topology / kind /
  quadratic exhaustion, smallest quadratic margin `3.41×10⁻¹¹`, smallest tail margin `7.07×10⁻⁵`
  (`certificates/sextuple/a1285/macro-scalar-tree/exact-replay-report.json`).
* Foundation build: success; `A1285.ScalarData` 455 s (1,701 s with a flat scalar table), `TreeWords` 40 s,
  `Layout` 19 s, `FlatEquivalence` 12 s, `Assembly` 5.9 s (`a1285-foundation*.log`).
* The 30,153 chunk modules (`certificates/sextuple/a1275/tools/build_a1275_chunks.py --ns A1285`, 61 Lake batches of
  500, nine concurrent builders): 30,153/30,153 built, zero failures, **48,654 s wall (13.5 h), 420,042 s CPU,
  longest single chunk 27 s** (`a1285-chunks-driver.log`, `a1285-chunks-state.json`).
* Assembly (`lake build +…A1285.LineDecimal`): the 302 part modules in ≈ 3,334 s total (≤ 25 s each), `TreeAssembly`
  (`improvedRootReplay`) 4.5 s, `Certificate` 30 s, `Unconditional` 30 s, `LineDecimal` 4.5 s; 39,481 jobs, success
  (`a1285-assembly-build.pass1.log`, `a1285-assembly-build.log`; the first pass stopped at `Certificate` on a missing
  `open`, fixed in the generator and the module, no other change).
* Default `lake build` (root `Zeta23`, now importing `Zeta23.ThmD.Sextuple.A1285.LineDecimal`): 51,748 jobs, success
  (`a1285-root-build.log`).
* `lake build Challenge.SextupleA1285 Solution.SextupleA1285`: success; the only warnings are the four deliberate
  challenge `sorry`s (`lake_comparator_sextuple_a1285.log`). `comparator/PrintAxioms/SextupleA1285.lean`: all eleven
  printed declarations depend on exactly `[propext, Classical.choice, Quot.sound]` (`printaxioms_sextuple_a1285.log`).
* `Zeta23/ThmD/Sextuple/A1285/AxiomAudit.lean` (24 declarations): every line is `[propext, Classical.choice, Quot.sound]`
  except the two physical-layout lemmas on `[propext, Quot.sound]` (`a1285-axiom-audit.log`, `audit-report.txt`).
* Forbidden-construct scan (now covering `A1285/` and `comparator/Solution/SextupleA1285.lean`): clean over 42,712
  files; `sorry` census unchanged (0 under `Zeta23/`, 0 in any `Solution` file); `axiom` declarations: 0.
* External consistency: `certificates/sextuple/a1275/tools/verify_a1275_packed_words.py --ns A1285` decodes the Lean
  word literals back to the four canonical byte streams and reproduces the SHA-256 values of
  `certificates/sextuple/a1285/macro-scalar-tree/manifest.json` (`certificates/sextuple/a1285/packed-words-verification.json`).
* Frontier evidence (`certificates/sextuple/a1285/frontier/`): `A = 8/625 = 0.0128` also closes (771,969 tokens, verifier
  PASS; not integrated, superseded by `A1285`); `A = 129/10000 = 0.0129` does not close within a 6,000,000-node
  branch-and-bound cap (32 boxes pending, no obstruction) — a resource result, not a mathematical no-go.
