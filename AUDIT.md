# Audit record

This file records the checks that were run on exactly the sources in this repository and how to reproduce them. Nothing here is part of the trusted base: a reader can re-run everything below, and can run the [comparator](https://github.com/leanprover/comparator) tool against the trusted statement files in `comparator/` (see `comparator/README.md`).

Toolchain: Lean `leanprover/lean4:v4.33.0-rc2`; Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (the commit Mathlib's tag `v4.33.0-rc2` points to, read from the tag archive; pinned in `lake-manifest.json`). Library name: `Zeta23`. Repository: <https://github.com/anthropics/zeta-23-lean>.

## How to reproduce

```bash
lake exe cache get            # optional: prebuilt Mathlib for the pinned commit; otherwise Mathlib builds from source
lake build                    # the Zeta23 library (default target: the headline modules imported by Zeta23.lean)
lake build Solution && lake env lean comparator/PrintAxioms.lean
lake build Solution.Multiplicity && lake env lean comparator/PrintAxioms/Multiplicity.lean
lake build Solution.XiPrime && lake env lean comparator/PrintAxioms/XiPrime.lean
lake build Challenge.Union Solution.Union && lake env lean comparator/PrintAxioms/Union.lean
lake env lean comparator/PrintAxioms/UnionConditional.lean
lake env lean comparator/PrintAxioms/PairCeiling.lean
lake build Challenge Challenge.Multiplicity Challenge.XiPrime Challenge.Union
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

The trusted statement files and configurations for the comparator tool are in `comparator/`: `config-multiplicity.json` (12 statements), `config.json` (15 statements), `config-xiprime.json` (6 statements), and `config-union.json` (4 statements). `comparator/README.md` explains what is trusted (`ChallengeDeps*.lean`, `Challenge*.lean`: Mathlib-only definitions and the statements) and what is not (`Solution*.lean` and the whole library), and how to run the tool, which independently re-checks that every `Solution` theorem has exactly the statement of its `Challenge` namesake and re-verifies the proofs in an external kernel.

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
  coefficient lies strictly between 0.890833567893 and 0.890833567894. The arithmetic caps are hypotheses,
  not consequences of `PaperInputs`; `comparator/PrintAxioms/UnionConditional.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for the certified numerical enclosure and all four
  conditional declarations.
