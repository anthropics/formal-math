# Zeta23 — a Lean 4 formalization of "More than two thirds of the zeta zeros are simple and on the critical line"

[![Zeta23 CI](https://github.com/anthropics/formal-math/actions/workflows/zeta23-ci.yml/badge.svg)](https://github.com/anthropics/formal-math/actions/workflows/zeta23-ci.yml)

This project lives in the `zeta23/` subdirectory of [anthropics/formal-math](https://github.com/anthropics/formal-math). All build commands below are run from this directory (`cd zeta23`).

> Research artifact. Not maintained and not accepting contributions.
> A Lean 4 formalization released as a static companion artifact to the paper.

Repository: <https://github.com/anthropics/formal-math/tree/main/zeta23>.

This repository accompanies the paper "More than two thirds of the zeta zeros are simple and on the critical line" by Levent Alpöge and Ralph Furman, [arXiv:2608.13637](https://arxiv.org/abs/2608.13637).
It contains a complete, `sorry`-free Lean 4 / Mathlib formalization of the paper's headline theorems, including proofs
of every analytic input the argument uses (Weil's explicit formula for ζ and for primitive Dirichlet L-functions,
the Riemann–von Mangoldt zero-counting formulas, Stirling-type estimates for Γ′/Γ on vertical lines,
Chebyshev–Mertens prime-sum estimates, and the Montgomery–Vaughan generalized Hilbert inequality). Nothing is
assumed: the top-level theorems have no hypotheses, the repository declares no axioms, and `#print axioms` on each
headline theorem reports only Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`.

Toolchain: Lean `v4.33.0-rc2`, Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (Mathlib's tag `v4.33.0-rc2`; pinned in `lake-manifest.json`).

The directory follows the layout of the [Palomar](https://palomar-registry.org/) submission template
([PalomarRegistry/PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate)): the trusted statement
surface is `Challenge.lean`, the proofs are connected to it by `Solution.lean`, and `comparator.json` tells
[Comparator](https://github.com/leanprover/comparator) which declarations must match. See "Submitting to Palomar" below.

## Repository map

- `Challenge.lean` — the small, **trusted** statement surface a reader audits: the seventeen theorem
  statements (Theorems A–E below, in the repository's labelling), each with proof `sorry`; imports only Mathlib.
  Its module docstring and the docstrings of the seventeen declarations carry the informal account of each statement.
- `ChallengeDeps.lean` — the fifteen Mathlib-only definitions the statements depend on (the counting functions and
  the Montgomery–Taylor constant), inlined character-for-character into `Challenge.lean`; kept as a module for the
  Solution build and as the readable reference copy.
- `Solution.lean` — the same seventeen statements, proved by delegating to the `Zeta23` library. **Untrusted**;
  Comparator checks it against `Challenge.lean`.
- `comparator.json` — the Comparator configuration for `Challenge` / `Solution` (17 theorem names, the three permitted
  axioms). **This is the configuration submitted to Palomar.**
- `Challenge/XiPrime.lean`, `ChallengeDeps/XiPrime.lean`, `Solution/XiPrime.lean`, `comparator-xiprime.json` — a
  second, independent topic (the zeros of ξ′, six statements), laid out the same way. Checked with Comparator but not
  part of the Palomar submission.
- `Zeta23.lean`, `Zeta23/` — the proof development (see "Layout of the proof development").
- `formalization.yaml` — the [formalization.yaml v0.4](https://github.com/mathlib-initiative/formalization.yaml)
  metadata: public abstract (`project.description`), sources, classification, authorship, automation, fidelity,
  review and statement alignment.
- `AUDIT.md` — the checks that were run at each revision and how to reproduce them.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — the Lake package (libraries `Zeta23`, `ChallengeDeps`,
  `Challenge`, `Solution`), its pinned dependency (Mathlib) and the Lean toolchain.
- `scripts/verify-comparator.sh` — runs pinned revisions of Comparator, lean4export, NanoDa and Landrun on
  `comparator.json` (or another configuration); `scripts/landrun-wrapper.sh` is the Landrun shim it uses;
  `scripts/validate-formalization.rb` checks `formalization.yaml`; `scripts/PrintAxioms*.lean` are the
  `#print axioms` audits. `test/` exercises the wrapper and the validator.
- `docbuild/` — the nested doc-gen4 project (`cd docbuild && lake build Zeta23:docs`).
- `LICENSE`, `NOTICE` — Apache-2.0, and the attribution notices for the ported files (see "Provenance and attribution").
  The licence file Palomar reads is the identical `LICENSE` at the repository root.

## What is proved

Write N(T₁,T₂) for the number of zeros ρ of ζ with 0 < Re ρ < 1 and T₁ < Im ρ ≤ T₂, counted with
multiplicity; N₀(T₁,T₂) for the on-line zeros counted with multiplicity; N₀*(T₁,T₂) for the number of
*distinct* on-line zeros; Nˢ for the simple zeros anywhere in the strip; N₀ˢ for those that are on the
line and *simple*; N_d for the number of distinct zeros; N(T) := N(0,T) etc.
All of these are defined directly from Mathlib's `riemannZeta` and `analyticOrderAt`
([`ChallengeDeps.lean`](ChallengeDeps.lean), 15 definitions, is the complete list
of definitions the statements depend on — nothing else). "liminf_{T→∞} X(T)/N(T) ≥ c" is formalized in the ε-form
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`. Here c₁* = √2·tan ϑ/(1+ϑ·tan ϑ), ϑ = 1/√2 (= 0.75329…) is the
Montgomery–Taylor constant of Theorem D.

The labels A–E below are the repository's own (they are used throughout the Lean docstrings). In the arXiv
version of the paper, B and C are Theorem A(i) and A(ii), D is the Montgomery–Taylor-window improvement stated with
them, E is Theorem B, and A (the on-the-line counts N₀* ≥ N₀ˢ) is the companion recorded in the paper's Appendix A;
`formalization.yaml` (`alignment.statements`) records this correspondence statement by statement.

| | statement (as in the paper) | Lean name (`Challenge.lean` / `Solution.lean`) | underlying Zeta23 theorem |
|---|---|---|---|
| **A** | liminf N₀*(T,2T)/N(T,2T) ≥ 2/3, and liminf N₀*(T)/N(T) ≥ 2/3 | `two_thirds_on_critical_line`(`_cumulative`) | `Zeta23.thmA₀`(`_cumulative`) (`Zeta23/Final.lean`) |
| **B** | liminf N₀ˢ/N ≥ 2/3: at least two thirds of the zeros are simple and on the critical line (dyadic and cumulative) | `two_thirds_simple_on_critical_line`(`_cumulative`) | `Zeta23.thmB₀_mult`(`_cumulative`) (`Zeta23/FinalMult.lean`) |
| **C** | liminf N_d/N ≥ 5/6 (dyadic and cumulative) | `five_sixths_distinct`(`_cumulative`) | `Zeta23.thmC₀_mult`(`_cumulative`) |
| **D** | with the optimal (Montgomery–Taylor) window: liminf N₀*(T,2T)/N(T,2T) ≥ 2 − 1/c₁* (= 0.67250…), the same for N₀ˢ (dyadic and cumulative), and N_d: ≥ (3 − 1/c₁*)/2 (= 0.83625…) (dyadic and cumulative) | `montgomery_taylor_on_critical_line`, `montgomery_taylor_simple_on_critical_line_mult`(`_cumulative`), `montgomery_taylor_distinct_mult`(`_cumulative`) | `Zeta23.ThmD.thmD₀` (`Zeta23/ThmD/Final.lean`), `Zeta23.ThmD.thmD₀_simple_mult`, `thmD₀_dist_mult` (`Zeta23/ThmD/Mult.lean`) |
| **E** | for every primitive Dirichlet character χ mod q > 1, the analogues of A, B, C and D for the zeros of L(s,χ) (Mathlib's `DirichletCharacter.LFunction χ`) | `dirichlet_two_thirds_on_critical_line`, `dirichlet_two_thirds_simple_on_critical_line`, `dirichlet_five_sixths_distinct`, `dirichlet_montgomery_taylor_on_critical_line`, `dirichlet_montgomery_taylor_*_mult` | `Zeta23.ThmE.thmE_A₀`, `thmE_B₀_mult`, `thmE_C₀_mult`; `Zeta23.ThmDE.thmE_D₀`, `thmE_D₀_simple_mult`, `thmE_D₀_dist_mult` |

Note on Theorem C: in this repository the constant 5/6 is obtained from the rank–trace inequality of §3 applied with
parameter c = 3 (`Zeta23.ZeroSide.ZeroBlockData.mult_three`, `Zeta23/ZeroSide/Mult.lean`); the paper's text derives the
same 5/6 from Proposition 4.5(iii) with c = 2.

Also proved here, beyond the statements of Theorems A–E: the rank–trace certificate ("Lemma R") is TIGHT — for on-line
atoms with integer multiplicities m_j ≤ c on orthonormal vectors together with b pair-blocks of eigenvalue c,
2c·tr(P+Q) − ‖P+Q‖_F² = Σ_j k_c(m_j) + c²·b, i.e. the inequality cannot be improved using only these quantities
(`Zeta23.ZeroSide.TightMult.lemmaR_tight`, `Zeta23/ZeroSide/TightMult.lean`; cited in the paper's appendix).

Also included, beyond Theorems A–E (each group has its own trusted statement file or, where noted, is checked with `#print axioms` only; neither is part of the Palomar submission):

* **The zeros of ξ′** (`Zeta23/XiPrime/`, Comparator topic `XiPrime`: [`Challenge/XiPrime.lean`](Challenge/XiPrime.lean), six statements, configuration [`comparator-xiprime.json`](comparator-xiprime.json)): unconditionally, at least 0.85838 of the zeros of ξ′ (the derivative of the completed zeta function) with ordinates in (T, 2T] are simple and on the critical line and at least 0.92919 are distinct (flat window; 0.86864 / 0.93432 with the quartic window), all zeros of ξ′ lie in the open critical strip, and Re ξ′/ξ > 0 on Re s ≥ 1 — `Zeta23.XiPrime.xiDeriv_simple_on_line`(`_cumulative`, `_quartic_std`) in `Zeta23/XiPrime/Final.lean`. The argument is the one of Theorem B with ξ′ in place of ζ (the rank–trace device applied to the Farmer–Gonek(–Lee)/Montgomery argument for ξ′; Farmer–Gonek, arXiv:0803.0425 = Farmer–Gonek–Lee, J. London Math. Soc. (2) 90 (2014)). In the docstrings under `Zeta23/XiPrime/`, labels of the form `[XF′ Lemma 6.1]`, `[XF′ Thm 8.2]`, `[XF′ (Z3)]` refer to the authors' technical supplement on the explicit formula for ξ′/ξ and the two-trace transfer, which is not included in this repository; these labels record provenance only — what is relied upon is in each case the Lean statement that the docstring introduces. (The counting functions in `ChallengeDeps/XiPrime.lean` are finite sums / cardinalities over the set of zeros of ξ′ in a height window; that set is finite because every zero of ξ′ lies in the open critical strip — the first of the six statements — and the zeros of an entire function are isolated.)

* **Certified critical-line decimal endpoint** (`Zeta23/ThmD/LineDecimal.lean`; comparator topic `LineDecimal`, four statements): a kernel-checked rational enclosure proves
  `0.672500703679 < HD(1) < 0.6725007036796`. Consequently, in both dyadic and cumulative windows,
  `liminf N₀*/N ≥ 0.672500703679` and, more strongly, the same lower bound holds for the simple-and-on-line count
  `N₀ˢ/N`. The fixed-coefficient theorems `thmD₀_6725` and `thmD₀_simple_mult_6725` (and their cumulative forms)
  state directly that at least 67.25% are represented by distinct, respectively simple, on-line zeros for all
  sufficiently large heights. In particular this is strictly greater than 67.2%, with no RH or other hypothesis.

* **Sextuple (six-translate) simple-critical-line improvement** (`Zeta23/ThmD/Sextuple/`; comparator topic `Sextuple`, four statements): an unconditional improvement of the Montgomery–Taylor simple-on-line proportion,
  `liminf N₀ˢ(T,2T)/N(T,2T) ≥ (6·B_MT − 10π·B₆)/(6 − A₆) = 0.67275562065609…` with the exact rational constants `A₆ = 1/80`,
  `B₆ = 1094977/5000000000`, in dyadic and cumulative windows (`Zeta23.ThmD.Sextuple.thmD₀_sextuple`, `_cumulative`), with fixed-coefficient
  corollaries at `0.6727556` and `0.672755620655` (`thmD₀_sextuple_6727556`, `thmD₀_sextuple_672755620655`, cumulative forms). The analytic input
  is a positive spectral penalty for six translates of the Montgomery–Taylor kernel; its only numerical ingredient is the five-dimensional
  affine inequality `A₆ ≤ E₆(g) + B₆·(g₀+…+g₄)` for all nonnegative gaps (`Zeta23.ThmD.Sextuple.Certificate.sextuple_affine`), proved by
  kernel replay (`decide +kernel`) of an exact rational branch-and-bound certificate: an audited 56-piece one-dimensional kernel envelope
  (`Zeta23/ThmD/Sextuple/Macro/EnvelopeData.lean`), 871 exact scalar seam certificates, and a 99,507-node dyadic tree with 49,754 leaves split
  over 2,969 subtree modules (`Macro/Chunks/`) and assembled through one generic split lemma. No floating point, `native_decide`, or external
  oracle enters the proof; the checker soundness layer (`Zeta23/ThmD/Sextuple/AffineTree.lean`) is stated for arbitrary streams.
  Generators, canonical certificate data, independent audits, and build logs are under [`certificates/sextuple/`](certificates/sextuple/).

* **Refined sextuple certificate at `A = 51/4000`** (`Zeta23/ThmD/Sextuple/A1275/`; comparator topic `SextupleA1275`, four statements): the same sextuple
  argument with the stronger affine coefficient `A = 51/4000 = 0.01275` (same `B₆`), giving
  `liminf N₀ˢ(T,2T)/N(T,2T) ≥ (6·B_MT − 10π·B₆)/(6 − 51/4000) = 0.67278371…` in dyadic and cumulative windows
  (`Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple`, `_cumulative`) with the fixed-coefficient corollaries `thmD₀_sextuple_6727837118`
  and `thmD₀_sextuple_cumulative_6727837118` at `0.6727837118`. The certificate `Zeta23.ThmD.Sextuple.A1275.Certificate.sextuple_affine`
  (`51/4000 ≤ E₆(g) + B₆·(g₀+…+g₄)`) is again a `decide +kernel` replay of an exact rational branch-and-bound tree: the unchanged 56-piece
  envelope plus a separately Lean-checked 216-cell refinement catalog (`A1275/RefinementData.lean`, 272 selectable one-dimensional models),
  1,383 exact scalar seam certificates, and a 385,967-node dyadic tree with 192,984 leaves split over 8,953 subtree modules (`A1275/Chunks/`),
  assembled through the same generic split lemma in 90 modules (`A1275/Assembly/`). The analytic layers (`Base`, `Ledger`, `Final`, the generic
  checker soundness in `AffineTree.lean` and `Macro/ParametricAdapter.lean`) are reused unchanged; the words are stored two levels deep for
  cheap kernel lookups, and `A1275/FlatEquivalence.lean` proves the replayed streams equal the audited flat packed streams. Data, generators,
  independent audits, and logs are under [`certificates/sextuple/a1275/`](certificates/sextuple/a1275/).

* **Refined sextuple certificate at `A = 257/20000`** (`Zeta23/ThmD/Sextuple/A1285/`; comparator topic `SextupleA1285`, four statements): the same
  argument at `A = 0.01285`, giving `liminf N₀ˢ(T,2T)/N(T,2T) ≥ (6·B_MT − 10π·B₆)/(6 − 257/20000) = 0.67279494…` in dyadic and cumulative windows
  (`Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple`, `_cumulative`) with the fixed corollaries `thmD₀_sextuple_6727949489`, `thmD₀_sextuple_cumulative_6727949489`
  at `0.6727949489`. Its certificate `A1285.Certificate.sextuple_affine` replays a 1,771,973-node exact tree (885,987 leaves, 3,365 scalar seam
  certificates over the same 272-model catalog) as 30,153 subtree modules and 302 assembly modules; all Lean modules of the target are produced by one
  generator (`certificates/sextuple/tools/gen_sextuple_target_lean.py`) from the canonical streams. Data, audits, and logs are under
  [`certificates/sextuple/a1285/`](certificates/sextuple/a1285/). The neighbouring `A = 129/10000` does not close within a 6,000,000-node
  branch-and-bound cap (no obstruction found); see `certificates/sextuple/a1285/frontier/`.

* **Refined sextuple certificate at `A = 129/10000`** (`Zeta23/ThmD/Sextuple/A1290/`; comparator topic `SextupleA1290`, four statements): the same argument
  at `A = 0.0129`, giving `liminf N₀ˢ(T,2T)/N(T,2T) ≥ (6·B_MT − 10π·B₆)/(6 − 129/10000) = 0.67280056…` in dyadic and cumulative windows
  (`Zeta23.ThmD.Sextuple.A1290.thmD₀_sextuple`, `_cumulative`) with the fixed corollaries `thmD₀_sextuple_6728005676`, `thmD₀_sextuple_cumulative_6728005676`
  at `0.6728005676`. This target needed a larger one-dimensional catalog: `A1290/RefinementData2.lean` adds 394 Lean-checked pieces (24 narrow wells on
  stable piece 36; 370 constant-barrier cells of width 1/64 over the barrier piece at 44.79–49.56 and over `[59, 60]`, each with the lower bound that Lean's own
  interval evaluator `kernelRange` certifies), giving the 666-model catalog `A1290/Catalog.lean`. The certificate replays a 3,550,925-node exact tree
  (1,775,463 leaves, 4,299 scalar seam certificates) as 56,924 subtree modules and 570 assembly modules. Data, the catalog generators (with an exact
  Python replica of the interval arithmetic), the frontier analysis (the method's true ceiling `A* ≤ 0.0129938`, i.e. `R ≤ 0.672811`; `A = 0.01293` closes
  externally, `A ≥ 0.01295` does not within the node budget), audits and logs are under [`certificates/sextuple/a1290/`](certificates/sextuple/a1290/).

* **Conditional simple-critical-line collision/energy seam** (`Zeta23/ThmD/LineConditional.lean`; `#print axioms` audit only): the exact combinatorial inequality
  `N ≤ N₀ˢ + Σγ M(γ)(M(γ)-1)` yields `liminf N₀ˢ/N ≥ 1-κ` from an explicitly assumed factorial
  ordinary-ordinate collision cap `Σγ M(γ)(M(γ)-1) ≤ (κ+o(1))N`. More generally, for a kernel
  `K ≥ 0` with `K(0)=1`, an explicitly assumed ordinary-ordinate pair-energy cap `E_K ≤ (R+o(1))N`
  yields `liminf N₀ˢ/N ≥ 2-R`. Both conclusions are proved in dyadic and cumulative form. Fixed 70%
  wrappers require the strict hypotheses `κ < 3/10` or `R < 13/10`; equality gives only the limiting
  threshold. These collision and energy caps are new conditional inputs and are not consequences of the
  repository's unconditional analytic assumptions.

* **The simple-or-on-line endpoint** (`Zeta23/ThmD/Union.lean`, `UnionDecimal.lean`; comparator topic `Union`, four statements): unconditionally, in dyadic windows (T, 2T] and cumulative windows (0, T],
  `liminf (N₀ + Nˢ − N₀ˢ)/N ≥ 1 − ((c₁*)⁻¹ − 1)/(3/2 + √2)`
  (`Zeta23.ThmD.thmD₀_union`, `_cumulative`). Here N and N₀ count with multiplicity, Nˢ and N₀ˢ count simple points, and the
  natural-number expression `N₀ + Nˢ − N₀ˢ` is the inclusion-exclusion count of zeros that are simple or on the
  critical line, counted with multiplicity. The exact coefficient is instantiated directly at bandwidth λ = 1.
  A kernel-checked Taylor-remainder certificate proves it lies strictly between 0.887620008173 and 0.887620008174;
  the corresponding exact-rational ε-form count bounds are `thmD₀_union_decimal` and `_cumulative_decimal`.
  The denominator `Q = 3/2 + √2` is emitted by the sharp zero-side block bookkeeping, not by an accumulated analytic
  error: at `C = 2 + √2`, a simple off-line pair and a reflected pair of double zeros simultaneously saturate
  `C² = 2(2C-1)`, `C² = 4Q`, and `2C-1 = 2Q`. Thus `Q(3-Q)=1/4`; improving `Q` requires arithmetic information beyond
  the present block/moment interface. `Zeta23/ThmD/UnionConditional.lean` isolates such a missing input: a factorial
  ordinary-ordinate collision cap `Σ M(γ)(M(γ)-1) ≤ (((c₁*)⁻¹-1)+o(1))N`, or the corresponding nonnegative pair-energy
  cap, would raise both endpoints to `1-((c₁*)⁻¹-1)/3 = 0.890833567893…`; neither cap is asserted unconditionally.
  The proved inequality `3 Nbad ≤ Σ M(γ)(M(γ)-1)` is sharp at one reflected double pair; any additional zeros sharing
  that ordinate only add slack, so collisions obstruct proving the cap rather than applying it.

* **The zeros of ξ′** (`Zeta23/XiPrime/`, comparator topic `XiPrime`, six statements): unconditionally, at least 0.85838 of the zeros of ξ′ (the derivative of the completed zeta function) with ordinates in (T, 2T] are simple and on the critical line and at least 0.92919 are distinct (flat window; 0.86864 / 0.93432 with the quartic window), all zeros of ξ′ lie in the open critical strip, and Re ξ′/ξ > 0 on Re s ≥ 1 — `Zeta23.XiPrime.xiDeriv_simple_on_line`(`_cumulative`, `_quartic_std`) in `Zeta23/XiPrime/Final.lean`. The argument is the one of Theorem B with ξ′ in place of ζ (the rank–trace device applied to the Farmer–Gonek(–Lee)/Montgomery argument for ξ′; Farmer–Gonek, arXiv:0803.0425 = Farmer–Gonek–Lee, J. London Math. Soc. (2) 90 (2014)). In the docstrings under `Zeta23/XiPrime/`, labels of the form `[XF′ Lemma 6.1]`, `[XF′ Thm 8.2]`, `[XF′ (Z3)]` refer to the authors' technical supplement on the explicit formula for ξ′/ξ and the two-trace transfer, which is not included in this repository; these labels record provenance only — what is relied upon is in each case the Lean statement that the docstring introduces. (The counting functions in `ChallengeDeps/XiPrime.lean` are finite sums / cardinalities over the set of zeros of ξ′ in a height window; that set is finite because every zero of ξ′ lies in the open critical strip — the first of the six statements — and the zeros of an entire function are isolated.)

* **The bandwidth-one ceiling** (`Zeta23/PairCeiling/`, no Comparator topic; `#print axioms` audit below): the stability inequality behind the paper's remark on the optimality of the method — for every certificate (c₀, r) of the type used in Theorem B (r ∈ C¹[0,1], r′ differentiable off a countable set with integrable derivative) that is valid against a configuration whose form-factor measure has grid masses s_j and simple-point fraction p, one has c₀ + ∫₀¹ r(x)·x dx ≤ p + |r(1)|·|D(1)| + |r′(1)|·|E(1)| + (sup|E|)·∫₀¹|r″| (`Zeta23.PairCeiling.ceiling_stability`, `Zeta23/PairCeiling/Stability.lean`, two integrations by parts) — and its instance at an explicit 256-periodic law (`Zeta23.PairCeiling.ceiling_law256`, `ceiling_law256_decimal`, `ceiling_nearCUE_signed`, `ceiling_law256_signed`; files `NearCUE.lean`, `RowCert.lean`, `LawN256.lean`, `CeilingLaw256.lean`, `Signed.lean`): every bandwidth-one certificate certifies a proportion of simple zeros at most 0.6818287 + 2.55·10⁻⁶·(|r′(1)| + ∫|r″|). The ONE displayed hypothesis of these theorems is `EnclOK`: that the law's form factor S(j), j = 1…256, lies in the 256 integer enclosures recorded in `LawN256.lean` (obtained outside Lean by interval arithmetic from an exact-rational certificate, sha256 `cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`, available from the authors); everything downstream of the enclosures — the 255 near-CUE row inequalities |256·S(j) − j| ≤ 3·10⁻⁴⁰ (0 < j < 256), the edge bound |D(1)| ≤ 0.82395317, the sign of the edge term — is checked in the kernel by `decide` (`LawN256_check`, `LawN256_edge`), and the analytic inequality is proved in Lean.

How the Comparator configuration covers this: [`comparator.json`](comparator.json) (seventeen statements,
[`Challenge.lean`](Challenge.lean)) contains Theorems A–E exactly as in the table above, each at
the constant stated in the paper. For B–E these multiplicity-aware constants are obtained from the analytic inputs by
the rank–trace inequality of §3 applied with parameter c = 2 (simple zeros) and c = 3 (distinct zeros) to the
multiplicity-aware zero side (`Zeta23/ZeroSide/Mult.lean`, `Zeta23/Assembly/SeamMult.lean`, `Zeta23/FinalMult.lean`).
The strictly weaker *Cauchy–Schwarz forms* of B–E — N₀ˢ/N ≥ 1/2, N_d/N ≥ 3/4, and with the optimal window
2c₁* − 1 (= 0.50659…) and c₁*, for ζ and for L(s,χ) — were stated separately in revision v1.0 of this repository and
are each implied by the corresponding statement above (the same counting function, a larger constant); the Zeta23
library still proves them (`Zeta23.thmB₀`, `Zeta23.thmC₀`, `Zeta23.ThmD.thmD₀_simple`, … in `Zeta23/Final.lean`,
`Zeta23/ThmD/Final.lean`, `Zeta23/ThmE/Final.lean`, `Zeta23/ThmDE/Final.lean`).
The same A–C statements in the Cauchy–Schwarz form, with the same names inside namespace `Zeta23`, are in
[`Zeta23/Unconditional.lean`](Zeta23/Unconditional.lean).

### Reading notes for the statements

What a skeptical reader has to trust: Mathlib's definitions of `riemannZeta`, `DirichletCharacter.LFunction`,
`analyticOrderAt`, `Set.ncard`, `finsum`; the trusted file `Challenge.lean` (whose only import is Mathlib; its inlined
definition layer is the content of `ChallengeDeps.lean`); the Lean kernel; and Comparator's own
assumptions (its README). Nothing under `Zeta23/` needs to be read to know *what* is proved.

N(T₁,T₂) on the LEFT of every inequality counts zeros **with multiplicity**, while N₀*, N₀ˢ, N_d on the right count
**distinct** points — the strong direction. "Nontrivial zero" is rendered as "zero with 0 < Re ρ < 1"; that every
zero other than the trivial ones lies in the open strip is classical and not needed to state anything. Finiteness of
the zeros in a window is proved on the solution side, not assumed. Windows are T₁ < Im ρ ≤ T₂ (positive ordinates), as
in the paper. Theorem E is stated for primitive characters of modulus q > 1 (the modulus-1 case is ζ itself). The
constants appear in closed Mathlib form (`2 / 3`, `5 / 6`, `2 - 1 / cMT`, `3 / 2 - cMT⁻¹ / 2`); the decimal
expansions in the docstrings are not part of the formal statements.

## Layout of the proof development

```
Zeta23/Statement.lean  nontrivial zeros, multiplicity, the counting functions, against Mathlib's riemannZeta
Zeta23/Unconditional.lean, Zeta23/Final.lean, Zeta23/FinalMult.lean      Theorems A, B, C (ζ)
Zeta23/ThmD/           Theorem D (the optimal Montgomery–Taylor window; variational problem in ThmD/Functional.lean; multiplicity in ThmD/Mult.lean; beyond-paper union endpoint in ThmD/Union*.lean; conditional simple-line seams in ThmD/LineConditional.lean)
Zeta23/ThmE/           Theorem E (primitive Dirichlet L-functions); Zeta23/ThmDE/: Theorem D for L(s,χ)
Zeta23/LinAlg/         §3 of the paper: Sylvester inertia, rank–trace inequality (via von Neumann), Cauchy–Schwarz count, Weyl
Zeta23/WeilEF/, Zeta23/ExplicitFormula*   Weil's explicit formula (contour integration, Landau's lemma, zero-sum limits)
Zeta23/RvM/            Riemann–von Mangoldt formula (argument principle, Backlund's bound via Jensen, local zero counts)
Zeta23/GammaFacts/, Zeta23/Analytic/   Γ′/Γ estimates on vertical lines (Stirling) and other analysis
Zeta23/Chebyshev.lean, Zeta23/FromPNTPlus/     Chebyshev–Mertens estimates; files ported (with attribution headers) from PrimeNumberTheoremAnd
Zeta23/MV/             Montgomery–Vaughan generalized Hilbert inequality
Zeta23/PrimeSideA/, PrimeSideB/, Poisson.lean, Taper/   the prime side: traces of the Gram matrix (paper §§4–5)
Zeta23/ZeroSide/, Tail/                the zero side: block structure, tail bounds (paper §§2, 6)
Zeta23/Assembly/, Main.lean            assembly of the certificate (paper §6)
Zeta23/XiPrime/         zeros of ξ′: explicit formula for ξ′/ξ, coefficient system, certificates, headline theorems (XiPrime/Final.lean)
Zeta23/PairCeiling/     the bandwidth-one ceiling: definitions, stability inequality (Stability.lean), near-CUE constants, integer row certificates, the N = 256 law instance
```

Throughout the docstrings of `Zeta23/`, bracketed labels such as `[prop:PP]`, `[eq:tr2]`, `[thm:E]`, `[lem:R]` are the LaTeX labels of the corresponding statements and equations in the paper's source; they identify which step of the paper a declaration formalizes.

## Building and checking

Install [`elan`](https://github.com/leanprover/elan); the right Lean toolchain is selected automatically
from `lean-toolchain`. Budget several GiB for `.lake/` (the Mathlib cache and the Zeta23 build).

```bash
lake exe cache get        # fetch prebuilt Mathlib for the pinned commit (a few GB). If this fails (no cache
                          # for your platform / offline), just proceed: the next step builds Mathlib from
                          # source, which takes several hours of CPU time but needs nothing else.
lake build                # default targets: library Zeta23 (the headline modules), Challenge and Solution
lake build Solution.XiPrime Solution.Union Solution.LineDecimal Solution.Sextuple Solution.SextupleA1275 Solution.SextupleA1285 Solution.SextupleA1290
lake env lean scripts/PrintAxioms.lean; lake env lean scripts/PrintAxioms/XiPrime.lean   # axiom audit of the 17 + 6 theorems
for t in Union LineDecimal Sextuple SextupleA1275 SextupleA1285 SextupleA1290; do lake env lean scripts/PrintAxioms/$t.lean; done   # + 6 × 4 topic theorems
lake env lean scripts/PrintAxioms/UnionConditional.lean; lake env lean scripts/PrintAxioms/LineConditional.lean   # conditional endpoints (no trusted statement file; see AUDIT.md)
lake env lean scripts/PrintAxioms/PairCeiling.lean   # axiom audit of the ceiling theorems (no trusted statement file; see AUDIT.md)
ruby scripts/validate-formalization.rb               # formalization.yaml parses, declares Apache-2.0, has no TEMPLATE values
(cd docbuild && lake build Zeta23:docs)              # optional: doc-gen4 API documentation (docbuild/.lake/build/doc; slow — it documents Mathlib too)
```

Expected: no errors; `declaration uses 'sorry'` warnings **only** from the trusted challenge files
(`Challenge.lean`: 17, `Challenge/XiPrime.lean`: 6, and 4 in each of the six further topic files), which state each theorem with a
placeholder proof by design, and none from `Zeta23/` or any `Solution` module; and 23 + 24 lines of the
form `'two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]` (plus the conditional audits, whose
displayed hypotheses are described in AUDIT.md).
For the strongest independent check — statement equality against the trusted challenge plus kernel replay —
run Comparator as described next.

## Verifying the statements with Comparator

[Comparator](https://github.com/leanprover/comparator), the Lean FRO's trusted-verification tool, builds the *trusted*
challenge module and the *untrusted* solution module in a sandbox, exports both, checks that the solution proves
**exactly** the challenge statements (every constant they mention must coincide), that the proofs use **only** the
axioms `propext`, `Classical.choice`, `Quot.sound`, and replays the solution through the Lean kernel (and, with
`enable_nanoda`, the independent [NanoDa](https://github.com/ammkrn/nanoda_lib) kernel).

| file | role | trusted? |
|---|---|---|
| `ChallengeDeps.lean` | the counting functions (nontrivial zeros of Mathlib's `riemannZeta` / `DirichletCharacter.LFunction`, multiplicity via `analyticOrderAt`, N, N₀*, N₀ˢ, N_d) and the Theorem-D constant c₁*, **defined from Mathlib alone** — exactly the definitions the challenge statements depend on, nothing else; inlined character-for-character into `Challenge.lean` (likewise `ChallengeDeps/XiPrime.lean` into `Challenge/XiPrime.lean`), so that each challenge module imports only Mathlib and can be read on its own | yes — read it (15 definitions) |
| `Challenge.lean` | seventeen theorem statements: Theorems A–E, each at the constant stated in the paper (2/3 on-line, 2/3 simple, 5/6 distinct, the optimal-window constants 2 − 1/c₁* and (3 − 1/c₁*)/2, and the Dirichlet analogues), proofs `sorry`; imports only Mathlib (the definition layer is inlined) | yes — read it |
| `Solution.lean` | the same seventeen statements, proved by delegating to the `Zeta23` library | no (checked by Comparator) |
| `comparator.json` | Comparator configuration (theorem names, permitted axioms) — the submitted configuration | yes |
| `ChallengeDeps/XiPrime.lean`, `Challenge/XiPrime.lean`, `Solution/XiPrime.lean`, `comparator-xiprime.json` | the second topic: the counting functions for the zeros of ξ′ (defined from Mathlib alone) and six statements about them (all zeros in the open strip; Re ξ′/ξ > 0 on Re s ≥ 1; ≥ 0.85838 simple and on the line, ≥ 0.92919 distinct, and the quartic-window constants), proofs `sorry`; its solution and configuration | the challenge files, yes; the solution, no |
| `ChallengeDeps/Union.lean`, `Challenge/Union.lean`, `Solution/Union.lean`, `comparator-union.json` | topic `Union`: the two further counting functions N₀ (on-line, with multiplicity) and Nˢ (simple, anywhere) and four beyond-paper statements — exact and certified-decimal simple-or-on-line endpoints in dyadic and cumulative windows, with multiplicity-aware denominators and inclusion-exclusion union counts | yes — read the challenge and deps files |
| `Challenge/LineDecimal.lean`, `Solution/LineDecimal.lean`, `comparator-line-decimal.json` | topic `LineDecimal`: four certified-decimal Montgomery–Taylor critical-line statements (`0.672500703679`): distinct and simple on-line zeros, dyadic and cumulative | yes — read the challenge file |
| `Challenge/Sextuple.lean`, `Solution/Sextuple.lean`, `comparator-sextuple.json` | topic `Sextuple`: four sextuple-improvement statements, simple on-line zeros at `0.672755620655` (ε-form) and fixed `0.6727556`, dyadic and cumulative | yes — read the challenge file |
| `Challenge/SextupleA1275.lean`, `Solution/SextupleA1275.lean`, `comparator-sextuple-a1275.json` | topic `SextupleA1275`: the refined certificate at `A = 51/4000`, simple on-line zeros at `0.6727837118`, ε-form and fixed, dyadic and cumulative | yes — read the challenge file |
| `Challenge/SextupleA1285.lean`, `Solution/SextupleA1285.lean`, `comparator-sextuple-a1285.json` | topic `SextupleA1285`: `A = 257/20000`, `0.6727949489` | yes — read the challenge file |
| `Challenge/SextupleA1290.lean`, `Solution/SextupleA1290.lean`, `comparator-sextuple-a1290.json` | topic `SextupleA1290`: `A = 129/10000` over the 666-model catalog, `0.6728005676` | yes — read the challenge file |
| `scripts/PrintAxioms.lean`, `scripts/PrintAxioms/XiPrime.lean`, `scripts/PrintAxioms/PairCeiling.lean`, `scripts/PrintAxioms/{Union,LineDecimal,Sextuple,SextupleA1275,SextupleA1285,SextupleA1290,UnionConditional,LineConditional}.lean` | `#print axioms` for the statements — the quick check without Comparator (`PairCeiling` has no trusted statement file: its theorems carry the displayed hypothesis `EnclOK`, see above) | — |

### Quick check (no extra tooling)

```bash
lake build Solution                      # builds the Zeta23 cone the seventeen theorems need (+ Mathlib)
lake env lean scripts/PrintAxioms.lean
# every line must read:  '<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Full Comparator run

`scripts/verify-comparator.sh` is the template's pinned runner, with the pins moved to this project's toolchain: it
checks out and builds Comparator and lean4export at their `v4.33.0-rc2` tags (matching `lean-toolchain`), Landrun and
NanoDa at fixed commits, fetches the Mathlib cache, and runs Comparator through `scripts/landrun-wrapper.sh` (which
supplies Landrun's command delimiter and refuses any request to switch off part of the sandbox). It needs Linux, Git,
Go, Rust/Cargo, Python 3, `lake`, and a working Landrun (Landlock) sandbox.

```bash
./scripts/verify-comparator.sh                          # comparator.json — the submitted configuration
./scripts/verify-comparator.sh comparator-xiprime.json  # the ξ′ topic
```

The repository's CI (`.github/workflows/lean-projects.yml`) runs the same bar for every changed project through
`.github/scripts/comparator-check.sh` (every `comparator*.json`, at the registry verifier's tool pins); from this
directory, `bash ../.github/scripts/comparator-check.sh` runs it locally.

Success ends with `Your solution is okay!`. Do not rely on a run against a tree in which you have already built
`Challenge`/`Solution` yourself (Comparator README, assumption 2); a clean checkout, or deleting
`.lake/build/lib/lean/{Challenge,Solution}*`, lets Comparator build both in its sandbox. To run Comparator by hand
instead (its README has the details; any release of the same era as `lean-toolchain` works):

```bash
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator/.lake/build/bin/comparator comparator.json'
```

The three `[[lean_lib]]` stanzas at the end of `lakefile.toml` make the modules `ChallengeDeps`, `Challenge`,
`Solution` (and their `*.XiPrime` submodules) resolvable by those bare names, as Comparator expects.

### Layout convention: one topic per configuration

The base set is `Challenge.lean` / `Solution.lean` / `comparator.json` / `scripts/PrintAxioms.lean` (Theorems A–E,
each at the constant stated in the paper). Every further group of results is a **topic** `<Topic>` with its own files
`Challenge/<Topic>.lean` (`import Mathlib` only, with the definition layer inlined verbatim; statements `:= by sorry` —
trusted), `ChallengeDeps/<Topic>.lean` (only if the statements need notions beyond `ChallengeDeps.lean`; Mathlib-only
definitions, each a character-for-character copy of the corresponding Zeta23 definition — trusted),
`Solution/<Topic>.lean` (the same statements byte-for-byte, proved by delegating to Zeta23 — untrusted),
`comparator-<topic>.json` and `scripts/PrintAxioms/<Topic>.lean`. Rules for the trusted side: Mathlib only, never
`import Zeta23…`; theorem names in the root namespace, globally unique and descriptive; constants that Zeta23 carries
as definitions (`HD`, `GD`, `cStar`, window constants, …) written out in closed Mathlib form in the challenge and
bridged by a lemma on the solution side; statements in the ε-form over the counting functions of `ChallengeDeps`,
with every hypothesis of the Zeta23 theorem (e.g. `1 < q`, `χ.IsPrimitive`) as an explicit binder; a statement enters a
challenge file only when the Zeta23 theorem it delegates to is sorry-free with `#print axioms` = the standard three; a
deps module contains exactly the definitions in the dependency closure of its challenge statements. Topics in the tree (each `comparator-<topic>.json` runs independently; the trusted files to read for a topic are
`ChallengeDeps.lean`, any `ChallengeDeps/<Topic>.lean` whose content its challenge inlines, and `Challenge/<Topic>.lean`):

| topic | what | trusted deps beyond ChallengeDeps.lean |
|---|---|---|
| XiPrime | zeros of ξ′: all in the open critical strip; Re ξ′/ξ > 0 on Re s ≥ 1; ≥ 0.85838 simple and on the line, ≥ 0.92919 distinct (flat window), 0.86864 / 0.93432 (quartic window) (6) | ChallengeDeps/XiPrime.lean |
| Union | ζ: exact and certified-decimal simple-or-on-line inclusion-exclusion proportions, dyadic and cumulative (4) | ChallengeDeps/Union.lean |
| LineDecimal | ζ: certified `0.672500703679` distinct-on-line and simple-on-line proportions, dyadic and cumulative (4) | — |
| Sextuple | ζ: sextuple-kernel improvement of the simple-on-line proportion, `0.672755620655` ε-form and fixed `0.6727556`, dyadic and cumulative (4); the numerical certificate is replayed in the kernel (`decide +kernel`) | — |
| SextupleA1275 | ζ: the refined sextuple certificate at `A = 51/4000`, simple-on-line proportion `0.6727837118`, ε-form and fixed, dyadic and cumulative (4); kernel replay of an 8,953-chunk exact certificate | — |
| SextupleA1285 | ζ: the refined sextuple certificate at `A = 257/20000`, simple-on-line proportion `0.6727949489`, ε-form and fixed, dyadic and cumulative (4); kernel replay of a 30,153-chunk exact certificate | — |
| SextupleA1290 | ζ: the refined sextuple certificate at `A = 129/10000` over the 666-model catalog, simple-on-line proportion `0.6728005676`, ε-form and fixed, dyadic and cumulative (4); kernel replay of a 56,924-chunk exact certificate | — |

Only `comparator.json` is submitted to Palomar; the topic configurations are checked in the same way (`scripts/verify-comparator.sh comparator-<topic>.json`).

## Submitting to Palomar

The [Palomar](https://palomar-registry.org/) submission of this formalization is the repository
`anthropics/formal-math` at a pinned commit, with **selected project** `zeta23` (this directory; Palomar's
[CONTRIBUTING.md](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), §6.1) and
**Comparator configuration path** `zeta23/comparator.json`. The licence file is the repository-root `LICENSE`
(Apache-2.0, identical to the copy here); `zeta23/lean-toolchain` is the toolchain; the metadata is
`zeta23/formalization.yaml`, whose `project.description` is the registry abstract. Submissions go through
<https://submit.palomar-registry.org/> with the full 40-character commit SHA. The ξ′ configuration
`zeta23/comparator-xiprime.json` is not submitted.

## Provenance and attribution

Files under `Zeta23/FromPNTPlus/` are ported from the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project (Apache 2.0); each
carries a header naming the upstream file and commit, the upstream copyright and license, and the local
modifications; the upstream text (including its informal comments) is otherwise unedited. `Zeta23/LinAlg/` (the
linear-algebra core of §3: von Neumann's trace inequality for Hermitian matrices, both directions of Sylvester's law
of inertia, the rank–trace inequality and Weyl's bound) was produced first, as a self-contained development (namespace `RHLinalg`)
accompanying §3 of the paper, and is incorporated here unchanged; it has no upstream outside this project. Everything builds on [Mathlib](https://github.com/leanprover-community/mathlib4).

Authorship: **all Lean code in this repository — `Zeta23/LinAlg/` included — was written by Claude (Anthropic)**; the
paper's authors (Levent Alpöge and Ralph Furman) wrote the mathematics being formalized, directed the formalization and
reviewed its outputs, and wrote no Lean by hand; Eric Easley orchestrated the Lean work (paper Acknowledgments). `formalization.yaml` (`project.authors`,
`automation`, `review`) and `AUDIT.md` record the same account.

Released under the Apache License, Version 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
