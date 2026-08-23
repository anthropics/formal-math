# Zeta23 — a Lean 4 formalization of "More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line"

> Research artifact. Not maintained and not accepting contributions.
> A Lean 4 formalization released as a static companion artifact to the paper.

Repository: <https://github.com/anthropics/zeta-23-lean>.

This repository accompanies the paper "More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line" [arXiv:2608.13637](https://arxiv.org/abs/2608.13637)).
It contains a complete, `sorry`-free Lean 4 / Mathlib formalization of Theorems A–E of that paper, including proofs
of every analytic input the argument uses (Weil's explicit formula for ζ and for primitive Dirichlet L-functions,
the Riemann–von Mangoldt zero-counting formulas, Stirling-type estimates for Γ′/Γ on vertical lines,
Chebyshev–Mertens prime-sum estimates, and the Montgomery–Vaughan generalized Hilbert inequality). Nothing is
assumed: the top-level theorems have no hypotheses, the repository declares no axioms, and `#print axioms` on each
headline theorem reports only Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`.

Toolchain: Lean `v4.33.0-rc2`, Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (Mathlib's tag `v4.33.0-rc2`; pinned in `lake-manifest.json`).

## What is proved

Write N(T₁,T₂) for the number of zeros ρ of ζ with 0 < Re ρ < 1 and T₁ < Im ρ ≤ T₂, counted with
multiplicity; N₀(T₁,T₂) for the on-line zeros counted with multiplicity; N₀*(T₁,T₂) for the number of
*distinct* on-line zeros; Nˢ for the simple zeros anywhere in the strip; N₀ˢ for those that are on the
line and *simple*; N_d for the number of distinct zeros; N(T) := N(0,T) etc.
All of these are defined directly from Mathlib's `riemannZeta` and `analyticOrderAt`
([`comparator/ChallengeDeps.lean`](comparator/ChallengeDeps.lean), 15 definitions, is the complete list
of definitions the statements depend on — nothing else). "liminf_{T→∞} X(T)/N(T) ≥ c" is formalized in the ε-form
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`. Here c₁* = √2·tan ϑ/(1+ϑ·tan ϑ), ϑ = 1/√2 (= 0.75329…) is the
Montgomery–Taylor constant of Theorem D.

| | statement (as in the paper) | Lean name (module `Solution` under [`comparator/`](comparator/)) | underlying Zeta23 theorem |
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

Also included, beyond Theorems A–E (each group has its own trusted statement file under [`comparator/`](comparator/) or, where noted, is checked with `#print axioms` only):

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

* **The zeros of ξ′** (`Zeta23/XiPrime/`, comparator topic `XiPrime`, six statements): unconditionally, at least 0.85838 of the zeros of ξ′ (the derivative of the completed zeta function) with ordinates in (T, 2T] are simple and on the critical line and at least 0.92919 are distinct (flat window; 0.86864 / 0.93432 with the quartic window), all zeros of ξ′ lie in the open critical strip, and Re ξ′/ξ > 0 on Re s ≥ 1 — `Zeta23.XiPrime.xiDeriv_simple_on_line`(`_cumulative`, `_quartic_std`) in `Zeta23/XiPrime/Final.lean`. The argument is the one of Theorem B with ξ′ in place of ζ (the rank–trace device applied to the Farmer–Gonek(–Lee)/Montgomery argument for ξ′; Farmer–Gonek, arXiv:0803.0425 = Farmer–Gonek–Lee, J. London Math. Soc. (2) 90 (2014)). In the docstrings under `Zeta23/XiPrime/`, labels of the form `[XF′ Lemma 6.1]`, `[XF′ Thm 8.2]`, `[XF′ (Z3)]` refer to the authors' technical supplement on the explicit formula for ξ′/ξ and the two-trace transfer, which is not included in this repository; these labels record provenance only — what is relied upon is in each case the Lean statement that the docstring introduces. (The counting functions in `comparator/ChallengeDeps/XiPrime.lean` are finite sums / cardinalities over the set of zeros of ξ′ in a height window; that set is finite because every zero of ξ′ lies in the open critical strip — the first of the six statements — and the zeros of an entire function are isolated.)

* **The bandwidth-one ceiling** (`Zeta23/PairCeiling/`, no comparator topic; `#print axioms` audit below): the stability inequality behind the paper's remark on the optimality of the method — for every certificate (c₀, r) of the type used in Theorem B (r ∈ C¹[0,1], r′ differentiable off a countable set with integrable derivative) that is valid against a configuration whose form-factor measure has grid masses s_j and simple-point fraction p, one has c₀ + ∫₀¹ r(x)·x dx ≤ p + |r(1)|·|D(1)| + |r′(1)|·|E(1)| + (sup|E|)·∫₀¹|r″| (`Zeta23.PairCeiling.ceiling_stability`, `Zeta23/PairCeiling/Stability.lean`, two integrations by parts) — and its instance at an explicit 256-periodic law (`Zeta23.PairCeiling.ceiling_law256`, `ceiling_law256_decimal`, `ceiling_nearCUE_signed`, `ceiling_law256_signed`; files `NearCUE.lean`, `RowCert.lean`, `LawN256.lean`, `CeilingLaw256.lean`, `Signed.lean`): every bandwidth-one certificate certifies a proportion of simple zeros at most 0.6818287 + 2.55·10⁻⁶·(|r′(1)| + ∫|r″|). The ONE displayed hypothesis of these theorems is `EnclOK`: that the law's form factor S(j), j = 1…256, lies in the 256 integer enclosures recorded in `LawN256.lean` (obtained outside Lean by interval arithmetic from an exact-rational certificate, sha256 `cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`, available from the authors); everything downstream of the enclosures — the 255 near-CUE row inequalities |256·S(j) − j| ≤ 3·10⁻⁴⁰ (0 < j < 256), the edge bound |D(1)| ≤ 0.82395317, the sign of the edge term — is checked in the kernel by `decide` (`LawN256_check`, `LawN256_edge`), and the analytic inequality is proved in Lean.

How the comparator configuration covers this: [`comparator/config.json`](comparator/config.json) (seventeen statements,
[`comparator/Challenge.lean`](comparator/Challenge.lean)) contains Theorems A–E exactly as in the table above, each at
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

## Layout

```
comparator/          trusted statements (ChallengeDeps, Challenge), untrusted Solution, comparator config — START HERE
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
from `lean-toolchain`.

```bash
lake exe cache get        # fetch prebuilt Mathlib for the pinned commit (a few GB). If this fails (no cache
                          # for your platform / offline), just proceed: the next step builds Mathlib from
                          # source, which takes several hours of CPU time but needs nothing else.
lake build                # builds library Zeta23 (the default target imports exactly the headline modules)
lake build Solution Solution.XiPrime Solution.Union Solution.LineDecimal Solution.Sextuple
lake env lean comparator/PrintAxioms.lean; lake env lean comparator/PrintAxioms/XiPrime.lean; lake env lean comparator/PrintAxioms/Union.lean; lake env lean comparator/PrintAxioms/LineDecimal.lean; lake env lean comparator/PrintAxioms/Sextuple.lean   # axiom audit of the 17 + 6 + 4 + 4 + 4 unconditional theorems
lake env lean comparator/PrintAxioms/UnionConditional.lean
lake env lean comparator/PrintAxioms/LineConditional.lean
lake env lean comparator/PrintAxioms/PairCeiling.lean   # axiom audit of the ceiling theorems (no trusted statement file; see AUDIT.md)
```

Expected: no errors, no `sorry` warnings from `Zeta23/` or `Solution` (the only `sorry`s in the repository
are the deliberate ones in the trusted challenge files under `comparator/`), and the 35 trusted unconditional declarations
(17 + 6 + 4 + 4 + 4), the eleven `LineConditional` audit declarations, the four conditional union endpoints, and the
conditional numerical enclosure report only `[propext, Classical.choice, Quot.sound]`.
For the strongest independent check — statement equality against the trusted challenge plus kernel replay —
run comparator as described in [`comparator/README.md`](comparator/README.md).


## Provenance and attribution

Files under `Zeta23/FromPNTPlus/` are ported from the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project (Apache 2.0); each
carries a header naming the upstream file and commit, the upstream copyright and license, and the local
modifications; the upstream text (including its informal comments) is otherwise unedited. `Zeta23/LinAlg/` (the
linear-algebra core of §3: von Neumann's trace inequality for Hermitian matrices, both directions of Sylvester's law
of inertia, the rank–trace inequality and Weyl's bound) was written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the
paper, by the paper's authors, and is incorporated here unchanged; it has no upstream outside this project. Everything builds on [Mathlib](https://github.com/leanprover-community/mathlib4).

Released under the Apache License, Version 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
