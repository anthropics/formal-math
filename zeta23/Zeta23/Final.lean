/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Final.lean — the headline theorems.

  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line",
   Theorems A, B, C — ε-forms.

Each theorem's TYPE in the first section displays the inputs as separate named hypotheses:
  hEF  : EF.EF_lit zetaZeroConfig        — Weil's explicit formula, literature form [eq:EFstd]
                                           ([IK04, Thm 5.12] for ζ), over ζ's nontrivial zeros;
  hRvM : RiemannVonMangoldt zetaZeroConfig — [eq:RvM] + local count N(t+1)−N(t) ≤ A₀ log(|t|+3);
  hMV  : ∃ C > 0, MVDiag C                — Montgomery–Vaughan weighted Hilbert inequality, literature
                                           (y = x) form [MV74, Thm 2]; the paper's bilinear [lem:MV] is
                                           derived (Zeta23.MVHilbert_of_diag);
  hΓ   : GammaFacts                        — Stirling-type facts for μ [eq:mufacts], [eq:muints].
Nothing else: the Chebyshev–Mertens bounds [lem:cheb] are proved (Zeta23.Cheb.chebyshevMertens), the
paper's spectral form of the explicit formula [eq:EF] is derived from hEF (Zeta23.EF), the taper profile
is Mathlib's Real.smoothTransition (Zeta23.stdProfile), the ζ-facts (analytic order, functional-equation
symmetry, local finiteness) are proved (Zeta23.zetaSeam), and thm:traces [thm:traces] is
Zeta23.PrimeSide.thm_traces (the versions with thm:traces as an explicit hypothesis are
Zeta23.thmA_of_traces etc. in Zeta23/Main.lean). Later sections discharge the hypotheses
hMV, hΓ, hRvM and hEF one by one, ending with the unconditional forms.

Counting functions (Zeta23/Statement.lean): Ncount T₁ T₂ = N(T₁,T₂) with multiplicity (analytic order of
riemannZeta), N0star = N₀* (on the line, distinct), N0simple = N₀ˢ (on the line, simple), Ndist = N_d
(distinct), all over nontrivial zeros ρ (ζ ρ = 0, 0 < Re ρ < 1) with T₁ < Im ρ ≤ T₂.
-/
import Zeta23.Main
import Zeta23.Defs.Profile
import Zeta23.PrimeSideB.Final
import Zeta23.MV
import Zeta23.MV.Final
import Zeta23.GammaFacts.Complete
import Zeta23.RvM.Statement
import Zeta23.WeilEF.Main

open Filter

noncomputable section

namespace Zeta23

section Final

/-- PaperInputs from the literature trust base: literature EF, RvM, MV74 in diagonal form, Γ-facts. -/
theorem PaperInputs.of_literature {Z : ZeroConfig} (hEF : EF.EF_lit Z) (hRvM : RiemannVonMangoldt Z)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVDiag C) (hΓ : GammaFacts) : PaperInputs Z :=
  PaperInputs.of_lit hEF hRvM (exists_MVHilbert_of_diag hMV) hΓ

variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
  (hMV : ∃ C : ℝ, 0 < C ∧ MVDiag C) (hΓ : GammaFacts)
include hEF hRvM hMV hΓ

omit hEF hRvM hMV hΓ in
private lemma tracesStd (H : PaperInputs zetaZeroConfig) :
    ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf stdProfile lam) zetaZeroConfig :=
  fun _ h1 h2 => PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

/-- **Theorem A** [thm:A]: "liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3" — for every ε > 0 and all large T,
at least (2/3 − ε) of the nontrivial zeros of ζ with T < Im ρ ≤ 2T, counted with multiplicity, are
accounted for by DISTINCT zeros on the critical line:  (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T). -/
theorem thmA :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmA_of_traces H taperProfile_stdProfile (tracesStd H)

/-- **Theorem A** [thm:A], cumulative: "liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3", N(T) := N(0,T). -/
theorem thmA_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmA_cumulative_of_traces H taperProfile_stdProfile (tracesStd H)

/-- **Theorem A at fixed λ ∈ (0,1)** [thm:A]: N₀*(T,2T) ≥ (H(λ) − ε) N(T,2T), H(λ) = 2 − 1/λ − λ/3
(the paper's c(λ)·loglogT/logT absorbed into ε). -/
theorem thmA_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmA_lam_of_traces H taperProfile_stdProfile h0 h1
    (PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile h0 h1.le) H)

/-- **Theorem B** [thm:B]: "at least half of the zeros are simple and on the critical line":
(1/2 − ε)·N(T,2T) ≤ N₀ˢ(T,2T) for T ≥ T₀(ε). -/
theorem thmB :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmB_of_traces H taperProfile_stdProfile (tracesStd H)

/-- **Theorem B** [thm:B], cumulative: "liminf_{T→∞} N₀ˢ(T)/N(T) ≥ 1/2". -/
theorem thmB_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmB_cumulative_of_traces H taperProfile_stdProfile (tracesStd H)

/-- **Theorem B at fixed λ** [thm:B]: N₀ˢ(T,2T) ≥ (2F(λ) − 1 − ε) N(T,2T), F(λ) = λ/(1+λ²/3). -/
theorem thmB_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmB_lam_of_traces H taperProfile_stdProfile h0 h1
    (PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile h0 h1.le) H)

/-- **Theorem C** [thm:C]: "liminf N_d(T)/N(T) ≥ 3/4" — distinct zeros: (3/4 − ε)·N(T,2T) ≤ N_d(T,2T). -/
theorem thmC :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmC_of_traces H taperProfile_stdProfile (tracesStd H)

/-- **Theorem C** [thm:C], cumulative: "liminf_{T→∞} N_d(T)/N(T) ≥ 3/4". -/
theorem thmC_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmC_cumulative_of_traces H taperProfile_stdProfile (tracesStd H)

/-- **Theorem C at fixed λ** [thm:C]: N_d(T,2T) ≥ (F(λ) − ε) N(T,2T). -/
theorem thmC_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Ffun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  let H := PaperInputs.of_literature hEF hRvM hMV hΓ
  thmC_lam_of_traces H taperProfile_stdProfile h0 h1
    (PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile h0 h1.le) H)

end Final

/-! ## Three-hypothesis forms: H-MV is a theorem (Zeta23.MV.mv_hilbert — the weighted Hilbert
inequality of Montgomery–Vaughan 1974, proved outright). -/

section ThreeHyp

/-- PaperInputs from (literature EF, RvM, Γ-facts) only: cheb and MV are theorems. -/
theorem PaperInputs.of_three {Z : ZeroConfig} (hEF : EF.EF_lit Z) (hRvM : RiemannVonMangoldt Z)
    (hΓ : GammaFacts) : PaperInputs Z :=
  PaperInputs.of_lit hEF hRvM MV.mv_hilbert hΓ

variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig) (hΓ : GammaFacts)
include hEF hRvM hΓ

/-- **Theorem A**, three hypotheses (EF_lit, RvM, Γ): (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T). -/
theorem thmA₃ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmA_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

/-- **Theorem A** cumulative, three hypotheses. -/
theorem thmA₃_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmA_cumulative_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

/-- **Theorem B**, three hypotheses: (1/2 − ε)·N(T,2T) ≤ N₀ˢ(T,2T). -/
theorem thmB₃ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmB_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

/-- **Theorem B** cumulative, three hypotheses. -/
theorem thmB₃_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmB_cumulative_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

/-- **Theorem C**, three hypotheses: (3/4 − ε)·N(T,2T) ≤ N_d(T,2T). -/
theorem thmC₃ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmC_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

/-- **Theorem C** cumulative, three hypotheses. -/
theorem thmC₃_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmC_cumulative_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

end ThreeHyp

/-! ## Two-hypothesis forms: H-Γ is a theorem (Zeta23.gammaFacts; proved via
digamma partial fractions + vertical Stirling + FTC). -/

section TwoHyp

/-- PaperInputs from (literature EF, RvM) only: cheb, MV and Γ are theorems. -/
theorem PaperInputs.of_two {Z : ZeroConfig} (hEF : EF.EF_lit Z) (hRvM : RiemannVonMangoldt Z) :
    PaperInputs Z :=
  PaperInputs.of_three hEF hRvM gammaFacts

variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
include hEF hRvM

/-- **Theorem A**, two hypotheses (EF_lit, RvM): (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T). -/
theorem thmA₂ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA₃ hEF hRvM gammaFacts

/-- **Theorem A** cumulative, two hypotheses. -/
theorem thmA₂_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  thmA₃_cumulative hEF hRvM gammaFacts

/-- **Theorem B**, two hypotheses: (1/2 − ε)·N(T,2T) ≤ N₀ˢ(T,2T). -/
theorem thmB₂ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  thmB₃ hEF hRvM gammaFacts

/-- **Theorem C**, two hypotheses: (3/4 − ε)·N(T,2T) ≤ N_d(T,2T). -/
theorem thmC₂ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  thmC₃ hEF hRvM gammaFacts

/-- **Theorem B** cumulative, two hypotheses. -/
theorem thmB₂_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  thmB₃_cumulative hEF hRvM gammaFacts

/-- **Theorem C** cumulative, two hypotheses. -/
theorem thmC₂_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  thmC₃_cumulative hEF hRvM gammaFacts

end TwoHyp

/-! ## One-hypothesis forms: H-RvM is a theorem given the proved Γ-facts
(local count + folded argument principle + Backlund; Zeta23/RvM/*). -/

section OneHyp

/-- **H-RvM for ζ, unconditionally** (from the RvM development and the proved Γ-facts). -/
theorem riemannVonMangoldt_zeta : RiemannVonMangoldt zetaZeroConfig :=
  RvM.riemannVonMangoldt gammaFacts

/-- PaperInputs from the literature explicit formula ALONE. -/
theorem PaperInputs.of_EF (hEF : EF.EF_lit zetaZeroConfig) : PaperInputs zetaZeroConfig :=
  PaperInputs.of_two hEF riemannVonMangoldt_zeta

variable (hEF : EF.EF_lit zetaZeroConfig)
include hEF

/-- **Theorem A** [thm:A], single hypothesis — Weil's explicit formula for ζ in literature form
[eq:EFstd] is the ONLY assumption: for every ε > 0 and all large T, at least (2/3 − ε) of the
nontrivial zeros of ζ in (T, 2T], counted with multiplicity, are matched by distinct zeros ON the
critical line:  (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T). -/
theorem thmA₁ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA₂ hEF riemannVonMangoldt_zeta

/-- **Theorem A** cumulative, single hypothesis: liminf N₀*(T)/N(T) ≥ 2/3. -/
theorem thmA₁_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  thmA₂_cumulative hEF riemannVonMangoldt_zeta

/-- **Theorem B** [thm:B], single hypothesis: (1/2 − ε)·N(T,2T) ≤ N₀ˢ(T,2T) (simple AND on-line). -/
theorem thmB₁ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  thmB₂ hEF riemannVonMangoldt_zeta

/-- **Theorem B** cumulative, single hypothesis. -/
theorem thmB₁_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  thmB₂_cumulative hEF riemannVonMangoldt_zeta

/-- **Theorem C** [thm:C], single hypothesis: (3/4 − ε)·N(T,2T) ≤ N_d(T,2T) (distinct zeros). -/
theorem thmC₁ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  thmC₂ hEF riemannVonMangoldt_zeta

/-- **Theorem C** cumulative, single hypothesis. -/
theorem thmC₁_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  thmC₂_cumulative hEF riemannVonMangoldt_zeta

end OneHyp

/-! ## Unconditional forms: the explicit formula is a theorem
(Zeta23.WeilEF.EF_lit_zetaZeroConfig — Weil/Riemann–von Mangoldt explicit formula for ζ,
literature form [eq:EFstd], proved from Mathlib's functional equation by contour integration).
These are the headline statements of the formalization: no hypotheses at all. -/

section Unconditional

/-- **Weil's explicit formula for ζ**, re-exported. -/
theorem zetaEF : EF.EF_lit zetaZeroConfig := WeilEF.EF_lit_zetaZeroConfig

/-- The paper's full input package, unconditionally. -/
theorem paperInputs_zeta : PaperInputs zetaZeroConfig := PaperInputs.of_EF zetaEF

/-- **Theorem A** [thm:A], UNCONDITIONAL: for every ε > 0, for all large T, at least (2/3 − ε) of the
nontrivial zeros of Mathlib's riemannZeta with T < Im ρ ≤ 2T, counted with multiplicity, are matched
by distinct zeros on the critical line:  (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T). -/
theorem thmA₀ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA₁ zetaEF

/-- **Theorem A**, cumulative, UNCONDITIONAL: liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3. -/
theorem thmA₀_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  thmA₁_cumulative zetaEF

/-- **Theorem B** [thm:B], UNCONDITIONAL: at least (1/2 − ε) of the zeros are simple AND on the line. -/
theorem thmB₀ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  thmB₁ zetaEF

/-- **Theorem B**, cumulative, UNCONDITIONAL. -/
theorem thmB₀_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  thmB₁_cumulative zetaEF

/-- **Theorem C** [thm:C], UNCONDITIONAL: at least (3/4 − ε) of the zeros are distinct. -/
theorem thmC₀ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  thmC₁ zetaEF

/-- **Theorem C**, cumulative, UNCONDITIONAL. -/
theorem thmC₀_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  thmC₁_cumulative zetaEF

end Unconditional

section AFortiori

/-- a fortiori (paper [thm:A]: "and a fortiori N₀(T) ≥ (2/3 − o(1))N(T)"): the WITH-multiplicity
on-line count also carries the 2/3 proportion. From thmA₃ and N₀* ≤ N₀ ([eq:trivialchain]). -/
theorem thmA₃_N0 (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
    (hΓ : GammaFacts) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := thmA₃ hEF hRvM hΓ ε hε
  refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
  exact_mod_cast (trivial_chain₀ T (2 * T)).2.1

/-- a fortiori (paper [thm:B]: "consequently also Nˢ(T) ≥ (1/2 − o(1))N(T)"): simple zeros
anywhere in the strip. From thmB₃ and N₀ˢ ≤ Nˢ ([eq:trivialchain]). -/
theorem thmB₃_Nsimple (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
    (hΓ : GammaFacts) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := thmB₃ hEF hRvM hΓ ε hε
  refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
  have h := trivial_chain₀ T (2 * T)
  have : N0simple T (2 * T) ≤ Nsimple T (2 * T) := h.2.2.2.1
  exact_mod_cast this

end AFortiori

section UnconditionalAFortiori

/-- a fortiori: the on-line count WITH multiplicity. -/
theorem thmA₀_N0 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) :=
  thmA₃_N0 zetaEF riemannVonMangoldt_zeta gammaFacts

/-- a fortiori: simple zeros anywhere in the strip. -/
theorem thmB₀_Nsimple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  thmB₃_Nsimple zetaEF riemannVonMangoldt_zeta gammaFacts

end UnconditionalAFortiori

/-- Same as thmA but from the bundled paper-form inputs (PaperInputs) rather than the literature
trust base. -/
theorem thmA_ofInputs (H : PaperInputs zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H

end Zeta23
