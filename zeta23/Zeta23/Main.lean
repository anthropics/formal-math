/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Main.lean — ζ-level headline theorems: proofs.
Instantiates the abstract §6 assembly (Zeta23.Assembly, over an arbitrary ZeroConfig) at the
nontrivial zeros of Mathlib's riemannZeta (Zeta23.zetaZeros), and performs the λ → 1⁻ and
dyadic-summation wrappers. See Zeta23/Statement.lean for the definitions being talked about.
-/
import Zeta23.Statement.Seam
import Zeta23.Assembly
import Zeta23.Hypotheses.GzGp
import Zeta23.Statement.SeamClosed
import Zeta23.Defs.Profile
import Zeta23.Taper.Params
import Zeta23.Tail
import Zeta23.Tail.Package
import Zeta23.ZeroSide
import Zeta23.Poisson
import Zeta23.PrimeSideTemp
import Zeta23.ExplicitFormula.Bridge
import Zeta23.Chebyshev

open Filter Topology

noncomputable section

namespace Zeta23

section wrappers
variable (hs : ZetaSeam)

/-- N(0,T) → ∞ for ζ's zeros, from H-RvM (via N(0,T) ≥ N(T/2,T)). -/
lemma tendsto_Ncount_zero_atTop (hR : RiemannVonMangoldt (zetaZeros hs)) :
    Tendsto (fun T => (Ncount 0 T : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun T : ℝ => ((zetaZeros hs).N (T / 2) (2 * (T / 2)) : ℝ)) atTop atTop :=
    (Assembly.tendsto_N_atTop (zetaZeros hs) hR).comp (tendsto_id.atTop_div_const two_pos)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have hsplit := Assembly.N_add (zetaZeros hs) (a := 0) (b := T / 2) (c := T) (by linarith)
    (by linarith)
  have : 2 * (T / 2) = T := by ring
  rw [this]
  simp only [zetaZeros_N] at hsplit ⊢
  exact_mod_cast hsplit ▸ Nat.le_add_left _ _

/-- Generic dyadic wrapper at the ζ level: a dyadic ε-form for an interval-additive count f
against N gives the cumulative ε-form. -/
lemma cumulative_of_dyadic (hR : RiemannVonMangoldt (zetaZeros hs)) {c : ℝ} {f : ℝ → ℝ → ℕ}
    (hf_add : ∀ a b d : ℝ, a ≤ b → b ≤ d → f a d = f a b + f b d)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount T (2 * T) : ℝ) ≤ f T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount 0 T : ℝ) ≤ f 0 T := by
  refine Assembly.dyadic (f := fun a b => (f a b : ℝ)) (g := fun a b => (Ncount a b : ℝ))
    (c := c) ?_ ?_ (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (tendsto_Ncount_zero_atTop hs hR) h
  · intro a b d hab hbd
    exact_mod_cast hf_add a b d hab hbd
  · intro a b d hab hbd
    have := Assembly.N_add (zetaZeros hs) hab hbd
    simp only [zetaZeros_N] at this
    exact_mod_cast this

lemma N0star_add' (hs : ZetaSeam) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    N0star a d = N0star a b + N0star b d := by
  simpa using Assembly.N0star_add (zetaZeros hs) hab hbd

lemma N0simple_add' (hs : ZetaSeam) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    N0simple a d = N0simple a b + N0simple b d := by
  simpa using Assembly.N0s_add (zetaZeros hs) hab hbd

lemma Ndist_add' (hs : ZetaSeam) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    Ndist a d = Ndist a b + Ndist b d := by
  simpa using Assembly.Nd_add (zetaZeros hs) hab hbd

/-- λ → 1⁻ wrapper for Theorem A at the ζ level. -/
theorem thmA_of_lam
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  Assembly.eps_form_twoThirds (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0star T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _) h

/-- λ → 1⁻ wrapper for Theorem B at the ζ level. -/
theorem thmB_of_lam
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (2 * Ffun lam - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  Assembly.eps_form_half (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simple T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _) h

/-- λ → 1⁻ wrapper for Theorem C at the ζ level. -/
theorem thmC_of_lam
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Ffun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  Assembly.eps_form_threeQuarters (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (Ndist T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _) h

/-- dyadic wrapper, Theorem A. -/
theorem thmA_cumulative_of_dyadic (hR : RiemannVonMangoldt (zetaZeros hs))
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  cumulative_of_dyadic hs hR (fun _ _ _ => N0star_add' hs) h

/-- dyadic wrapper, Theorem B. -/
theorem thmB_cumulative_of_dyadic (hR : RiemannVonMangoldt (zetaZeros hs))
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic hs hR (fun _ _ _ => N0simple_add' hs) h

/-- dyadic wrapper, Theorem C. -/
theorem thmC_cumulative_of_dyadic (hR : RiemannVonMangoldt (zetaZeros hs))
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  cumulative_of_dyadic hs hR (fun _ _ _ => Ndist_add' hs) h

end wrappers

/-! ## Theorem A from PaperInputs + the thm:traces hypothesis

`thmA_of_traces` is a named declaration whose type shows exactly what is assumed: the
published inputs H : PaperInputs, a taper profile, and the thm:traces hypothesis
ThmTracesHyp (stated on the prime-side ν_X integrals). The zero-side block package and the
tail package are discharged from the sibling files. -/

section M1

open Assembly

/-- the §6 parameter choice: profile ϱ, exponent λ, ramp width w := 1. -/
def paramsOf (ϱ : ℝ → ℝ) (lam : ℝ) : Params := ⟨ϱ, lam, 1⟩

lemma paramsOf_valid {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    (paramsOf ϱ lam).Valid := ⟨hϱ, h0, h1, le_rfl⟩

/-- Discharge of the "small" eventually-hypotheses of Assembly.thmA_abstract from Taper.lean,
the H-EF bridge (GzGp.lean), Tail's boundary count and Assembly's ℰ_T → 0. -/
lemma eventually_side_conditions (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) :
    (∀ᶠ T in atTop, Z.Gz P T = P.Gp T) ∧
    (∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1) ∧
    (∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T) ∧
    Tendsto P.calE atTop (𝓝 0) := by
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
  have hLpos : ∀ᶠ T in atTop, 0 < P.L T := hLtop.eventually_gt_atTop _
  refine ⟨?_, ?_, ?_, Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)⟩
  · filter_upwards [hwL, hLpos] with T hwL hL
    refine Z.Gz_eq_Gp P T H.EF hL ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.comp (Params.phi_contDiff hP hwL)).of_le (by norm_num)
    · exact closure_minimal (Params.phi_support_subset hP) isClosed_Icc
  · filter_upwards [hwL] with T hwL
    exact ⟨(Params.one_sub_le_b hP hwL).trans (Params.b_le_a hP hwL), Params.a_le_one hP hwL⟩
  · obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
    exact Tail.eventually_NII_le Z hA₀ hloc

/-- prop:block + [eq:Ncount] eventually (ZeroSide.eventually_blockInputs_of), with its two
inputs discharged: a > 0 eventually ([eq:abdef] via Taper's half_le_a) and lem:poisson ★
(Params.hasSum_phiHatR_sq). -/
lemma eventually_blockInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) :
    ∀ᶠ T in atTop, BlockInputs Z P T := by
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T :=
    (Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop _
  refine ZeroSide.eventually_blockInputs_of Z P hP ?_ ?_
  · filter_upwards [hwL] with T hwL
    linarith [Params.half_le_a hP hwL]
  · filter_upwards [hwL] with T hwL
    exact fun γ => Params.hasSum_phiHatR_sq hP hwL γ

/-- **Theorem A at fixed λ ∈ (0,1), modulo the thm:traces hypothesis.** -/
theorem thmA_lam_of_traces (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hTr : ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨hGzGp, ha, hNII, hcalE⟩ := eventually_side_conditions zetaZeroConfig H _ hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := Tail.eventually_tailPackage zetaZeroConfig H _ hP
  have hBlock := eventually_blockInputs zetaZeroConfig _ hP
  simpa [paramsOf] using Assembly.thmA_abstract zetaZeroConfig H (paramsOf ϱ lam) hP h1 hTr hBlock
    θ₀ hTail hθ₀ hNII hGzGp ha hcalE

/-- **Theorem A (2/3, dyadic ε-form) modulo the thm:traces hypothesis.** -/
theorem thmA_of_traces (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  refine thmA_of_lam fun lam hl1 hl2 => ?_
  exact thmA_lam_of_traces H hϱ (by linarith) hl2 (hTr lam hl1 hl2)

/-- and its cumulative form (liminf N₀*(T)/N(T) ≥ 2/3), same hypotheses. -/
theorem thmA_cumulative_of_traces (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ}
    (hϱ : TaperProfile ϱ)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  thmA_cumulative_of_dyadic zetaSeam H.RvM (thmA_of_traces H hϱ hTr)

end M1

section M1BC

open Assembly

/-- Theorem B at fixed λ, modulo the thm:traces hypothesis. -/
theorem thmB_lam_of_traces (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hTr : ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨hGzGp, -, hNII, hcalE⟩ := eventually_side_conditions zetaZeroConfig H _ hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := Tail.eventually_tailPackage zetaZeroConfig H _ hP
  have hBlock := eventually_blockInputs zetaZeroConfig _ hP
  simpa [paramsOf] using Assembly.thmB_abstract zetaZeroConfig H (paramsOf ϱ lam) hP h1 hTr hBlock
    θ₀ hTail hθ₀ hNII hGzGp hcalE

/-- Theorem C at fixed λ, modulo the thm:traces hypothesis. -/
theorem thmC_lam_of_traces (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hTr : ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Ffun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨hGzGp, -, hNII, hcalE⟩ := eventually_side_conditions zetaZeroConfig H _ hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := Tail.eventually_tailPackage zetaZeroConfig H _ hP
  have hBlock := eventually_blockInputs zetaZeroConfig _ hP
  simpa [paramsOf] using Assembly.thmC_abstract zetaZeroConfig H (paramsOf ϱ lam) hP h1 hTr hBlock
    θ₀ hTail hθ₀ hNII hGzGp hcalE

variable (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig)
include H hϱ hTr

/-- Theorem B modulo thm:traces: (1/2 − ε), dyadic. -/
theorem thmB_of_traces :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  refine thmB_of_lam fun lam hl1 hl2 => ?_
  exact thmB_lam_of_traces H hϱ (by linarith) hl2 (hTr lam hl1 hl2)

/-- Theorem B modulo thm:traces, cumulative. -/
theorem thmB_cumulative_of_traces :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  thmB_cumulative_of_dyadic zetaSeam H.RvM (thmB_of_traces H hϱ hTr)

/-- Theorem C modulo thm:traces: (3/4 − ε), dyadic. -/
theorem thmC_of_traces :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  refine thmC_of_lam fun lam hl1 hl2 => ?_
  exact thmC_lam_of_traces H hϱ (by linarith) hl2 (hTr lam hl1 hl2)

/-- Theorem C modulo thm:traces, cumulative. -/
theorem thmC_cumulative_of_traces :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  thmC_cumulative_of_dyadic zetaSeam H.RvM (thmC_of_traces H hϱ hTr)

end M1BC

/-! ## Minimal trust base, displayed in the type

The literature-form explicit formula EF_lit ([eq:EFstd]) implies the paper form given
H-Γ (Zeta23.EF.explicitFormulaPaper_of_lit), and H-cheb is a theorem (Zeta23.Cheb.chebyshevMertens).
So the published inputs reduce to: EF_lit, Riemann–von Mangoldt (+ local count),
Montgomery–Vaughan, and the Γ-facts. -/

section TrustBase

/-- PaperInputs from the minimal trust base. -/
theorem PaperInputs.of_lit {Z : ZeroConfig} (hEF : EF.EF_lit Z) (hRvM : RiemannVonMangoldt Z)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVHilbert C) (hΓ : GammaFacts) : PaperInputs Z :=
  ⟨EF.explicitFormulaPaper_of_lit Z hEF hΓ, hRvM, Cheb.chebyshevMertens, hMV, hΓ⟩

open Assembly in
/-- **Theorem A, minimal-trust-base form, modulo the thm:traces hypothesis.** -/
theorem thmA_final_of_traces
    (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVHilbert C) (hΓ : GammaFacts)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA_of_traces (PaperInputs.of_lit hEF hRvM hMV hΓ) hϱ hTr

end TrustBase

section M1Std

/-- **Theorem A, hypothesis-minimal form**: with the concrete profile
ϱ := Real.smoothTransition (Zeta23.stdProfile), so the type carries only the literature trust base
(hEF, hRvM, hMV, hΓ) and the thm:traces hypothesis hTr. -/
theorem thmA_std_of_traces
    (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVHilbert C) (hΓ : GammaFacts)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ThmTracesHyp (paramsOf stdProfile lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA_of_traces (PaperInputs.of_lit hEF hRvM hMV hΓ) taperProfile_stdProfile hTr

/-- same, Theorem B. -/
theorem thmB_std_of_traces
    (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVHilbert C) (hΓ : GammaFacts)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ThmTracesHyp (paramsOf stdProfile lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  thmB_of_traces (PaperInputs.of_lit hEF hRvM hMV hΓ) taperProfile_stdProfile hTr

/-- same, Theorem C. -/
theorem thmC_std_of_traces
    (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVHilbert C) (hΓ : GammaFacts)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ThmTracesHyp (paramsOf stdProfile lam) zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  thmC_of_traces (PaperInputs.of_lit hEF hRvM hMV hΓ) taperProfile_stdProfile hTr

end M1Std

end Zeta23
