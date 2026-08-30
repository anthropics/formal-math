/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/LitCorr.lean — (EF2) archimedean line + the "literature form with correction" layer of the
ξ′ / W explicit formulas.

§A (archimedean, 1 < c ≤ 3/2):  (1/2π)∫[H(c+it)+H(1−c−it)]·L(c+it)dt = H(0)+H(1) + (1/2π)∫h·[Re ψ(¼+ir/2) − log π]
   (Γℝ piece: WeilEF.gamma_line_shift/gammaR_bracket; rational piece: FullLine.rational_line_inst).
§B (generic line Re s = c): HwC c k t := H(c+it)+H(1−c−it), its decay/continuity/integrability against bounded g, and
   the ζ-case evaluation  Efn_line_identity : (1/2π)∫ HwC·E = literatureRHS k  (E = L + ζ′/ζ; = the
   EF_lit_zeta right-hand side [eq:EFstd] at any 1 < c ≤ 3/2).
§C (ξ′ at c = 5/4): the input Props FullLineIdentity / RationalLine, dEE, Hw := HwC (5/4), Jcorr, and
   xiPrime_EF_lit_corr :  Σ'_{ρ₁} m_{ρ₁} h_k(γ_{ρ₁}) = literatureRHS k + Jcorr k  [ξ″/ξ′ = E + E′/E, Expansion].
-/
import Zeta23.XiPrime.ExplicitFormula.FullLine
import Zeta23.XiPrime.ExplicitFormula.DirichletLine

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn Hfn_mirror gamma_line_shift gammaR_bracket prime_side_line norm_Hfn_le continuous_Hfn_line
  integrable_Hfn_mul_logDeriv_zeta integrable_Hfn_mul_logDeriv_Gammaℝ)

/-! ## §A. The archimedean line -/


open Complex MeasureTheory Filter Topology
open Zeta23.WeilEF (Hfn Hfn_mirror gamma_line_shift gammaR_bracket norm_Hfn_le
  continuous_Hfn_line integrable_Hfn_mul_logDeriv_Gammaℝ)

/-- L splits as Γℝ′/Γℝ + (1/s + 1/(s−1)) (definition). -/
theorem Lfn_eq (s : ℂ) : Lfn s = logDeriv Complex.Gammaℝ s + (1 / s + 1 / (s - 1)) := by
  unfold Lfn; ring

/-- 1/s + 1/(s−1) is the logarithmic derivative of s(s−1), off {0,1}. -/
theorem logDeriv_mul_sub_one {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv (fun w : ℂ => w * (w - 1)) s = 1 / s + 1 / (s - 1) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s h0 h1'
    differentiableAt_id (differentiableAt_id.sub_const 1)]
  have e1 : logDeriv (fun w : ℂ => w) s = 1 / s := by
    rw [logDeriv_apply]; simp
  have e2 : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    simp
  rw [e1, e2]

/-- **Γℝ piece** (WeilEF.gamma_line_shift + gammaR_bracket):
(1/2π)∫[H(c+it)+H(1−c−it)]·Γℝ′/Γℝ(c+it) dt = (1/2π)∫ h_k(r)·gammaBracket(r) dr. -/
theorem gamma_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I))
      = (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
  congr 1
  rw [gamma_line_shift hk hkc hc1 hc2]
  congr 1
  funext t
  rw [gammaR_bracket t]
  congr 2
  unfold Zeta23.EF.gammaBracket
  congr 3
  ring

/-- **rational piece**: (1/2π)∫[H(c+it)+H(1−c−it)]·(1/(c+it) + 1/(c+it−1)) dt = H(0) + H(1)
— the f = s(s−1) instance of the generic full-line identity (FullLine.rational_line_inst). -/
theorem rational_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1))) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1)))
      = Hfn k 0 + Hfn k 1 :=
  rational_line_inst hk hkc hc1 hc2

/-- integrability of the Γℝ piece with the two-sided weight. -/
theorem integrable_weight_mul_logDeriv_Gammaℝ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)) := by
  have hkneg2 : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have hknegc : HasCompactSupport (fun u : ℝ => k (-u)) := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have h1 : Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I)
      * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)) :=
    integrable_Hfn_mul_logDeriv_Gammaℝ hk hkc (σ := c) (by linarith) hc2
  have h2 : Integrable (fun t : ℝ => Hfn k (1 - c - t * I)
      * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)) := by
    have heq : (fun t : ℝ => Hfn k (1 - c - t * I) * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I))
        = fun t : ℝ => Hfn (fun u => k (-u)) ((c : ℂ) + t * I)
          * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) := by
      funext t; rw [Hfn_mirror k c t]
    rw [heq]
    exact integrable_Hfn_mul_logDeriv_Gammaℝ hkneg2 hknegc (σ := c) (by linarith) hc2
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

/-- **(EF2)**: the archimedean line identity. -/
theorem archimedean_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * Lfn ((c : ℂ) + t * I))
      = Hfn k 0 + Hfn k 1
        + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
  obtain ⟨hRint, hR⟩ := rational_line hk hkc hc1 hc2
  have hΓint := integrable_weight_mul_logDeriv_Gammaℝ hk hkc hc1 hc2
  have hsplit : (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * Lfn ((c : ℂ) + t * I))
      = (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
          * logDeriv Complex.Gammaℝ ((c : ℂ) + t * I))
        + ∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
          * (1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1)) := by
    rw [← integral_add hΓint hRint]
    congr 1
    funext t
    rw [Lfn_eq]
    ring
  rw [hsplit, mul_add, gamma_line hk hkc hc1 hc2, hR]
  ring


/-! ## §B. The generic line Re s = c: two-sided weight and the ζ-case evaluation -/

/-- the two-sided test weight on the line c: H(c+it) + H(1−c−it). -/
def HwC (c : ℝ) (k : ℝ → ℂ) (t : ℝ) : ℂ := Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I)

/-! ## weight facts on the line -/

theorem norm_HwC_le {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖HwC c k t‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  refine ⟨2 * C, by positivity, fun t => ?_⟩
  have h1 := hC c t (by linarith) (by linarith)
  have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
  have e2 : (((1 - c : ℝ) : ℂ) + ((-t:ℝ):ℂ) * I) = 1 - (c:ℂ) - t * I := by push_cast; ring
  rw [e2] at h2
  have e3 : (1:ℝ) + (-t) ^ 2 = 1 + t ^ 2 := by ring
  rw [e3] at h2
  calc ‖HwC c k t‖ ≤ ‖Hfn k ((c:ℂ) + t * I)‖ + ‖Hfn k (1 - c - t * I)‖ := norm_add_le _ _
    _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add h1 h2
    _ = 2 * C / (1 + t ^ 2) := by ring

theorem continuous_HwC {c : ℝ} {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Continuous (HwC c k) := by
  have h1 := continuous_Hfn_line hk hkc c
  have h2 := continuous_Hfn_line hk hkc (1 - c)
  have h2' : Continuous (fun t : ℝ => Hfn k (1 - (c:ℂ) - t * I)) := by
    have : (fun t : ℝ => Hfn k (1 - (c:ℂ) - t * I))
        = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [Function.comp]; congr 1; push_cast; ring
    rw [this]; exact h2.comp continuous_neg
  exact h1.add h2'

theorem integrable_HwC_mul_bdd {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {g : ℝ → ℂ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, ‖g t‖ ≤ M) :
    Integrable (fun t : ℝ => HwC c k t * g t) := by
  obtain ⟨C, hC0, hC⟩ := norm_HwC_le hc1 hc2 hk hkc
  have hdom : Integrable (fun t : ℝ => C / (1 + t ^ 2) * M) := by
    have := (integrable_inv_one_add_sq.const_mul C).mul_const M
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [div_eq_mul_inv]
  refine hdom.mono' ((continuous_HwC hk hkc).mul hg).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC t) (hM t) (norm_nonneg _) (by positivity)

/-! ## the ζ evaluation at general c:  (1/2π)∫[H+H̃]·E = literatureRHS k -/

theorem Efn_line_identity {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    Integrable (fun t : ℝ => HwC c k t * Efn ((c:ℂ) + t * I)) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * Efn ((c:ℂ) + t * I)) = Zeta23.EF.literatureRHS k := by
  have hkneg2 : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have hknegc : HasCompactSupport (fun u : ℝ => k (-u)) := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have hH2eq : ∀ t : ℝ, Hfn k (1 - c - t * I) = Hfn (fun u => k (-u)) ((c:ℂ) + t * I) :=
    fun t => Hfn_mirror k c t
  -- integrable pieces
  have hint1 := integrable_Hfn_mul_logDeriv_zeta hk hkc hc1 hc2
  have hint2 : Integrable (fun t : ℝ => Hfn k (1 - c - t * I) * logDeriv riemannZeta ((c:ℂ) + t * I)) := by
    have heq : (fun t : ℝ => Hfn k (1 - c - t * I) * logDeriv riemannZeta ((c:ℂ) + t * I))
        = fun t : ℝ => Hfn (fun u => k (-u)) ((c:ℂ) + t * I) * logDeriv riemannZeta ((c:ℂ) + t * I) := by
      funext t; rw [hH2eq t]
    rw [heq]; exact integrable_Hfn_mul_logDeriv_zeta hkneg2 hknegc hc1 hc2
  have hintζ : Integrable (fun t : ℝ => HwC c k t * logDeriv riemannZeta ((c:ℂ) + t * I)) := by
    refine (hint1.add hint2).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, HwC]; ring
  have hintΓ : Integrable (fun t : ℝ => HwC c k t * logDeriv Complex.Gammaℝ ((c:ℂ) + t * I)) :=
    integrable_weight_mul_logDeriv_Gammaℝ hk hkc hc1 hc2
  obtain ⟨hintR0, hR⟩ := rational_line hk hkc hc1 hc2
  have hintR : Integrable (fun t : ℝ => HwC c k t * (1 / ((c:ℂ) + t * I) + 1 / ((c:ℂ) + t * I - 1))) := hintR0
  have hintL : Integrable (fun t : ℝ => HwC c k t * Lfn ((c:ℂ) + t * I)) := by
    refine (hintΓ.add hintR).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Lfn]; ring
  have hintE : Integrable (fun t : ℝ => HwC c k t * Efn ((c:ℂ) + t * I)) := by
    refine (hintL.add hintζ).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Efn]; ring
  refine ⟨hintE, ?_⟩
  -- evaluations
  have hArch : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * Lfn ((c:ℂ) + t * I))
      = Hfn k 0 + Hfn k 1 + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) :=
    archimedean_line hk hkc hc1 hc2
  have hζ1 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * logDeriv riemannZeta ((c:ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
    have h := prime_side_line hk hkc hc1
    have h2 : (∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * (-logDeriv riemannZeta ((c:ℂ) + t * I)))
        = -∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * logDeriv riemannZeta ((c:ℂ) + t * I) := by
      rw [← integral_neg]; congr 1; funext t; ring
    rw [h2] at h
    linear_combination -h
  have hζ2 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (1 - c - t * I) * logDeriv riemannZeta ((c:ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n) := by
    have h := prime_side_line hkneg2 hknegc hc1
    have h2 : (∫ t : ℝ, Hfn (fun u => k (-u)) ((c:ℂ) + t * I) * (-logDeriv riemannZeta ((c:ℂ) + t * I)))
        = -∫ t : ℝ, Hfn k (1 - c - t * I) * logDeriv riemannZeta ((c:ℂ) + t * I) := by
      rw [← integral_neg]; congr 1; funext t; rw [hH2eq t]; ring
    rw [h2] at h
    have h3 : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (fun u => k (-u)) (Real.log n))
        = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n) := rfl
    rw [h3] at h
    linear_combination -h
  have hζ : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, HwC c k t * logDeriv riemannZeta ((c:ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    have hsum2 : (∫ t : ℝ, HwC c k t * logDeriv riemannZeta ((c:ℂ) + t * I))
        = (∫ t : ℝ, Hfn k ((c:ℂ) + t * I) * logDeriv riemannZeta ((c:ℂ) + t * I))
          + ∫ t : ℝ, Hfn k (1 - c - t * I) * logDeriv riemannZeta ((c:ℂ) + t * I) := by
      rw [← integral_add hint1 hint2]; congr 1; funext t; simp only [HwC]; ring
    obtain ⟨B₁, hB₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
    have hsummable_gen : ∀ (g : ℝ → ℂ), (∀ u, g u ≠ 0 → |u| ≤ max B₁ 0) →
        Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n)) := by
      intro g hg
      refine summable_of_hasFiniteSupport ?_
      have hsub : Function.support (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n))
          ⊆ Set.Iic ⌈Real.exp (max B₁ 0)⌉₊ := by
        intro n hn
        rw [Function.mem_support] at hn
        have hgne : g (Real.log n) ≠ 0 := by
          intro h; rw [h, mul_zero] at hn; exact hn rfl
        have hlog := hg _ hgne
        have hn0 : n ≠ 0 := by rintro rfl; simp at hn
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        have : (n:ℝ) ≤ Real.exp (max B₁ 0) := by
          have h2 : Real.log n ≤ max B₁ 0 := (le_abs_self _).trans hlog
          calc (n:ℝ) = Real.exp (Real.log n) := (Real.exp_log (by linarith)).symm
            _ ≤ Real.exp (max B₁ 0) := Real.exp_le_exp.mpr h2
        rw [Set.mem_Iic]
        exact_mod_cast this.trans (Nat.le_ceil _)
      exact (Set.finite_Iic _).subset hsub
    have hsummable1 := hsummable_gen k (fun u hu => (hB₁ u hu).trans (le_max_left _ _))
    have hsummable2 : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n)) := by
      refine hsummable_gen (fun u => k (-u)) (fun u hu => ?_)
      have h2 := hB₁ (-u) hu
      rw [abs_neg] at h2
      exact h2.trans (le_max_left _ _)
    rw [hsum2, mul_add, hζ1, hζ2, ← neg_add, ← Summable.tsum_add hsummable1 hsummable2]
    congr 1
    exact tsum_congr fun n => by ring
  have hpole0 : Hfn k 0 = paperFT k (I / 2) := by
    unfold Hfn; congr 1
    rw [div_eq_iff Complex.I_ne_zero, div_mul_eq_mul_div, Complex.I_mul_I]; norm_num
  have hpole1 : Hfn k 1 = paperFT k (-I / 2) := by
    unfold Hfn; congr 1
    rw [div_eq_iff Complex.I_ne_zero]
    rw [show (-I / 2) * I = -(I * I) / 2 by ring, Complex.I_mul_I]; norm_num
  have hsplit : (∫ t : ℝ, HwC c k t * Efn ((c:ℂ) + t * I))
      = (∫ t : ℝ, HwC c k t * Lfn ((c:ℂ) + t * I)) + ∫ t : ℝ, HwC c k t * logDeriv riemannZeta ((c:ℂ) + t * I) := by
    rw [← integral_add hintL hintζ]; congr 1; funext t; simp only [Efn]; ring
  rw [hsplit, mul_add, hArch, hζ, Zeta23.EF.literatureRHS, hpole0, hpole1]
  ring

/-! ## §C. ξ′ at c = 5/4: input Props, the correction functional J, literature form with correction -/

/-! ## Input propositions (discharged elsewhere) -/

/-- (EF1) on the line c = 5/4, as a Prop (proved in `Main.full_line_identity`). -/
def FullLineIdentity : Prop :=
  ∀ (k : ℝ → ℂ), ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k (((5/4:ℝ) : ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * logDeriv xiDeriv (((5/4:ℝ) : ℂ) + t * I))
      = ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ

/-- the rational line identity at c = 5/4, as a Prop (Archimedean.rational_line). -/
def RationalLine : Prop :=
  ∀ (k : ℝ → ℂ), ContDiff ℝ 2 k → HasCompactSupport k →
    Integrable (fun t : ℝ => (Hfn k (((5/4:ℝ) : ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * (1 / (((5/4:ℝ) : ℂ) + t * I) + 1 / (((5/4:ℝ) : ℂ) + t * I - 1))) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k (((5/4:ℝ) : ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * (1 / (((5/4:ℝ) : ℂ) + t * I) + 1 / (((5/4:ℝ) : ℂ) + t * I - 1)))
      = Hfn k 0 + Hfn k 1

theorem rationalLine_holds : RationalLine := fun k hk hkc =>
  rational_line hk hkc (by norm_num) (by norm_num)

/-- E′/E on the line: the function g(t) := (deriv E / E)(5/4 + it). -/
def dEE (t : ℝ) : ℂ := deriv Efn (((5/4:ℝ) : ℂ) + t * I) / Efn (((5/4:ℝ) : ℂ) + t * I)

/-- the two-sided test weight on the line 5/4 (= HwC (5/4)). -/
def Hw (k : ℝ → ℂ) (t : ℝ) : ℂ := HwC (5/4) k t

/-- Jcorr k := (1/2π) ∫ [H(5/4+it) + H(1−5/4−it)]·(E′/E)(5/4+it) dt. -/
def Jcorr (k : ℝ → ℂ) : ℂ := (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hw k t * dEE t

/-- under (F2), Hw·(E′/E) is integrable. -/
theorem integrable_Hw_mul_dEE (hF2 : XiDerivZerosInStrip) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : Integrable (fun t : ℝ => Hw k t * dEE t) := by
  obtain ⟨CE, hCE0, hCE⟩ := derivE_div_E_uniform hF2
  exact integrable_HwC_mul_bdd (by norm_num) (by norm_num) hk hkc
    (continuous_derivE_div_E_line (xiDeriv_ne_zero_line hF2)) hCE

/-- pointwise on Re s = 5/4:  ξ″/ξ′ = E + E′/E  (Expansion.logDeriv_xiDeriv_eq_Efn). -/
theorem logDeriv_xiDeriv_line_split' (hF2 : XiDerivZerosInStrip) (t : ℝ) :
    logDeriv xiDeriv (((5/4:ℝ) : ℂ) + t * I) = Efn (((5/4:ℝ) : ℂ) + t * I) + dEE t := by
  rw [logDeriv_xiDeriv_eq_Efn (one_lt_re_54 t) (xiDeriv_ne_zero_line hF2 t), dEE]

/-- **ξ′ explicit formula, literature form with correction**:
Σ' m_{ρ₁} h_k(γ_{ρ₁}) = literatureRHS k + Jcorr k. -/
theorem xiPrime_EF_lit_corr (hF2 : XiDerivZerosInStrip) (hEF1 : FullLineIdentity)
    (_hRL : RationalLine) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf ρ)
      = Zeta23.EF.literatureRHS k + Jcorr k := by
  have hgammaOf : ∀ ρ : ℂ, paperFT k (gammaOf ρ) = Hfn k ρ := fun ρ => rfl
  simp_rw [hgammaOf]
  obtain ⟨hsum, hfull⟩ := hEF1 k hk hkc
  refine ⟨hsum, ?_⟩
  obtain ⟨hintE, hEv⟩ := Efn_line_identity (c := 5/4) (by norm_num) (by norm_num) hk hkc
  have hintJ := integrable_Hw_mul_dEE hF2 hk hkc
  have hintE' : Integrable (fun t : ℝ => Hw k t * Efn (((5/4:ℝ) : ℂ) + t * I)) := hintE
  have e : ∀ t : ℝ, Hw k t * logDeriv xiDeriv (((5/4:ℝ) : ℂ) + t * I)
      = Hw k t * Efn (((5/4:ℝ) : ℂ) + t * I) + Hw k t * dEE t := by
    intro t; rw [logDeriv_xiDeriv_line_split' hF2 t]; ring
  have hfull' : (∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hw k t * logDeriv xiDeriv (((5/4:ℝ):ℂ) + t * I) := by
    rw [← hfull]; rfl
  rw [hfull', Jcorr]
  simp_rw [e]
  rw [integral_add hintE' hintJ, mul_add]
  have hEv' : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hw k t * Efn (((5/4:ℝ) : ℂ) + t * I))
      = Zeta23.EF.literatureRHS k := hEv
  rw [hEv']

end XiPrime
end Zeta23
