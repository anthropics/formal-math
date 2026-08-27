/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Abel.lean — ξ′ generalised-coefficient prime side: the
partial-summation step with a general diagonal density.

Proof of Thm 8.1: "Proposition PP's diagonal becomes
Σ_{N≤X} |b_N|²/N · g(log N) = ∫_0^L g(y) d(Σ_{N≤e^y} |b_N|²/N) = l ∫_0^L g(y) D₁(y/l) dy + o(·)
by Lemma 7.1(i) (Abel summation; g is Lipschitz with constant ≪ 1 and supported in [−L,L])."
Abstract in everything: weights c ≥ 0 or not, any continuous density D, any C¹ window moment g
with |g′| ≤ 2 vanishing on [L, ∞).  Mirror of Zeta23/ThmD/PP.lean's abel_sum_close (density
(log t)²/2 there ↦ l²·∫_0^{log t/l} D here), same Mathlib Abel-summation + IBP route.
-/
import Zeta23.PrimeSideB.PP
import Mathlib.NumberTheory.AbelSummation

noncomputable section

open Real Finset MeasureTheory

namespace Zeta23
namespace XiPrime

/-- **Abel summation against a density.**  If the partial sums satisfy
`|Σ_{k≤t} c_k − l²·∫_0^{log t/l} D| ≤ η` for `1 ≤ t ≤ e^L`, and `g ∈ C¹`, `|g′| ≤ 2`, `g ≡ 0` on `[L,∞)`,
then `|Σ_{n≤e^L} c_n g(log n) − l·∫_0^L D(y/l) g(y) dy| ≤ 2ηL`. -/
theorem abel_sum_density {c : ℕ → ℝ} (hc0 : c 0 = 0) {D : ℝ → ℝ} (hD : Continuous D)
    {lT L η : ℝ} (hl : 0 < lT) (hL : 0 < L)
    (hS : ∀ t : ℝ, 1 ≤ t → t ≤ Real.exp L →
      |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k) - lT ^ 2 * ∫ s in (0:ℝ)..(Real.log t / lT), D s| ≤ η)
    {g : ℝ → ℝ} (hgd : Differentiable ℝ g) (hg'c : Continuous (deriv g))
    (hg'le : ∀ y : ℝ, |deriv g y| ≤ 2) (hgsupp : ∀ y : ℝ, L ≤ y → g y = 0) :
    |(∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, c n * g (Real.log n))
        - lT * ∫ y in (0:ℝ)..L, (D (y / lT) * g y)| ≤ 2 * η * L := by
  classical
  set X := Real.exp L with hX
  have hX1 : 1 < X := by rw [hX]; exact Real.one_lt_exp_iff.2 hL
  have hX0 : 0 < X := by linarith
  have hlogX : Real.log X = L := by rw [hX, Real.log_exp]
  have hη : 0 ≤ η := le_trans (abs_nonneg _) (hS 1 le_rfl hX1.le)
  -- the Abel data
  set f : ℝ → ℝ := fun t => g (Real.log t) with hfdef
  have hfderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (deriv g (Real.log t) / t) t := by
    intro t ht
    have h1 := (hgd (Real.log t)).hasDerivAt
    have h2 := Real.hasDerivAt_log ht.ne'
    have := h1.comp t h2
    rw [hfdef]
    simpa [Function.comp_def, div_eq_mul_inv] using this
  have hdiff : ∀ t ∈ Set.Icc (1:ℝ) X, DifferentiableAt ℝ f t := fun t ht =>
    (hfderiv t (by linarith [ht.1])).differentiableAt
  have hderiv_eq : Set.EqOn (deriv f) (fun t => deriv g (Real.log t) / t)
      (Set.Icc (1:ℝ) X) := fun t ht => (hfderiv t (by linarith [ht.1])).deriv
  have hlogcont : ContinuousOn Real.log (Set.Icc (1:ℝ) X) := by
    apply Real.continuousOn_log.mono
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h0
    rw [h0] at ht
    linarith [ht.1]
  have hinvcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (1:ℝ) X) :=
    continuousOn_inv₀.mono fun t ht => by
      have h1 : (1:ℝ) ≤ t := ht.1
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, ne_eq]
      intro h0; linarith
  have hint : IntegrableOn (deriv f) (Set.Icc (1:ℝ) X) := by
    apply IntegrableOn.congr_fun _ (fun t ht => (hderiv_eq ht).symm) measurableSet_Icc
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    simp_rw [div_eq_mul_inv]
    exact ((hg'c.comp_continuousOn hlogcont)).mul hinvcont
  -- Abel's summation formula
  have habel := sum_mul_eq_sub_integral_mul₀ c hc0 (f := f) X hdiff hint
  have hfX : f X = 0 := by
    show g (Real.log X) = 0
    rw [hlogX]; exact hgsupp L le_rfl
  rw [hfX, zero_mul, zero_sub] at habel
  have hsum_eq : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, c n * g (Real.log n))
      = ∑ k ∈ Finset.Icc 0 ⌊X⌋₊, f k * c k := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc0, mul_zero, zero_add]
    exact Finset.sum_congr rfl fun n _ => by rw [hfdef, mul_comm]
  have hSIoc : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k := by
    intro t
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc0, zero_add]
  -- the main-term function M(t) = l²·∫_0^{log t/l} D and its continuity on [1, X]
  set ID : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, D s with hID
  have hIDderiv : ∀ u, HasDerivAt ID (D u) u := fun u =>
    (hD.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hIDcont : Continuous ID := continuous_iff_continuousAt.2 fun u => (hIDderiv u).continuousAt
  set M : ℝ → ℝ := fun t => lT ^ 2 * ID (Real.log t / lT) with hM
  have hMcont : ContinuousOn M (Set.Icc (1:ℝ) X) := by
    refine continuousOn_const.mul (hIDcont.comp_continuousOn ?_)
    exact hlogcont.div_const _
  -- error piece: |∫ f'·(S − M)| ≤ 2ηL
  have hi1 : IntegrableOn (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) (Set.Ioc (1:ℝ) X) :=
    (integrableOn_mul_sum_Icc c (by norm_num : (0:ℝ) ≤ 1) hint).mono_set Set.Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun t => deriv f t * M t) (Set.Ioc (1:ℝ) X) := by
    refine IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    exact hint.mul_continuousOn hMcont isCompact_Icc
  have herr : |(∫ t in Set.Ioc (1:ℝ) X, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      - ∫ t in Set.Ioc (1:ℝ) X, deriv f t * M t| ≤ 2 * η * L := by
    rw [← integral_sub hi1 hi2]
    have hmajint : IntegrableOn (fun t : ℝ => 2 * η * t⁻¹) (Set.Ioc (1:ℝ) X) := by
      refine IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
      exact ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_const.mul hinvcont)
    have hptw : ∀ t ∈ Set.Ioc (1:ℝ) X,
        |deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - deriv f t * M t| ≤ 2 * η * t⁻¹ := by
      intro t ht
      have ht1 : 1 < t := ht.1
      have ht0 : 0 < t := by linarith
      have hfd : deriv f t = deriv g (Real.log t) / t := hderiv_eq ⟨ht1.le, ht.2⟩
      have hfdabs : |deriv f t| ≤ 2 / t := by
        rw [hfd, abs_div, abs_of_pos ht0]
        exact div_le_div_of_nonneg_right (hg'le _) ht0.le
      rw [← mul_sub, abs_mul, hSIoc t]
      calc |deriv f t| * |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k) - M t| ≤ (2 / t) * η :=
            mul_le_mul hfdabs (hS t ht1.le ht.2) (abs_nonneg _) (by positivity)
        _ = 2 * η * t⁻¹ := by rw [div_eq_mul_inv]; ring
    have hmono : |∫ t in Set.Ioc (1:ℝ) X,
        (deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - deriv f t * M t)|
        ≤ ∫ t in Set.Ioc (1:ℝ) X, 2 * η * t⁻¹ := by
      refine (abs_integral_le_integral_abs).trans ?_
      exact setIntegral_mono_on ((hi1.sub hi2).abs) hmajint measurableSet_Ioc hptw
    have hmaj_eval : ∫ t in Set.Ioc (1:ℝ) X, 2 * η * t⁻¹ = 2 * η * L := by
      rw [← intervalIntegral.integral_of_le hX1.le, intervalIntegral.integral_const_mul,
        integral_inv_of_pos one_pos hX0, div_one, hlogX]
    rw [hmaj_eval] at hmono
    exact hmono
  -- main piece: ∫_1^X f'(t) M(t) dt = −l·∫_0^L D(y/l) g(y) dy (substitution + IBP)
  have hmain : ∫ t in Set.Ioc (1:ℝ) X, deriv f t * M t
      = -(lT * ∫ y in (0:ℝ)..L, (D (y / lT) * g y)) := by
    rw [← intervalIntegral.integral_of_le hX1.le]
    rw [intervalIntegral.integral_congr (g := fun t => (deriv g (Real.log t) / t) * M t) (by
      rw [Set.uIcc_of_le hX1.le]
      intro t ht
      beta_reduce
      rw [hderiv_eq ht])]
    -- substitution t = e^y
    have hsub : ∫ t in (1:ℝ)..X, (deriv g (Real.log t) / t) * M t
        = ∫ y in (0:ℝ)..L, deriv g y * (lT ^ 2 * ID (y / lT)) := by
      have himg : Real.exp '' Set.uIcc (0:ℝ) L ⊆ {t : ℝ | 0 < t} := by
        rintro t ⟨y, _, rfl⟩; exact Real.exp_pos y
      have hlogc : ContinuousOn Real.log {t : ℝ | 0 < t} :=
        Real.continuousOn_log.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at ht ⊢
          exact ht.ne'
      have hgcont : ContinuousOn (fun t => (deriv g (Real.log t) / t) * M t) {t : ℝ | 0 < t} := by
        apply ContinuousOn.mul
        · apply ContinuousOn.div (hg'c.comp_continuousOn hlogc) continuousOn_id
          intro t ht; exact ne_of_gt ht
        · exact continuousOn_const.mul (hIDcont.comp_continuousOn (hlogc.div_const _))
      have := intervalIntegral.integral_comp_mul_deriv' (f := Real.exp) (f' := Real.exp)
        (g := fun t => (deriv g (Real.log t) / t) * M t) (a := (0:ℝ)) (b := L)
        (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
        (hgcont.mono himg)
      rw [Real.exp_zero] at this
      rw [show Real.exp L = X from rfl] at this
      rw [← this]
      apply intervalIntegral.integral_congr
      intro y _
      simp only [Function.comp_apply, hM]
      rw [Real.log_exp]
      have he : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
      field_simp
    rw [hsub]
    -- integration by parts with u = g, v = l²·ID(·/l), v' = l·D(·/l)
    have hv : ∀ y ∈ Set.uIcc (0:ℝ) L,
        HasDerivAt (fun y : ℝ => lT ^ 2 * ID (y / lT)) (lT * D (y / lT)) y := by
      intro y _
      have h1 : HasDerivAt (fun y : ℝ => y / lT) (lT⁻¹) y := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id y).mul_const lT⁻¹
      have h2 := (hIDderiv (y / lT)).comp y h1
      have h3 := h2.const_mul (lT ^ 2)
      exact h3.congr_deriv (by field_simp)
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := g) (u' := deriv g) (v := fun y : ℝ => lT ^ 2 * ID (y / lT))
      (v' := fun y : ℝ => lT * D (y / lT))
      (fun y _ => (hgd y).hasDerivAt) hv (hg'c.intervalIntegrable 0 L)
      ((continuous_const.mul (hD.comp (continuous_id.div_const _))).intervalIntegrable 0 L)
    have hgL : g L = 0 := hgsupp L le_rfl
    have hID0 : ID (0 / lT) = 0 := by simp [hID]
    beta_reduce at hparts
    rw [hgL, hID0] at hparts
    -- hparts : ∫ g · (l D(y/l)) = 0·v(L) − g(0)·(l²·0) − ∫ g' · v
    have e2 : ∫ y in (0:ℝ)..L, deriv g y * (lT ^ 2 * ID (y / lT))
        = -(∫ y in (0:ℝ)..L, g y * (lT * D (y / lT))) := by
      have : (∫ y in (0:ℝ)..L, g y * (lT * D (y / lT)))
          = 0 * (lT ^ 2 * ID (L / lT)) - g 0 * (lT ^ 2 * 0)
            - ∫ y in (0:ℝ)..L, deriv g y * (lT ^ 2 * ID (y / lT)) := hparts
      linarith
    rw [e2, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun y _ => ?_
    beta_reduce
    ring
  -- assemble
  rw [hsum_eq, habel]
  have e : -(∫ t in Set.Ioc (1:ℝ) X, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      - lT * ∫ y in (0:ℝ)..L, (D (y / lT) * g y)
      = -((∫ t in Set.Ioc (1:ℝ) X, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
          - ∫ t in Set.Ioc (1:ℝ) X, deriv f t * M t) := by
    rw [hmain]; ring
  rw [e, abs_neg]
  exact herr

end XiPrime
end Zeta23
