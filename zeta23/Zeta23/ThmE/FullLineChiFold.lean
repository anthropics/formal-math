/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/FullLineChiFold.lean — auxiliary pieces for full_line_identity_chi
(Zeta23/ThmE/FullLineChi.lean), the χ-analogues of verticals_eq (FullLine.lean) and
zero_sum_limit (ZeroSumLimit.lean):
 • the two vertical sides of the rectangle [1−c,c]×[−R,R] for H·Λ_sym'/Λ_sym(·,χ) fold onto the
   line Re s = c: the left side is the χ⁻¹-term, by (Λ_sym'/Λ_sym)(1−s̄,χ) = −conj(Λ_sym'/Λ_sym)(s,χ)
   (FoldChi.logDeriv_completedLSym_one_sub_conj) and conj(Λ_sym'/Λ_sym)(s,χ) = (Λ_sym'/Λ_sym)(s̄,χ⁻¹)
   (FoldChi.logDeriv_completedLSym_inv_conj), then y ↦ −t;
 • the finite zero sums Σ_{|γ|<R_j} m_ρ H(ρ) → the absolutely convergent tsum over LZeros
   (EF_zero_sum_summable_chi).
-/
import Zeta23.ThmE.FullLineChi
import Zeta23.WeilEF.FullLine
import Zeta23.ThmE.FoldChi

open Complex MeasureTheory Set Topology Filter DirichletCharacter
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace ThmE

open Zeta23.WeilEF

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- the folded full-line integrand for χ: H(c+it)·(Λ_sym'/Λ_sym)(c+it,χ) + H(1−c−it)·(Λ_sym'/Λ_sym)(c+it,χ⁻¹). -/
def FlineChi (χ : DirichletCharacter ℂ q) (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  Hfn k ((c:ℂ) + t * I) * logDeriv (completedLSym χ) ((c:ℂ) + t * I)
    + Hfn k (1 - c - t * I) * logDeriv (completedLSym χ⁻¹) ((c:ℂ) + t * I)

/-! ## (V) the vertical sides -/

/-- Λ_sym'/Λ_sym(·,χ) is continuous along Re s = c > 1 (Λ_sym entire, zero-free there). -/
lemma continuous_logDeriv_completedLSym_line (hq : 1 < q) (hprim : χ.IsPrimitive) {c : ℝ} (hc1 : 1 < c) :
    Continuous fun t : ℝ => logDeriv (completedLSym χ) ((c : ℂ) + t * I) := by
  have hχ1 := ne_one_of_primitive hq hprim
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hΛ : AnalyticAt ℂ (completedLSym χ) ((c:ℂ) + t * I) :=
    (differentiable_completedLSym hχ1).analyticAt _
  have hne : completedLSym χ ((c:ℂ) + t * I) ≠ 0 := by
    intro h
    have hz := (completedLSym_eq_zero_iff hq hprim).mp h
    have : ((c:ℂ) + t * I).re < 1 := hz.2.2
    simp at this; linarith
  have h : ContinuousAt (logDeriv (completedLSym χ)) ((c:ℂ) + t * I) :=
    hΛ.deriv.continuousAt.div hΛ.continuousAt hne
  exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + t * I) h (by fun_prop)

/-- **(V) verticals fold for χ.** -/
theorem verticals_eq_chi (hq : 1 < q) (hprim : χ.IsPrimitive) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (_hc2 : c ≤ 3/2) (R : ℝ) :
    VIntegral (fun s => Hfn k s * logDeriv (completedLSym χ) s) c (-R) R
      - VIntegral (fun s => Hfn k s * logDeriv (completedLSym χ) s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, FlineChi χ k c t := by
  have hχ1 := ne_one_of_primitive hq hprim
  have hprim' : χ⁻¹.IsPrimitive := isPrimitive_inv hprim
  set L := logDeriv (completedLSym χ) with hL
  set L' := logDeriv (completedLSym χ⁻¹) with hL'
  have hLc : Continuous (fun t : ℝ => L ((c : ℂ) + t * I)) :=
    continuous_logDeriv_completedLSym_line hq hprim hc1
  have hL'c : Continuous (fun t : ℝ => L' ((c : ℂ) + t * I)) :=
    continuous_logDeriv_completedLSym_line (χ := χ⁻¹) hq hprim' hc1
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := by
    have h := continuous_Hfn_line hk hkc (1 - c)
    have : (fun t : ℝ => Hfn k (1 - c - t * I))
        = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [Function.comp_apply, one_sub_cast]
    rw [this]; exact h.comp continuous_neg
  -- the left-line integrand, pointwise: L((1−c)+iy,χ) = −L'(c−iy,χ⁻¹)
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * L' ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - conj ((c : ℂ) + y * I) := by
      apply Complex.ext <;> simp
    have hval : L (((1 - c : ℝ) : ℂ) + y * I) = -L' ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      rw [hs, hL, logDeriv_completedLSym_one_sub_conj hq hprim, hL',
        ← logDeriv_completedLSym_inv_conj hq hχ1]
      congr 2
      apply Complex.ext <;> simp
    have hH : Hfn k (((1 - c : ℝ) : ℂ) + y * I) = Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    rw [hval, hH]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * L' ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hL'c).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * L' ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * L' ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1

/-! ## (Z) the zero-sum limit -/

/-- **(Z) zero-sum limit for χ.** -/
theorem zero_sum_limit_chi (hq : 1 < q) (hprim : χ.IsPrimitive) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | IsNontrivialZeroL χ ρ ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zeroMultL χ ρ : ℂ) * Hfn k ρ) atTop
      (𝓝 (∑' ρ : (LZeros (LSeam_of hq hprim)).carrier,
        ((LZeros (LSeam_of hq hprim)).mult ρ : ℂ) * Hfn k ρ)) := by
  classical
  set ZC := LZeros (LSeam_of hq hprim) with hZC
  set g : ZC.carrier → ℂ := fun ρ => (ZC.mult ρ : ℂ) * Hfn k ρ with hg
  have hsum : Summable g := EF_zero_sum_summable_chi hq hprim hk hkc
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ IsNontrivialZeroL χ ρ ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  set s : ℕ → Finset ZC.carrier := fun j => (Z j).subtype (· ∈ ZC.carrier) with hsdef
  have hsum_eq : ∀ j, ∑ x ∈ s j, g x = ∑ ρ ∈ Z j, (zeroMultL χ ρ : ℂ) * Hfn k ρ := by
    intro j
    have h1 := Finset.sum_subtype_eq_sum_filter (s := Z j)
      (p := (· ∈ ZC.carrier)) (fun ρ : ℂ => (zeroMultL χ ρ : ℂ) * Hfn k ρ)
    have h2 : (Z j).filter (· ∈ ZC.carrier) = Z j := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((hmemZ j ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
    rfl
  have hRmono : ∀ i j : ℕ, i ≤ j → R i ≤ R j := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hR i).2, (hR j).1]
  have hmono : Monotone s := by
    intro i j hij x hx
    rw [Finset.mem_subtype, hmemZ] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have := hRmono i j hij
    exact ⟨h1, by linarith, by linarith⟩
  have hexh : ∀ b : Finset ZC.carrier, ∃ j, b ≤ s j := by
    intro b
    set M : ℝ := ∑ x ∈ b, |((x : ℂ)).im| with hM
    have hMle : ∀ x ∈ b, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : ZC.carrier => |((x : ℂ)).im|)
        (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, hmemZ]
    have hx0 : IsNontrivialZeroL χ (x : ℂ) := x.2
    have habs := abs_le.mp (hMle x hx)
    have hRj := (hR j).1
    exact ⟨hx0, by linarith [habs.1], by linarith [habs.2]⟩
  have hs_tend : Tendsto s atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset ZC.carrier => ∑ x ∈ S, g x) atTop (𝓝 (∑' x, g x)) := by
    have hHas := hsum.hasSum
    simpa [HasSum] using hHas
  have := hT.comp hs_tend
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, hsum_eq]

end ThmE
end Zeta23
