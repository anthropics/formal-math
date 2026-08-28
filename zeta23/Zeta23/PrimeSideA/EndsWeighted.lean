/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/EndsWeighted.lean

Substrate for the 𝓔₂ bound [lem:ends], shared with EndsNu.lean (the
1-D estimates N1/N2): log⁺/√ facts, pointwise ν-bounds from NuBound, integrability of the
ψ-weighted ν integrals, and the grid-domination lemmas reducing Σ_{k<d} ψ(τ−τ_k) to
Σ_{j<d} ψ(Δ + jh), Δ = dist(τ, I).
-/
import Zeta23.PrimeSideA.EndsCore

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide
section Prelim

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem max_log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : max (Real.log x) 0 ≤ 2 * Real.sqrt x := by
  refine max_le ?_ (by positivity)
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  · have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]
    calc Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := h
      _ = 2 * x ^ (1 / 2 : ℝ) := by ring

theorem abs_nuX_le_B (hν : NuBound p B ν) (hT : 0 < p.T) {τ : ℝ} (hτ : |τ| ≤ 4 * p.T) :
    |ν τ| ≤ B := by
  have h := hν τ
  have hmax : max (Real.log (|τ| / (4 * p.T))) 0 = 0 := by
    rw [max_eq_right]
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by positivity)]
    exact hτ
  rw [hmax, add_zero] at h
  exact h

theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hx' := Real.sq_sqrt hx
    have hy' := Real.sq_sqrt hy
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

theorem abs_nuX_le_B_add_sqrt (hν : NuBound p B ν) (hT : 0 < p.T) (τ : ℝ) :
    |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) := by
  have h := hν τ
  refine h.trans ?_
  gcongr
  exact max_log_le_two_sqrt (by positivity)

theorem sqrt_shift_le {a r T' : ℝ} (hT : 0 < T') (ha : |a| ≤ 4 * T') :
    Real.sqrt (|a + r| / (4 * T')) ≤ 1 + Real.sqrt (|r| / (4 * T')) := by
  have h1 : |a + r| / (4 * T') ≤ |a| / (4 * T') + |r| / (4 * T') := by
    rw [← add_div]
    gcongr
    exact abs_add_le a r
  calc Real.sqrt (|a + r| / (4 * T'))
      ≤ Real.sqrt (|a| / (4 * T') + |r| / (4 * T')) := Real.sqrt_le_sqrt h1
    _ ≤ Real.sqrt (|a| / (4 * T')) + Real.sqrt (|r| / (4 * T')) :=
        sqrt_add_le' (by positivity) (by positivity)
    _ ≤ 1 + Real.sqrt (|r| / (4 * T')) := by
        gcongr
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by rw [div_le_one (by positivity)]; linarith)

theorem psiA_aestronglyMeasurable (hF : LocalHypsCoreW cϱ p F) :
    AEStronglyMeasurable (psiA cϱ p) (volume : Measure ℝ) :=
  hF.psi_integrable.aestronglyMeasurable

end Prelim

section Weighted

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- ψ(· − a) is integrable. -/
theorem psiA_shift_integrable (hF : LocalHypsCoreW cϱ p F) (a : ℝ) :
    Integrable (fun τ : ℝ => psiA cϱ p (τ - a)) :=
  hF.psi_integrable.comp_sub_right a

/-- ∫ ψ(τ − a) dτ = ∫ ψ. -/
theorem integral_psiA_shift (a : ℝ) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) = ∫ r : ℝ, psiA cϱ p r :=
  integral_sub_right_eq_self (psiA cϱ p) a

set_option maxHeartbeats 1000000 in
/-- ψ(r)·√|r| is integrable (L·√|r| near 0, (c/w)|r|^(−3/2) at infinity). -/
theorem integrable_psiA_mul_sqrt (hF : LocalHypsCoreW cϱ p F) :
    Integrable (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) := by
  have hL := hF.L_pos
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : (0 : ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hmeas : AEStronglyMeasurable (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) volume :=
    (psiA_aestronglyMeasurable hF).mul
      (Real.continuous_sqrt.comp continuous_abs).aestronglyMeasurable
  have hnn : ∀ r : ℝ, 0 ≤ psiA cϱ p r * Real.sqrt |r| :=
    fun r => mul_nonneg (psiA_nonneg hL.le hc hw r) (Real.sqrt_nonneg _)
  have heven : ∀ r : ℝ, psiA cϱ p (-r) * Real.sqrt |(-r)| = psiA cϱ p r * Real.sqrt |r| := by
    intro r; rw [psiA_even, abs_neg]
  have htail : ∀ r : ℝ, r ∈ Ioi (1 : ℝ) →
      psiA cϱ p r * Real.sqrt |r| ≤ (cϱ / p.w) * r ^ (-(3 / 2) : ℝ) := by
    intro r hr
    have hr1 : (1 : ℝ) < r := hr
    have hr0 : (0 : ℝ) < r := by linarith
    have h1 : psiA cϱ p r ≤ cϱ / (p.w * r ^ 2) := psiA_le_div_sq (by linarith)
    have h2 : Real.sqrt |r| = r ^ (1 / 2 : ℝ) := by
      rw [abs_of_pos hr0, Real.sqrt_eq_rpow]
    calc psiA cϱ p r * Real.sqrt |r| ≤ cϱ / (p.w * r ^ 2) * r ^ (1 / 2 : ℝ) := by
          rw [h2]; gcongr
      _ = (cϱ / p.w) * r ^ (-(3 / 2) : ℝ) := by
          rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hr0, Real.rpow_two]
          field_simp
  have hIoi : IntegrableOn (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1)
      one_pos).const_mul (cϱ / p.w)).mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn r)]
    exact htail r hr
  have hIio : IntegrableOn (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) (Iio (-1)) := by
    have hIoi' : IntegrableOn (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) (Ioi (-(-1) : ℝ)) := by
      rw [neg_neg]; exact hIoi
    have h := hIoi'.comp_neg_Iio
    exact h.congr_fun (fun r _ => heven r) measurableSet_Iio
  have hIcc : IntegrableOn (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) (Icc (-1) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => p.L) (Icc (-1 : ℝ) 1) :=
      integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine hconst.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn r)]
    calc psiA cϱ p r * Real.sqrt |r| ≤ p.L * 1 := by
          refine mul_le_mul (psiA_le_L r) ?_ (Real.sqrt_nonneg _) hL.le
          rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
          exact Real.sqrt_le_sqrt (abs_le.mpr ⟨hr.1, hr.2⟩)
      _ = p.L := mul_one _
  have hall : IntegrableOn (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) univ := by
    rw [show (univ : Set ℝ) = Iio (-1) ∪ (Icc (-1) 1 ∪ Ioi 1) from ?_]
    · exact hIio.union (hIcc.union hIoi)
    · rw [Set.Icc_union_Ioi_eq_Ici (by norm_num : (-1 : ℝ) ≤ 1), Set.Iio_union_Ici]
  rwa [integrableOn_univ] at hall

/-- ψ(· − a)·|ν| is integrable, for a ∈ [T, 2T]. -/
theorem integrable_psiA_shift_mul_nu (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB1 : 1 ≤ B) (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    Integrable (fun τ : ℝ => psiA cϱ p (τ - a) * |ν τ|) := by
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : (0 : ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hB0 : 0 ≤ B := by linarith
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => psiA cϱ p (τ - a) * |ν τ|) volume :=
    (psiA_shift_integrable hF a).aestronglyMeasurable.mul
      (hνc.abs.aestronglyMeasurable)
  have hdom : Integrable (fun τ : ℝ =>
      psiA cϱ p (τ - a) * (B + 2) + psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T) := by
    refine ((psiA_shift_integrable hF a).mul_const _).add ?_
    have := ((integrable_psiA_mul_sqrt hF).comp_sub_right a).div_const (Real.sqrt p.T)
    exact this
  refine hdom.mono' hmeas ?_
  filter_upwards with τ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (psiA_nonneg hL.le hc hw _) (abs_nonneg _))]
  have hν1 : |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) :=
    abs_nuX_le_B_add_sqrt hν hT0 τ
  have hsh : Real.sqrt (|τ| / (4 * p.T)) ≤ 1 + Real.sqrt (|τ - a| / (4 * p.T)) := by
    have := sqrt_shift_le (a := a) (r := τ - a) (T' := p.T) hT0 (by
      rw [abs_of_nonneg (by linarith [ha.1] : (0:ℝ) ≤ a)]
      linarith [ha.2])
    simpa using this
  have hsq : Real.sqrt (|τ - a| / (4 * p.T)) = Real.sqrt |τ - a| / (2 * Real.sqrt p.T) := by
    rw [Real.sqrt_div (abs_nonneg _), show (4 : ℝ) * p.T = 2 ^ 2 * p.T by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hbound : |ν τ| ≤ (B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T := by
    have h2 : 2 * Real.sqrt (|τ - a| / (4 * p.T)) ≤ Real.sqrt |τ - a| / Real.sqrt p.T := by
      rw [hsq]
      have hs0 : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT0
      refine le_of_eq ?_
      field_simp
    calc |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) := hν1
      _ ≤ B + 2 * (1 + Real.sqrt (|τ - a| / (4 * p.T))) := by gcongr
      _ = (B + 2) + 2 * Real.sqrt (|τ - a| / (4 * p.T)) := by ring
      _ ≤ (B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T := by linarith [h2]
  calc psiA cϱ p (τ - a) * |ν τ|
      ≤ psiA cϱ p (τ - a) * ((B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T) := by
        gcongr
        exact psiA_nonneg hL.le hc hw _
    _ = psiA cϱ p (τ - a) * (B + 2) + psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T := by
        ring

end Weighted

section Grid

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- Left grid domination: for τ ≤ T the distances to the grid points T + k·h are exactly
(T − τ) + k·h (evenness of ψ). -/
theorem sum_psiA_shift_left (T h τ : ℝ) (d : ℕ) :
    ∑ k ∈ Finset.range d, psiA cϱ p (τ - (T + k * h))
      = ∑ k ∈ Finset.range d, psiA cϱ p ((T - τ) + k * h) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show τ - (T + k * h) = -((T - τ) + k * h) by ring, psiA_even]

/-- Right grid domination: for 2T ≤ τ and grid points T + k·h ≤ 2T (k < d), after reflecting the
index the distances dominate (τ − 2T) + j·h (ψ antitone on [0,∞)). -/
theorem sum_psiA_shift_right (hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w)
    {T h τ : ℝ} (hh : 0 < h) (hτ : 2 * T ≤ τ) {d : ℕ}
    (hgrid : ∀ k : ℕ, k < d → T + k * h ≤ 2 * T) :
    ∑ k ∈ Finset.range d, psiA cϱ p (τ - (T + k * h))
      ≤ ∑ j ∈ Finset.range d, psiA cϱ p ((τ - 2 * T) + j * h) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rw [← Finset.sum_range_reflect (fun k => psiA cϱ p (τ - (T + k * h))) d]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j < d := Finset.mem_range.mp hj
  have hdj : d - 1 - j < d := by omega
  have hgr := hgrid (d - 1 - j) hdj
  have hg1 : T + ((d : ℝ) - 1) * h ≤ 2 * T := by
    have h1 := hgrid (d - 1) (by omega)
    rwa [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at h1
  have hcast : ((d - 1 - j : ℕ) : ℝ) = (d : ℝ) - 1 - j := by
    have h1 : j ≤ d - 1 := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  rw [hcast]
  apply psiA_antitoneOn hL hc hw
  · exact Set.mem_Ici.mpr (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh.le])
  · exact Set.mem_Ici.mpr (by nlinarith)
  · nlinarith

end Grid

end PrimeSide
end Zeta23
