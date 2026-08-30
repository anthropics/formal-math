/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], the two one-dimensional ν-weighted ψ estimates feeding the 𝓔₂ bound
(§5.3 of the paper).  Consumed by Zeta23/PrimeSideA/EndsE2.lean.

* N1 `nu_weight_bound` (§5.3: "In the second factor, the range |τ'−τ_k| ≤ 2T has |τ'| ≤ 4T and
  contributes at most 2Ψ₀B; on |τ'−τ_k| =: r > 2T we have |τ'| ≤ 2r, |ν_X(τ')| ≤ B + log(r/T) and
  ψ(r) ≤ c_ϱ r⁻², contributing ≪ B/T. So the second factor is ≤ 3Ψ₀B uniformly in k."):
      ∫_ℝ ψ(τ−a) |ν_X(τ)| dτ ≤ (2Ψ + 5c_ϱ)·B   for a ∈ I = [T,2T],  Ψ := 4 + 2 log(c_ϱL/4w) ≥ Ψ₀.
  Route (constants only differ): |ν_X(τ)| ≤ B + log⁺(|τ|/4T) ≤ B + 2√(|τ|/4T) ≤ B + 2 + 2√(|τ−a|/4T)
  for |a| ≤ 2T, so the integral is ≤ (B+2)∫ψ + T^{-1/2}∫ψ(r)√|r| dr ≤ (B+2)·2Ψ + 2L + 4c_ϱ/w.
* N2 `nu_grid_bound` (§5.3: "The sum over k of the first factor equals ∫_{τ∉I}|ν_X(τ)|σ(τ)dτ with
  σ(τ) := Σ_{k<d} ψ(τ−τ_k) … Hence ∫_{τ∉I}|ν_X|σ ≪ BLl"):
      ∫_{ℝ∖I} |ν_X(τ)| σ(τ) dτ ≤ CN2(c_ϱ)·B·L·l.
Here ψ = `psiA cϱ p` [eq:psidef], B = `B` = l + 4√X and `NuBound p` = [eq:Bdef]
(discharged by nuX_abs_le), all from Zeta23/PrimeSideA/EndsCore.lean.
-/
import Zeta23.PrimeSideA.EndsWeighted

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- The constant of N2 (depends on c_ϱ only; explicit, value immaterial). -/
def CN2 (cϱ : ℝ) : ℝ := 100 * (1 + |Real.log cϱ| + |cϱ|)

lemma CN2_nonneg (cϱ : ℝ) : 0 ≤ CN2 cϱ := by
  unfold CN2
  have h1 : 0 ≤ |Real.log cϱ| := abs_nonneg _
  have h2 : 0 ≤ |cϱ| := abs_nonneg _
  linarith

lemma CN2_def (cϱ : ℝ) : CN2 cϱ = 100 * (1 + |Real.log cϱ| + |cϱ|) := rfl

/-- ∫_ℝ ψ(r)√|r| dr ≤ 2L + 4c_ϱ/w  (ψ ≤ L on |r| ≤ 1, ψ(r)√r ≤ (c_ϱ/w) r^{−3/2} on r > 1). -/
theorem integral_psiA_mul_sqrt_le (hF : LocalHypsCoreW cϱ p F) :
    ∫ r, psiA cϱ p r * Real.sqrt |r| ≤ 2 * p.L + 4 * (cϱ / p.w) := by
  have hL := hF.L_pos
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  set f : ℝ → ℝ := fun s => psiA cϱ p s * Real.sqrt s with hf
  have h1 : (fun r => psiA cϱ p r * Real.sqrt |r|) = fun r => f |r| := by
    funext r; simp only [hf, psiA_abs]
  rw [h1, integral_comp_abs]
  have hint0 : IntegrableOn f (Ioi 0) := by
    have := (integrable_psiA_mul_sqrt hF).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only [hf]; rw [abs_of_pos (Set.mem_Ioi.mp hs)]
  have hsplit : ∫ s in Ioi 0, f s = (∫ s in Ioc 0 1, f s) + ∫ s in Ioi 1, f s := by
    rw [← setIntegral_union ?_ measurableSet_Ioi (hint0.mono_set Ioc_subset_Ioi_self)
      (hint0.mono_set (Ioi_subset_Ioi zero_le_one)), Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'
  have hb1 : ∫ s in Ioc 0 1, f s ≤ p.L := by
    have hvol : volume (Ioc (0:ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    calc ∫ s in Ioc 0 1, f s ≤ ∫ s in Ioc (0:ℝ) 1, p.L := by
          apply setIntegral_mono_on (hint0.mono_set Ioc_subset_Ioi_self)
            (integrableOn_const hvol) measurableSet_Ioc
          intro s hs
          simp only [hf]
          calc psiA cϱ p s * Real.sqrt s ≤ p.L * 1 := by
                apply mul_le_mul (psiA_le_L s) _ (Real.sqrt_nonneg _) hL.le
                rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs.2
            _ = p.L := mul_one _
      _ = p.L := by
          rw [setIntegral_const]
          simp [Measure.real, Real.volume_Ioc]
  have hb2 : ∫ s in Ioi 1, f s ≤ cϱ / p.w * 2 := by
    have hrpow := integral_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) one_pos
    calc ∫ s in Ioi 1, f s ≤ ∫ s in Ioi (1:ℝ), cϱ / p.w * s ^ (-(3/2):ℝ) := by
          apply setIntegral_mono_on (hint0.mono_set (Ioi_subset_Ioi zero_le_one))
            ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _) measurableSet_Ioi
          intro r hr
          have hr1 : (1 : ℝ) < r := hr
          have hr0 : (0 : ℝ) < r := by linarith
          have hψ : psiA cϱ p r ≤ cϱ / (p.w * r ^ 2) := psiA_le_div_sq (by linarith)
          have h2 : Real.sqrt r = r ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow r
          simp only [hf]
          calc psiA cϱ p r * Real.sqrt r ≤ cϱ / (p.w * r ^ 2) * r ^ (1 / 2 : ℝ) := by
                rw [h2]; gcongr
            _ = (cϱ / p.w) * r ^ (-(3 / 2) : ℝ) := by
                rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hr0, Real.rpow_two]
                field_simp
      _ = cϱ / p.w * ∫ s in Ioi (1:ℝ), s ^ (-(3/2):ℝ) := integral_const_mul _ _
      _ = cϱ / p.w * 2 := by rw [hrpow, Real.one_rpow]; norm_num
  rw [hsplit]
  linarith

/-- **N1, master form** (§5.3, "the second factor is ≤ 3Ψ₀B uniformly in k"): for a ∈ [T,2T] and any level
`B` with `L ≤ 2B`, `4 ≤ B`,   ∫_ℝ ψ(τ−a)|ν(τ)| dτ ≤ (2(4 + 2 log(c_ϱL/4w)) + 7c_ϱ)·B.
(The two paper regimes are the corollaries `nu_weight_bound` (B ≥ l ≥ L/2) and `nu_weight_bound_L` (B ≥ L).) -/
theorem nu_weight_bound_of_L_le_two_B (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hL2B : p.L ≤ 2 * B) (hB4 : 4 ≤ B)
    (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B := by
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hw1 := hF.one_le_w
  have hw : 0 < p.w := by linarith
  have hc4 := hF.four_le_cϱ
  have hc : (0 : ℝ) ≤ cϱ := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  -- pointwise domination (same as in integrable_psiA_shift_mul_nu)
  have hpt : ∀ τ, psiA cϱ p (τ - a) * |ν τ|
      ≤ psiA cϱ p (τ - a) * (B + 2)
        + psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T := by
    intro τ
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
    have hs0 : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT0
    have h2 : 2 * Real.sqrt (|τ - a| / (4 * p.T)) = Real.sqrt |τ - a| / Real.sqrt p.T := by
      rw [hsq]; field_simp
    have hbound : |ν τ| ≤ (B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T := by
      calc |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) := hν1
        _ ≤ B + 2 * (1 + Real.sqrt (|τ - a| / (4 * p.T))) := by gcongr
        _ = (B + 2) + 2 * Real.sqrt (|τ - a| / (4 * p.T)) := by ring
        _ = (B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T := by rw [h2]
    calc psiA cϱ p (τ - a) * |ν τ|
        ≤ psiA cϱ p (τ - a) * ((B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T) :=
          mul_le_mul_of_nonneg_left hbound (psiA_nonneg_of hF _)
      _ = _ := by ring
  have hI1 := integrable_psiA_shift_mul_nu hνc hF hν hB1 hT ha
  have hI2 : Integrable (fun τ => psiA cϱ p (τ - a) * (B + 2)) :=
    (psiA_shift_integrable hF a).mul_const _
  have hI3 : Integrable (fun τ => psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T) :=
    ((integrable_psiA_mul_sqrt hF).comp_sub_right a).div_const _
  have hΨ := integral_psiA_le hF
  have hS := integral_psiA_mul_sqrt_le hF
  have hmain : ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (B + 2) * (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))))
        + (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T := by
    calc ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
        ≤ ∫ τ : ℝ, (psiA cϱ p (τ - a) * (B + 2)
            + psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T) :=
          integral_mono hI1 (hI2.add hI3) hpt
      _ = ((B + 2) * ∫ r, psiA cϱ p r)
          + (∫ r, psiA cϱ p r * Real.sqrt |r|) / Real.sqrt p.T := by
          have hshift : ∫ τ : ℝ, psiA cϱ p (τ - a) * Real.sqrt |τ - a|
              = ∫ r : ℝ, psiA cϱ p r * Real.sqrt |r| :=
            integral_sub_right_eq_self (fun r => psiA cϱ p r * Real.sqrt |r|) a
          rw [integral_add hI2 hI3, integral_mul_const, integral_div, integral_psiA_shift,
            mul_comm, hshift]
      _ ≤ (B + 2) * (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))))
          + (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T :=
          add_le_add (mul_le_mul_of_nonneg_left hΨ (by positivity))
            (div_le_div_of_nonneg_right hS (Real.sqrt_nonneg _))
  -- the arithmetic:  4Ψ + (2L + 4c/w)/√T ≤ 5cB
  have hsT : 1 ≤ Real.sqrt p.T := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT
  have hcw : cϱ / p.w ≤ cϱ := div_le_self hc hw1
  have htail : (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T ≤ 2 * p.L + 4 * cϱ := by
    calc (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T ≤ 2 * p.L + 4 * (cϱ / p.w) :=
          div_le_self (by positivity) hsT
      _ ≤ 2 * p.L + 4 * cϱ := by linarith
  have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
  have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / 4 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos harg
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith
  -- endgame: 4Ψ + 2L + 4c ≤ 8 + 2cL + 2L + 4c ≤ 8 + 4c + 5cB ≤ 7cB  (Ψ ≤ 2 + cL/2, L ≤ 2B, 4 ≤ c, 4 ≤ B)
  have hcL : cϱ * p.L ≤ 2 * (cϱ * B) := by nlinarith
  have h2L : 2 * p.L ≤ cϱ * B := by nlinarith
  have h8c : 8 + 4 * cϱ ≤ 2 * (cϱ * B) := by nlinarith
  nlinarith [hmain, htail, hlog, hcL, h2L, h8c, hB0]

/-- **N1** (§5.3, "the second factor is ≤ 3Ψ₀B uniformly in k"): for a ∈ [T,2T],
  ∫_ℝ ψ(τ−a)|ν_X(τ)| dτ ≤ (2(4 + 2 log(c_ϱL/4w)) + 7c_ϱ)·B   (paper regime B ≥ l, L ≤ 2l). -/
theorem nu_weight_bound (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBl : p.l ≤ B) (hL2l : p.L ≤ 2 * p.l)
    (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B := by
  have hl4 : 4 ≤ p.l := by linarith [hF.eight_le_L]
  exact nu_weight_bound_of_L_le_two_B hνc hF hν (by linarith) (by linarith) hT ha

/-- **N1, L-intrinsic form** (no bandwidth cap; the absorbing hypothesis is `L ≤ B`). -/
theorem nu_weight_bound_L (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBL : p.L ≤ B)
    (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B := by
  exact nu_weight_bound_of_L_le_two_B hνc hF hν (by linarith [hF.L_pos]) (by linarith [hF.eight_le_L]) hT ha


/-! ### N2: reduction to the half-line and the majorant -/

/-- change of variables Δ = T − τ on (−∞, T). -/
lemma setIntegral_Iio_comp_sub_left (f : ℝ → ℝ) (T : ℝ) :
    ∫ τ in Iio T, f (T - τ) = ∫ Δ in Ioi 0, f Δ := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  have e : (fun τ => (Iio T).indicator (fun τ => f (T - τ)) τ)
      = fun τ => (Ioi (0:ℝ)).indicator f (T - τ) := by
    funext τ
    by_cases h : τ < T
    · rw [indicator_of_mem (show τ ∈ Iio T from h),
        indicator_of_mem (show T - τ ∈ Ioi (0:ℝ) from sub_pos.mpr h)]
    · rw [indicator_of_notMem (show τ ∉ Iio T from h),
        indicator_of_notMem (show T - τ ∉ Ioi (0:ℝ) from fun h' => h (sub_pos.mp h'))]
  rw [e]
  exact integral_sub_left_eq_self ((Ioi (0:ℝ)).indicator f) volume T

/-- change of variables Δ = τ − c on (c, ∞). -/
lemma setIntegral_Ioi_comp_sub_right (f : ℝ → ℝ) (c : ℝ) :
    ∫ τ in Ioi c, f (τ - c) = ∫ Δ in Ioi 0, f Δ := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have e : (fun τ => (Ioi c).indicator (fun τ => f (τ - c)) τ)
      = fun τ => (Ioi (0:ℝ)).indicator f (τ - c) := by
    funext τ
    by_cases h : c < τ
    · rw [indicator_of_mem (show τ ∈ Ioi c from h),
        indicator_of_mem (show τ - c ∈ Ioi (0:ℝ) from sub_pos.mpr h)]
    · rw [indicator_of_notMem (show τ ∉ Ioi c from h),
        indicator_of_notMem (show τ - c ∉ Ioi (0:ℝ) from fun h' => h (sub_pos.mp h'))]
  rw [e]
  exact integral_sub_right_eq_self ((Ioi (0:ℝ)).indicator f) c

/-- σ reduced to the half-line: S(Δ) := Σ_{j<d} ψ(Δ + jh)  (§5.3). -/
def Sgrid (cϱ : ℝ) (p : Setting) (Δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range p.d, psiA cϱ p (Δ + j * p.h)

lemma Setting.h_pos (hL : 0 < p.L) : 0 < p.h := by
  unfold Setting.h; positivity

lemma Setting.h_inv (_hL : 0 < p.L) : (p.h)⁻¹ = p.L / (2 * π) := by
  unfold Setting.h; rw [inv_div]

/-- near range (§5.3): S(Δ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ ψ. -/
lemma Sgrid_le_near (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Sgrid cϱ p Δ ≤ psiA cϱ p Δ + p.L / (2 * π) * ∫ r in Ioi Δ, psiA cϱ p r := by
  have h := sum_psiA_grid_le hF hΔ (Setting.h_pos hF.L_pos) p.d
  rw [Setting.h_inv hF.L_pos] at h
  exact h

/-- far range (§5.3): S(Δ) ≤ d ψ(Δ)  (ψ antitone). -/
lemma Sgrid_le_far (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Sgrid cϱ p Δ ≤ p.d * psiA cϱ p Δ := by
  have hh := Setting.h_pos (p := p) hF.L_pos
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  unfold Sgrid
  calc ∑ j ∈ Finset.range p.d, psiA cϱ p (Δ + j * p.h)
      ≤ ∑ j ∈ Finset.range p.d, psiA cϱ p Δ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hj : 0 ≤ (j:ℝ) * p.h := by positivity
        exact psiA_antitoneOn hF.L_pos.le hc hw (Set.mem_Ici.mpr hΔ)
          (Set.mem_Ici.mpr (by linarith)) (by linarith)
    _ = p.d * psiA cϱ p Δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma Sgrid_nonneg (hF : LocalHypsCoreW cϱ p F) (Δ : ℝ) : 0 ≤ Sgrid cϱ p Δ :=
  Finset.sum_nonneg fun _ _ => psiA_nonneg_of hF _

/-- σ(τ) = S(T−τ) for τ ≤ T;  σ(τ) ≤ S(τ−2T) for τ ≥ 2T. -/
lemma sigma_eq_left (τ : ℝ) :
    ∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k) = Sgrid cϱ p (p.T - τ) := by
  unfold Sgrid
  simp_rw [Setting.tau_natCast]
  exact sum_psiA_shift_left p.T p.h τ p.d

lemma sigma_le_right (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T) {τ : ℝ} (hτ : 2 * p.T ≤ τ) :
    ∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k) ≤ Sgrid cϱ p (τ - 2 * p.T) := by
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  unfold Sgrid
  simp_rw [Setting.tau_natCast]
  refine sum_psiA_shift_right hF.L_pos.le hc hw (Setting.h_pos hF.L_pos) hτ ?_
  intro k hk
  have := p.tau_mem hF.L_pos hT (Finset.mem_range.mpr hk)
  rw [Setting.tau_natCast] at this
  exact this.2

/-- The half-line majorants (§5.3).  Near: Δ ≤ 2T, |ν| ≤ B and
S(Δ) ≤ ψ(Δ) + (L/2π)min(Ψ', c/(wΔ));  far: Δ > 2T, |ν| ≤ B + 2√(Δ/T) and S(Δ) ≤ d c/(wΔ²). -/
def Mnear (cϱ : ℝ) (p : Setting) (B : ℝ) (Δ : ℝ) : ℝ :=
  B * (psiA cϱ p Δ + p.L / (2 * π) * min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)))

def Mfar (cϱ : ℝ) (p : Setting) (B : ℝ) (Δ : ℝ) : ℝ :=
  p.d * (cϱ / (p.w * Δ ^ 2)) * (B + 2 * Real.sqrt (Δ / p.T))

def Mtot (cϱ : ℝ) (p : Setting) (B : ℝ) (Δ : ℝ) : ℝ :=
  (Ioc 0 (2 * p.T)).indicator (Mnear cϱ p B) Δ + (Ioi (2 * p.T)).indicator (Mfar cϱ p B) Δ

lemma Mnear_nonneg (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) {Δ : ℝ} (hΔ : 0 < Δ) : 0 ≤ Mnear cϱ p B Δ := by

  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hL := hF.L_pos
  have h1 : 0 ≤ ∫ r in Ioi 0, psiA cϱ p r := setIntegral_nonneg measurableSet_Ioi
    fun r _ => psiA_nonneg_of hF r
  unfold Mnear
  have : 0 ≤ min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)) := le_min h1 (by positivity)
  have := psiA_nonneg_of hF Δ
  positivity

lemma Mfar_nonneg (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) (hT : 0 < p.T) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 ≤ Mfar cϱ p B Δ := by

  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  unfold Mfar; positivity

/-- the product S(Δ)·(ν-bound) against the majorant, near range. -/
lemma Sgrid_mul_le_Mnear (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v ≤ B) : Sgrid cϱ p Δ * v ≤ Mnear cϱ p B Δ := by
  have hS := Sgrid_le_near hF hΔ.le
  have htail : ∫ r in Ioi Δ, psiA cϱ p r ≤ min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)) :=
    le_min (setIntegral_psiA_Ioi_mono hF hΔ.le) (setIntegral_psiA_Ioi_le_div hF hΔ)
  have hL := hF.L_pos
  have hS' : Sgrid cϱ p Δ ≤ psiA cϱ p Δ + p.L / (2 * π) *
      min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)) := by
    refine hS.trans ?_
    gcongr
  unfold Mnear
  rw [mul_comm (B)]
  exact mul_le_mul hS' hv hv0 (le_trans (Sgrid_nonneg hF Δ) hS')

/-- the product S(Δ)·(ν-bound) against the majorant, far range. -/
lemma Sgrid_mul_le_Mfar (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v ≤ B + 2 * Real.sqrt (Δ / p.T)) : Sgrid cϱ p Δ * v ≤ Mfar cϱ p B Δ := by
  have hS := Sgrid_le_far hF hΔ.le
  have hψ : psiA cϱ p Δ ≤ cϱ / (p.w * Δ ^ 2) := psiA_le_div_sq hΔ.ne'
  have hS' : Sgrid cϱ p Δ ≤ p.d * (cϱ / (p.w * Δ ^ 2)) :=
    hS.trans (mul_le_mul_of_nonneg_left hψ (Nat.cast_nonneg _))
  unfold Mfar
  exact mul_le_mul hS' hv hv0 (le_trans (Sgrid_nonneg hF Δ) hS')

/-- pointwise domination, left of I:  σ(τ)|ν(τ)| ≤ M(T−τ) for τ < T. -/
lemma dom_left (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 0 < p.T) {τ : ℝ} (hτ : τ < p.T) :
    (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ Mtot cϱ p B (p.T - τ) := by
  rw [sigma_eq_left]
  set Δ := p.T - τ with hΔdef
  have hΔ : 0 < Δ := by rw [hΔdef]; linarith
  unfold Mtot
  rcases le_or_gt Δ (2 * p.T) with h | h
  · rw [indicator_of_mem (show Δ ∈ Ioc 0 (2 * p.T) from ⟨hΔ, h⟩),
      indicator_of_notMem (show Δ ∉ Ioi (2 * p.T) from not_lt.mpr h), add_zero]
    refine Sgrid_mul_le_Mnear hF hΔ (abs_nonneg _) (abs_nuX_le_B hν hT ?_)
    rw [abs_le]; constructor <;> linarith
  · rw [indicator_of_notMem (show Δ ∉ Ioc 0 (2 * p.T) from fun hh => not_lt.mpr hh.2 h),
      indicator_of_mem (show Δ ∈ Ioi (2 * p.T) from h), zero_add]
    refine Sgrid_mul_le_Mfar hF hΔ (abs_nonneg _) ((abs_nuX_le_B_add_sqrt hν hT τ).trans ?_)
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num : (0:ℝ) ≤ 2))
    rw [div_le_div_iff₀ (by positivity) hT]
    have : |τ| ≤ Δ := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg τ]

/-- pointwise domination, right of I:  σ(τ)|ν(τ)| ≤ M(τ−2T) for τ > 2T. -/
lemma dom_right (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 0 < p.T) {τ : ℝ}
    (hτ : 2 * p.T < τ) :
    (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ Mtot cϱ p B (τ - 2 * p.T) := by
  have hσ := sigma_le_right hF hT.le hτ.le
  set Δ := τ - 2 * p.T with hΔdef
  have hΔ : 0 < Δ := by rw [hΔdef]; linarith
  have hσ0 : 0 ≤ ∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k) :=
    Finset.sum_nonneg fun k _ => psiA_nonneg_of hF _
  have step : (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ Sgrid cϱ p Δ * |ν τ| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
  refine step.trans ?_
  unfold Mtot
  rcases le_or_gt Δ (2 * p.T) with h | h
  · rw [indicator_of_mem (show Δ ∈ Ioc 0 (2 * p.T) from ⟨hΔ, h⟩),
      indicator_of_notMem (show Δ ∉ Ioi (2 * p.T) from not_lt.mpr h), add_zero]
    refine Sgrid_mul_le_Mnear hF hΔ (abs_nonneg _) (abs_nuX_le_B hν hT ?_)
    rw [abs_le]; constructor <;> linarith
  · rw [indicator_of_notMem (show Δ ∉ Ioc 0 (2 * p.T) from fun hh => not_lt.mpr hh.2 h),
      indicator_of_mem (show Δ ∈ Ioi (2 * p.T) from h), zero_add]
    refine Sgrid_mul_le_Mfar hF hΔ (abs_nonneg _) ((abs_nuX_le_B_add_sqrt hν hT τ).trans ?_)
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num : (0:ℝ) ≤ 2))
    rw [div_le_div_iff₀ (by positivity) hT]
    have : |τ| ≤ 2 * Δ := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg τ]


/-! ### N2: integrating the majorant -/

lemma Mnear_integrableOn (hF : LocalHypsCoreW cϱ p F) (_hT : 0 < p.T) :
    IntegrableOn (Mnear cϱ p B) (Ioc 0 (2 * p.T)) := by
  have hΨ0 : 0 ≤ ∫ r in Ioi 0, psiA cϱ p r :=
    setIntegral_nonneg measurableSet_Ioi fun r _ => psiA_nonneg_of hF r
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hmeas : Measurable fun Δ : ℝ => min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)) :=
    measurable_const.min (measurable_const.div (measurable_const.mul measurable_id))
  have hmin : IntegrableOn (fun Δ : ℝ => min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)))
      (Ioc 0 (2 * p.T)) := by
    refine Integrable.mono' (g := fun _ => ∫ r in Ioi 0, psiA cϱ p r)
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with Δ hΔ
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hΨ0 (by have := hΔ.1; positivity))]
    exact min_le_left _ _
  unfold Mnear
  exact ((hF.psi_integrable.integrableOn).add (hmin.const_mul _)).const_mul _

/-- rpow form of the far majorant on Δ > 0. -/
lemma Mfar_eq_rpow (hT : 0 < p.T) {Δ : ℝ} (hΔ : 0 < Δ) :
    Mfar cϱ p B Δ = p.d * (cϱ / p.w) *
      (B * Δ ^ (-2:ℝ) + (2 / Real.sqrt p.T) * Δ ^ (-(3/2):ℝ)) := by
  unfold Mfar
  have hw : Δ ^ (-2:ℝ) = (Δ ^ 2)⁻¹ := by rw [Real.rpow_neg hΔ.le, Real.rpow_two]
  have h32 : Δ ^ (-(3/2):ℝ) = Δ ^ (1/2:ℝ) / Δ ^ 2 := by
    rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hΔ, Real.rpow_two]
  rw [hw, h32, Real.sqrt_div hΔ.le, Real.sqrt_eq_rpow]
  have : Δ ^ 2 ≠ 0 := by positivity
  have : Real.sqrt p.T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  field_simp

lemma Mfar_integrableOn (_hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    IntegrableOn (Mfar cϱ p B) (Ioi (2 * p.T)) := by
  have h2T : 0 < 2 * p.T := by linarith
  have hg : IntegrableOn (fun Δ : ℝ => p.d * (cϱ / p.w) *
      (B * Δ ^ (-2:ℝ) + (2 / Real.sqrt p.T) * Δ ^ (-(3/2):ℝ))) (Ioi (2 * p.T)) :=
    ((((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) h2T).const_mul _).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) h2T).const_mul _)).const_mul _)
  refine hg.congr_fun (fun Δ hΔ => ?_) measurableSet_Ioi
  exact (Mfar_eq_rpow hT (lt_trans h2T hΔ)).symm

lemma Mtot_integrable (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) : Integrable (Mtot cϱ p B) := by
  unfold Mtot
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr (Mnear_integrableOn hF hT)).add
    ((integrable_indicator_iff measurableSet_Ioi).mpr (Mfar_integrableOn hF hT))

lemma integral_Mtot_eq (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    ∫ Δ in Ioi 0, Mtot cϱ p B Δ
      = (∫ Δ in Ioc 0 (2 * p.T), Mnear cϱ p B Δ) + ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun Δ hΔ => ?_)]
  · unfold Mtot
    rw [integral_add ((integrable_indicator_iff measurableSet_Ioc).mpr (Mnear_integrableOn hF hT))
      ((integrable_indicator_iff measurableSet_Ioi).mpr (Mfar_integrableOn hF hT)),
      integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi]
  · unfold Mtot
    have hΔ' : Δ ≤ 0 := not_lt.mp hΔ
    rw [indicator_of_notMem (fun h : Δ ∈ Ioc 0 (2 * p.T) => not_lt.mpr hΔ' h.1),
      indicator_of_notMem (fun h : Δ ∈ Ioi (2 * p.T) => not_lt.mpr hΔ' (lt_trans (by linarith) h)),
      add_zero]

/-- near integral (§5.3): ∫_0^{2T} Mnear ≤ B[Ψ' + (L/2π)(Ψ' + (c/w) log 2T)],  Ψ' = ∫_0^∞ ψ. -/
lemma integral_Mnear_le (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) (hT : 1 ≤ p.T) :
    ∫ Δ in Ioc 0 (2 * p.T), Mnear cϱ p B Δ
      ≤ B * ((∫ r in Ioi 0, psiA cϱ p r)
        + p.L / (2 * π) * ((∫ r in Ioi 0, psiA cϱ p r) + cϱ / p.w * Real.log (2 * p.T))) := by
  have hT0 : 0 < p.T := by linarith
  set Ψ' := ∫ r in Ioi 0, psiA cϱ p r with hΨ'
  have hΨ0 : 0 ≤ Ψ' := setIntegral_nonneg measurableSet_Ioi fun r _ => psiA_nonneg_of hF r
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hL := hF.L_pos

  have hmeas : Measurable fun Δ : ℝ => min Ψ' (cϱ / (p.w * Δ)) :=
    measurable_const.min (measurable_const.div (measurable_const.mul measurable_id))
  have hmin_int : ∀ (a b : ℝ), 0 ≤ a →
      IntegrableOn (fun Δ : ℝ => min Ψ' (cϱ / (p.w * Δ))) (Ioc a b) := by
    intro a b ha
    refine Integrable.mono' (g := fun _ => Ψ')
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with Δ hΔ
    have hΔ0 : 0 < Δ := lt_of_le_of_lt ha hΔ.1
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hΨ0 (by positivity))]
    exact min_le_left _ _
  -- (1) ∫_{Ioc 0 2T} ψ ≤ Ψ'
  have h1 : ∫ Δ in Ioc 0 (2 * p.T), psiA cϱ p Δ ≤ Ψ' :=
    setIntegral_mono_set hF.psi_integrable.integrableOn
      (Filter.Eventually.of_forall fun r => psiA_nonneg_of hF r)
      (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
  -- (2) ∫_{Ioc 0 2T} min(Ψ', c/(wΔ)) ≤ Ψ' + (c/w) log 2T  (split at Δ = 1)
  have h2 : ∫ Δ in Ioc 0 (2 * p.T), min Ψ' (cϱ / (p.w * Δ)) ≤ Ψ' + cϱ / p.w * Real.log (2 * p.T) := by
    have h12 : (1:ℝ) ≤ 2 * p.T := by linarith
    have hsplit : ∫ Δ in Ioc 0 (2 * p.T), min Ψ' (cϱ / (p.w * Δ))
        = (∫ Δ in Ioc 0 1, min Ψ' (cϱ / (p.w * Δ))) + ∫ Δ in Ioc 1 (2 * p.T), min Ψ' (cϱ / (p.w * Δ)) := by
      rw [← setIntegral_union ?_ measurableSet_Ioc (hmin_int 0 1 le_rfl) (hmin_int 1 _ zero_le_one),
        Set.Ioc_union_Ioc_eq_Ioc zero_le_one h12]
      exact Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'.1
    have ha : ∫ Δ in Ioc 0 1, min Ψ' (cϱ / (p.w * Δ)) ≤ Ψ' := by
      calc ∫ Δ in Ioc 0 1, min Ψ' (cϱ / (p.w * Δ)) ≤ ∫ Δ in Ioc (0:ℝ) 1, Ψ' :=
            setIntegral_mono_on (hmin_int 0 1 le_rfl)
              (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
              measurableSet_Ioc (fun Δ _ => min_le_left _ _)
        _ = Ψ' := by rw [setIntegral_const]; simp [Measure.real, Real.volume_Ioc]
    have hb : ∫ Δ in Ioc 1 (2 * p.T), min Ψ' (cϱ / (p.w * Δ))
        ≤ cϱ / p.w * Real.log (2 * p.T) := by
      have hcont : ContinuousOn (fun Δ : ℝ => cϱ / p.w * Δ⁻¹) (Icc 1 (2 * p.T)) := by
        apply ContinuousOn.mul continuousOn_const
        exact (continuousOn_inv₀).mono fun x hx => ne_of_gt (lt_of_lt_of_le one_pos hx.1)
      calc ∫ Δ in Ioc 1 (2 * p.T), min Ψ' (cϱ / (p.w * Δ))
          ≤ ∫ Δ in Ioc 1 (2 * p.T), cϱ / p.w * Δ⁻¹ := by
            refine setIntegral_mono_on (hmin_int 1 _ zero_le_one)
              (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc ?_
            intro Δ _
            rw [← div_eq_mul_inv, ← div_mul_eq_div_div]
            exact min_le_right _ _
        _ = cϱ / p.w * ∫ Δ in Ioc 1 (2 * p.T), Δ⁻¹ := integral_const_mul _ _
        _ = cϱ / p.w * Real.log (2 * p.T) := by
            rw [← intervalIntegral.integral_of_le h12, integral_inv_of_pos one_pos (by linarith),
              div_one]
    rw [hsplit]; linarith
  unfold Mnear
  rw [integral_const_mul, integral_add hF.psi_integrable.integrableOn
    ((hmin_int 0 _ le_rfl).const_mul _), integral_const_mul]
  refine mul_le_mul_of_nonneg_left (add_le_add h1 ?_) hB
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- far integral (§5.3): ∫_{2T}^∞ Mfar ≤ (d/T)(c/w)(B/2 + 4). -/
lemma integral_Mfar_le (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) (hT : 1 ≤ p.T) :
    ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ ≤ p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by
  have hT0 : 0 < p.T := by linarith
  have h2T : 0 < 2 * p.T := by linarith
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]

  have hI2 := integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) h2T
  have hI32 := integral_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) h2T
  have hint2 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) h2T
  have hint32 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) h2T
  have e : ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ = p.d * (cϱ / p.w) *
      (B * (∫ Δ in Ioi (2 * p.T), Δ ^ (-2:ℝ))
        + (2 / Real.sqrt p.T) * ∫ Δ in Ioi (2 * p.T), Δ ^ (-(3/2):ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun Δ hΔ => Mfar_eq_rpow (cϱ := cϱ) hT0 (lt_trans h2T hΔ)),
      integral_const_mul, integral_add (hint2.const_mul _) (hint32.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [e, hI2, hI32]
  -- evaluate: (2T)^{-1} and 2(2T)^{-1/2}; bound (2T)^{-1/2} ≤ 1/√T
  have ev1 : -(2 * p.T) ^ ((-2:ℝ) + 1) / ((-2:ℝ) + 1) = 1 / (2 * p.T) := by
    rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]; field_simp
  have ev2 : -(2 * p.T) ^ (-(3/2:ℝ) + 1) / (-(3/2:ℝ) + 1) = 2 * (2 * p.T) ^ (-(1/2):ℝ) := by
    rw [show (-(3/2:ℝ)) + 1 = -(1/2) by norm_num]; field_simp
  rw [ev1, ev2]
  have hsq : (2 * p.T) ^ (-(1/2):ℝ) ≤ 1 / Real.sqrt p.T := by
    rw [Real.rpow_neg h2T.le, ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr hT0) (Real.sqrt_le_sqrt (by linarith))
  have hsT : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT0
  have key : B * (1 / (2 * p.T)) + 2 / Real.sqrt p.T * (2 * (2 * p.T) ^ (-(1/2):ℝ))
      ≤ 1 / p.T * (B / 2 + 4) := by
    have h1 : 2 / Real.sqrt p.T * (2 * (2 * p.T) ^ (-(1/2):ℝ)) ≤ 2 / Real.sqrt p.T * (2 * (1 / Real.sqrt p.T)) := by
      gcongr
    have h2 : 2 / Real.sqrt p.T * (2 * (1 / Real.sqrt p.T)) = 4 / p.T := by
      rw [show (4:ℝ) / p.T = 4 / (Real.sqrt p.T * Real.sqrt p.T) by rw [Real.mul_self_sqrt hT0.le]]
      field_simp; ring
    have h3 : B * (1 / (2 * p.T)) = 1 / p.T * (B / 2) := by field_simp
    rw [h3]
    have : 1 / p.T * (B / 2 + 4) = 1 / p.T * (B / 2) + 4 / p.T := by field_simp
    rw [this]
    linarith
  calc p.d * (cϱ / p.w) * (B * (1 / (2 * p.T)) + 2 / Real.sqrt p.T * (2 * (2 * p.T) ^ (-(1/2):ℝ)))
      ≤ p.d * (cϱ / p.w) * (1 / p.T * (B / 2 + 4)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by field_simp

/-- integrability of N2's integrand on ℝ ∖ I. -/
theorem integrableOn_sigma_mul_abs_nuX (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hT : 1 ≤ p.T) :
    IntegrableOn (fun τ : ℝ =>
      (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|) (p.I)ᶜ := by
  have hT0 : 0 < p.T := by linarith
  have hmeas : AEStronglyMeasurable (fun τ : ℝ =>
      (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|) volume := by
    apply AEStronglyMeasurable.mul
    · apply Finset.aestronglyMeasurable_fun_sum
      intro k _
      exact (psiA_shift_integrable hF (p.tau k)).aestronglyMeasurable
    · exact hνc.abs.aestronglyMeasurable
  have hnn : ∀ τ, 0 ≤ (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ| :=
    fun τ => mul_nonneg (Finset.sum_nonneg fun k _ => psiA_nonneg_of hF _) (abs_nonneg _)
  have hcompl : (p.I)ᶜ = Iio p.T ∪ Ioi (2 * p.T) := by
    ext x
    simp only [Setting.I, Zeta23.Iwin, Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi, not_and_or, not_le]
  rw [hcompl]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (((Mtot_integrable (B := B) hF hT0).comp_sub_left p.T).integrableOn)
      hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn τ)]
    exact dom_left hF hν hT0 hτ
  · refine Integrable.mono' (((Mtot_integrable (B := B) hF hT0).comp_sub_right (2 * p.T)).integrableOn)
      hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn τ)]
    exact dom_right hF hν hT0 hτ

/-- log(2T) = log(4π) + l ≤ l + 12. -/
lemma log_two_mul_T_le (hT : 0 < p.T) : Real.log (2 * p.T) ≤ p.l + 12 := by
  have h1 : 2 * p.T = (4 * π) * (p.T / (2 * π)) := by field_simp; ring
  have h4π : 0 < 4 * π := by positivity
  have h2 : Real.log (2 * p.T) = Real.log (4 * π) + p.l := by
    rw [h1, Real.log_mul h4π.ne' (by positivity)]
    rfl
  have h3 : Real.log (4 * π) ≤ 4 * π - 1 := Real.log_le_sub_one_of_pos h4π
  have h4 : π < 3.15 := Real.pi_lt_d2
  rw [h2]
  linarith

/-- **N2, raw form** (§5.3): the common core of `nu_grid_bound` / `nu_grid_bound_L` — the majorant
integrated on both half-lines, before the polynomial endgame:
  ∫_{τ∉I}|ν|σ ≤ 2·(B·(2 + 2L + (25/2)c_ϱL + c_ϱL²/2 + c_ϱLl) + L·c_ϱ·B),   any level B ≥ 8. -/
theorem nu_grid_bound_raw (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB8 : 8 ≤ B) (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + p.L * cϱ * B) := by
  have hl8 : 8 ≤ p.l := Setting.le_l_of_T hT
  have hT1 : 1 ≤ p.T := Setting.one_le_T (by norm_num) hT
  have hT0 : 0 < p.T := by linarith
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hc : (0:ℝ) ≤ cϱ := by linarith
  have hw1 := hF.one_le_w
  have hw : 0 < p.w := by linarith
  have hB : 0 ≤ B := by linarith
  -- the set-up
  have hint := integrableOn_sigma_mul_abs_nuX hνc hF hν hT1
  have hcompl : (p.I)ᶜ = Iio p.T ∪ Ioi (2 * p.T) := by
    ext x
    simp only [Setting.I, Zeta23.Iwin, Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi, not_and_or, not_le]
  rw [hcompl] at hint ⊢
  have hintL := hint.mono_set Set.subset_union_left
  have hintR := hint.mono_set Set.subset_union_right
  have hdisj : Disjoint (Iio p.T) (Ioi (2 * p.T)) :=
    Set.disjoint_left.mpr fun x hx hx' => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at hx hx'; linarith
  rw [setIntegral_union hdisj measurableSet_Ioi hintL hintR]
  -- each side ≤ ∫_0^∞ Mtot
  have hleft : ∫ τ in Iio p.T, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ ∫ Δ in Ioi 0, Mtot cϱ p B Δ := by
    calc ∫ τ in Iio p.T, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
        ≤ ∫ τ in Iio p.T, Mtot cϱ p B (p.T - τ) :=
          setIntegral_mono_on hintL ((Mtot_integrable (B := B) hF hT0).comp_sub_left p.T).integrableOn
            measurableSet_Iio (fun τ hτ => dom_left hF hν hT0 hτ)
      _ = ∫ Δ in Ioi 0, Mtot cϱ p B Δ := setIntegral_Iio_comp_sub_left _ _
  have hright : ∫ τ in Ioi (2 * p.T), (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ ∫ Δ in Ioi 0, Mtot cϱ p B Δ := by
    calc ∫ τ in Ioi (2 * p.T), (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
        ≤ ∫ τ in Ioi (2 * p.T), Mtot cϱ p B (τ - 2 * p.T) :=
          setIntegral_mono_on hintR ((Mtot_integrable (B := B) hF hT0).comp_sub_right (2 * p.T)).integrableOn
            measurableSet_Ioi (fun τ hτ => dom_right hF hν hT0 hτ)
      _ = ∫ Δ in Ioi 0, Mtot cϱ p B Δ := setIntegral_Ioi_comp_sub_right _ _
  -- the majorant's integral
  set Ψ' := ∫ r in Ioi 0, psiA cϱ p r with hΨ'
  have hΨ0 : 0 ≤ Ψ' := setIntegral_nonneg measurableSet_Ioi fun r _ => psiA_nonneg_of hF r
  have hM : ∫ Δ in Ioi 0, Mtot cϱ p B Δ
      ≤ B * (Ψ' + p.L / (2 * π) * (Ψ' + cϱ / p.w * Real.log (2 * p.T)))
        + p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by
    rw [integral_Mtot_eq hF hT0]
    exact add_le_add (integral_Mnear_le hF hB hT1) (integral_Mfar_le hF hB hT1)
  -- elementary bounds on the ingredients
  have hΨ1 : Ψ' ≤ 2 + cϱ * p.L / 2 := by
    have h1 : Ψ' ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w)) := hF.integral_psi_Ioi_le
    have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
    have h2 := Real.log_le_sub_one_of_pos harg
    have h3 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith
  have hlog := log_two_mul_T_le (p := p) hT0
  have hcw : cϱ / p.w ≤ cϱ := div_le_self hc hw1
  have hdT : p.d / p.T ≤ p.L := by
    rw [div_le_iff₀ hT0]
    have := p.d_le (by positivity : 0 ≤ p.L * p.T)
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, mul_pos hL hT0]
  have h2π : p.L / (2 * π) ≤ p.L := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have hB2 : B / 2 + 4 ≤ B := by linarith
  -- near ≤ B (Ψ₁ + L (Ψ₁ + c (l + 12))),  Ψ₁ = 2 + cL/2
  have hinner : Ψ' + cϱ / p.w * Real.log (2 * p.T) ≤ (2 + cϱ * p.L / 2) + cϱ * (p.l + 12) := by
    have hlog0 : 0 ≤ Real.log (2 * p.T) := Real.log_nonneg (by linarith)
    have : cϱ / p.w * Real.log (2 * p.T) ≤ cϱ * (p.l + 12) :=
      mul_le_mul hcw hlog hlog0 hc
    linarith
  have hinner0 : 0 ≤ Ψ' + cϱ / p.w * Real.log (2 * p.T) := by
    have hlog0 : 0 ≤ Real.log (2 * p.T) := Real.log_nonneg (by linarith)
    positivity
  have hnear : B * (Ψ' + p.L / (2 * π) * (Ψ' + cϱ / p.w * Real.log (2 * p.T)))
      ≤ B * ((2 + cϱ * p.L / 2) + p.L * ((2 + cϱ * p.L / 2) + cϱ * (p.l + 12))) := by
    refine mul_le_mul_of_nonneg_left (add_le_add hΨ1 ?_) hB
    exact mul_le_mul h2π hinner hinner0 hL.le
  have hfar : p.d / p.T * (cϱ / p.w) * (B / 2 + 4) ≤ p.L * cϱ * B := by
    apply mul_le_mul (mul_le_mul hdT hcw (by positivity) hL.le) hB2 (by positivity) (by positivity)
  -- polynomial endgame
  have hside : ∫ Δ in Ioi 0, Mtot cϱ p B Δ
      ≤ B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B := by
    refine hM.trans (add_le_add (hnear.trans (le_of_eq ?_)) hfar)
    ring
  linarith [hleft, hright, hside]

/-- **N2** (§5.3, "∫_{τ∉I}|ν_X|σ ≪ BLl", σ(τ) := Σ_{k<d} ψ(τ−τ_k))  (paper regime B ≥ l, L ≤ 2l). -/
theorem nu_grid_bound (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBl : p.l ≤ B) (hL2l : p.L ≤ 2 * p.l)
    (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ CN2 cϱ * (B * (p.L * p.l)) := by
  have hl8 : 8 ≤ p.l := Setting.le_l_of_T hT
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hc : (0:ℝ) ≤ cϱ := by linarith
  have hB : 0 ≤ B := by linarith
  have hLl : p.L ≤ 2 * p.l := hL2l
  have hpoly : 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B) ≤ 100 * (1 + cϱ) * (B * (p.L * p.l)) := by
    have hLl64 : 64 ≤ p.L * p.l := by
      have := mul_le_mul hL8 hl8 (by norm_num) hL.le; linarith
    have hL2 : p.L ^ 2 ≤ 2 * (p.L * p.l) := by
      rw [sq]; nlinarith [mul_le_mul_of_nonneg_left hLl hL.le]
    -- divide out B ≥ 0
    set M := p.L * p.l with hM
    have hcM : 0 ≤ cϱ * M := by positivity
    have e1 : (4:ℝ) ≤ M := by linarith
    have e2 : 4 * p.L ≤ M := by
      rw [hM]; nlinarith [mul_nonneg hL.le (by linarith : (0:ℝ) ≤ p.l - 4)]
    have e3 : 27 * cϱ * p.L ≤ 4 * (cϱ * M) := by
      have h27 : 27 * p.L ≤ 4 * M := by
        rw [hM]; nlinarith [mul_nonneg hL.le (by linarith : (0:ℝ) ≤ 4 * p.l - 27)]
      have := mul_le_mul_of_nonneg_left h27 hc
      linarith
    have e4 : cϱ * p.L ^ 2 ≤ cϱ * (2 * M) := mul_le_mul_of_nonneg_left hL2 hc
    have inner : 2 * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + 2 * (p.L * cϱ) ≤ 100 * (1 + cϱ) * M := by
      have : cϱ * p.L * p.l = cϱ * M := by rw [hM]; ring
      rw [this]
      have hM0 : 0 ≤ M := by linarith
      linarith [e1, e2, e3, e4, hcM, hM0]
    have := mul_le_mul_of_nonneg_left inner hB
    have eB : 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B)
        = B * (2 * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + 2 * (p.L * cϱ)) := by ring
    have eR : 100 * (1 + cϱ) * (B * (p.L * p.l)) = B * (100 * (1 + cϱ) * M) := by
      rw [hM]; ring
    rw [eB, eR]
    exact this
  have hCN2 : 100 * (1 + cϱ) ≤ CN2 cϱ := by
    rw [CN2_def, abs_of_nonneg hc]
    have := abs_nonneg (Real.log cϱ)
    nlinarith
  calc ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + p.L * cϱ * B) := nu_grid_bound_raw hνc hF hν (by linarith) hT
    _ ≤ 100 * (1 + cϱ) * (B * (p.L * p.l)) := hpoly
    _ ≤ CN2 cϱ * (B * (p.L * p.l)) :=
        mul_le_mul_of_nonneg_right hCN2 (by positivity)

/-- **N2, L-intrinsic form**: ∫_{τ∉I}|ν|σ ≤ CN2·B·L·(L + l)  (l = log(T/2π) carries the
genuine log T from the window geometry; no bandwidth cap, absorbing hypothesis `L ≤ B`). -/
theorem nu_grid_bound_L (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBL : p.L ≤ B)
    (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ CN2 cϱ * (B * (p.L * (p.L + p.l))) := by
  have hl8 : 8 ≤ p.l := Setting.le_l_of_T hT
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hc : (0:ℝ) ≤ cϱ := by linarith
  have hB : 0 ≤ B := by linarith
  have hpoly : 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B) ≤ 100 * (1 + cϱ) * (B * (p.L * (p.L + p.l))) := by
    set M := p.L * (p.L + p.l) with hM
    have hM128 : 128 ≤ M := by rw [hM]; nlinarith
    have hcM : 0 ≤ cϱ * M := by positivity
    have e1 : (4:ℝ) ≤ M := by linarith
    have e2 : 4 * p.L ≤ M := by rw [hM]; nlinarith
    have e3 : 27 * cϱ * p.L ≤ 4 * (cϱ * M) := by
      have h27 : 27 * p.L ≤ 4 * M := by rw [hM]; nlinarith
      have := mul_le_mul_of_nonneg_left h27 hc
      linarith
    have e4 : cϱ * p.L ^ 2 ≤ cϱ * M := by
      apply mul_le_mul_of_nonneg_left _ hc; rw [hM]; nlinarith
    have e5 : cϱ * p.L * p.l ≤ cϱ * M := by
      rw [hM, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hc; nlinarith
    have inner : 2 * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + 2 * (p.L * cϱ) ≤ 100 * (1 + cϱ) * M := by
      have hM0 : 0 ≤ M := by linarith
      nlinarith [e1, e2, e3, e4, e5, hcM, hM0]
    have := mul_le_mul_of_nonneg_left inner hB
    have eB : 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B)
        = B * (2 * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + 2 * (p.L * cϱ)) := by ring
    have eR : 100 * (1 + cϱ) * (B * (p.L * (p.L + p.l))) = B * (100 * (1 + cϱ) * M) := by
      rw [hM]; ring
    rw [eB, eR]
    exact this
  have hCN2 : 100 * (1 + cϱ) ≤ CN2 cϱ := by
    rw [CN2_def, abs_of_nonneg hc]
    have := abs_nonneg (Real.log cϱ)
    nlinarith
  calc ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + p.L * cϱ * B) := nu_grid_bound_raw hνc hF hν (by linarith) hT
    _ ≤ 100 * (1 + cϱ) * (B * (p.L * (p.L + p.l))) := hpoly
    _ ≤ CN2 cϱ * (B * (p.L * (p.L + p.l))) :=
        mul_le_mul_of_nonneg_right hCN2 (by positivity)

end PrimeSide
end Zeta23
