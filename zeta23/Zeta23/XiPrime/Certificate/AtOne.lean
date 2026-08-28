/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Certificate/AtOne.lean — the certified window constants at λ = 1.

[XF′ Thm 8.2 "Certified constants"]:  κ₁(1, v) = 1/c₁^{(1)}(v) = (∫v² + 𝒥_{D₁}(1;v))/(∫v)²  with the
FULL series D₁ (Defs.kappaXi) is sandwiched using  D1trunc 9 ≤ D₁ ≤ D1trunc 9 + ε₉ on [0,1]
(Certificate/D1.lean) and the exact rational values of Certificate/Poly.lean:
  flat     κ₉ = 100905635384/88388425125,                            κ₉ ≤ κ₁(1,vFlat)    ≤ κ₉ + ε₉,
  quartic  κ₉ = 277244140547469154168336/245053976636191319722125,    κ₉ ≤ κ₁(1,vQuartic) ≤ κ₉ + ε₉,
whence the SHARP certified decimals (the interface Props CertFlat/CertQuartic of
Statement.lean carry five digits and are discharged in Certificate.lean via continuity in λ):
  2 − κ₁(1,vFlat) ≥ 0.85838371,   3/2 − κ₁(1,vFlat)/2 ≥ 0.92919185,
  2 − κ₁(1,vQuartic) ≥ 0.86864017, 3/2 − κ₁(1,vQuartic)/2 ≥ 0.93432008   (eight digits; all margins ≥ 6·10⁻⁹
  in exact rational arithmetic).
The tail ε₉ enters with the sign that makes 1/c LARGER (the correct-side requirement for a lower bound).
-/
import Zeta23.XiPrime.Certificate.Poly

open scoped BigOperators
open Set intervalIntegral

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### generic λ = 1 algebra -/

theorem jWin_one (D v : ℝ → ℝ) : jWin D 1 v = 2 * ∫ r in (0:ℝ)..1, (D r * vConv v r) := by
  unfold jWin; simp only [one_mul]

theorem kappaXi_one (v : ℝ → ℝ) :
    kappaXi 1 v = ((∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + jWin D1 1 v)
      / (∫ s in (-(1:ℝ)/2)..(1/2), v s) ^ 2 := by
  unfold kappaXi cWin
  rw [one_mul, one_mul, one_div, inv_div]

/-- comparison of 𝒥 at λ = 1 under a pointwise bound with constant slack on [0,1]. -/
theorem jWin_one_le_of_le {D E w : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 1))
    (hE : ContinuousOn E (Icc 0 1)) (hw : ContinuousOn w (Icc 0 1))
    (hw0 : ∀ r ∈ Icc (0:ℝ) 1, 0 ≤ w r) {e : ℝ} (hle : ∀ r ∈ Icc (0:ℝ) 1, D r ≤ E r + e)
    {v : ℝ → ℝ} (hvw : ∀ r ∈ Icc (0:ℝ) 1, vConv v r = w r) :
    jWin D 1 v ≤ jWin E 1 v + e * (2 * ∫ r in (0:ℝ)..1, w r) := by
  rw [jWin_one, jWin_one]
  have h01 : uIcc (0:ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hcD : ∫ r in (0:ℝ)..1, D r * vConv v r = ∫ r in (0:ℝ)..1, D r * w r :=
    integral_congr fun r hr => by rw [h01] at hr; simp [hvw r hr]
  have hcE : ∫ r in (0:ℝ)..1, E r * vConv v r = ∫ r in (0:ℝ)..1, E r * w r :=
    integral_congr fun r hr => by rw [h01] at hr; simp [hvw r hr]
  rw [hcD, hcE]
  have hiD : IntervalIntegrable (fun r => D r * w r) MeasureTheory.volume 0 1 :=
    (hD.mul hw).intervalIntegrable_of_Icc zero_le_one
  have hiE : IntervalIntegrable (fun r => E r * w r) MeasureTheory.volume 0 1 :=
    (hE.mul hw).intervalIntegrable_of_Icc zero_le_one
  have hiw : IntervalIntegrable w MeasureTheory.volume 0 1 := hw.intervalIntegrable_of_Icc zero_le_one
  have hmono : ∫ r in (0:ℝ)..1, D r * w r ≤ ∫ r in (0:ℝ)..1, (E r * w r + e * w r) := by
    apply intervalIntegral.integral_mono_on zero_le_one hiD (hiE.add (hiw.const_mul e))
    intro r hr
    have := mul_le_mul_of_nonneg_right (hle r hr) (hw0 r hr)
    linarith [this, add_mul (E r) e (w r)]
  rw [intervalIntegral.integral_add hiE (hiw.const_mul e), intervalIntegral.integral_const_mul] at hmono
  linarith

/-! ### 2∫₀¹(v⋆v) = (∫v)² for the two windows (Fubini instances, by direct evaluation) -/

theorem two_integral_vConv_vFlat : 2 * ∫ r in (0:ℝ)..1, (1 - r) = (1:ℝ) := by
  have h : (fun r : ℝ => 1 - r) = polyEval [1, -1] := by
    ext r; simp [polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]; simp [polyInt, Finset.sum_range_succ]; norm_num

theorem two_integral_convQ : 2 * ∫ r in (0:ℝ)..1, convQ r = (2777 / 3000 : ℝ) ^ 2 := by
  have h : (fun r : ℝ => convQ r)
      = polyEval [518783/600000, -729/1600, -522523/262500, 7082/1875, -47209/12500, 30551/18750,
          0, -68/3125, 0, -578/21875] := by
    ext r; simp [convQ, polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]; simp [polyInt, Finset.sum_range_succ]; norm_num

/-! ### the sandwich for the two windows -/

/-- the flat κ₉. -/
def kap9Flat : ℝ := 100905635384 / 88388425125
/-- the quartic κ₉. -/
def kap9Quartic : ℝ := 277244140547469154168336 / 245053976636191319722125

theorem jWin_D1_one_vFlat_le : jWin D1 1 vFlat ≤ 12517210259 / 88388425125 + eps9 := by
  have h := jWin_one_le_of_le (v := vFlat) (w := fun r => 1 - r) (continuousOn_D1 _)
    (continuous_D1trunc 9).continuousOn (by fun_prop) (fun r hr => by linarith [hr.2])
    (e := eps9) (fun r hr => D1_le_D1trunc9_add hr.1 hr.2) (fun r _ => vConv_vFlat r)
  rw [jWin_trunc9_vFlat, two_integral_vConv_vFlat, mul_one] at h
  exact h

theorem le_jWin_D1_one_vFlat : 12517210259 / 88388425125 ≤ jWin D1 1 vFlat := by
  have h := jWin_one_le_of_le (v := vFlat) (w := fun r => 1 - r)
    (continuous_D1trunc 9).continuousOn (continuousOn_D1 _) (by fun_prop)
    (fun r hr => by linarith [hr.2]) (e := 0)
    (fun r hr => by linarith [D1trunc_le_D1 9 hr.1]) (fun r _ => vConv_vFlat r)
  rw [jWin_trunc9_vFlat] at h
  linarith

theorem jWin_D1_one_vQuartic_le :
    jWin D1 1 vQuartic ≤ 29965280330934234270211 / 285991090937677125000000
      + eps9 * (2777 / 3000 : ℝ) ^ 2 := by
  have h := jWin_one_le_of_le (v := vQuartic) (w := convQ) (continuousOn_D1 _)
    (continuous_D1trunc 9).continuousOn (by unfold convQ; fun_prop) (fun r hr => convQ_nonneg hr)
    (e := eps9) (fun r hr => D1_le_D1trunc9_add hr.1 hr.2) (fun r _ => vConv_vQuartic r)
  rw [jWin_trunc9_vQuartic, two_integral_convQ] at h
  exact h

theorem le_jWin_D1_one_vQuartic :
    29965280330934234270211 / 285991090937677125000000 ≤ jWin D1 1 vQuartic := by
  have h := jWin_one_le_of_le (v := vQuartic) (w := convQ)
    (continuous_D1trunc 9).continuousOn (continuousOn_D1 _) (by unfold convQ; fun_prop)
    (fun r hr => convQ_nonneg hr) (e := 0)
    (fun r hr => by linarith [D1trunc_le_D1 9 hr.1]) (fun r _ => vConv_vQuartic r)
  rw [jWin_trunc9_vQuartic] at h
  linarith

/-- **flat window:** κ₉ ≤ κ₁(1, vFlat) ≤ κ₉ + ε₉. -/
theorem kappaXi_one_vFlat_mem : kappaXi 1 vFlat ∈ Icc kap9Flat (kap9Flat + eps9) := by
  rw [kappaXi_one, integral_vFlat, integral_vFlat_sq]
  unfold kap9Flat
  constructor
  · have := le_jWin_D1_one_vFlat; norm_num at this ⊢; linarith
  · have := jWin_D1_one_vFlat_le; norm_num at this ⊢; linarith

/-- **quartic window:** κ₉ ≤ κ₁(1, vQuartic) ≤ κ₉ + ε₉. -/
theorem kappaXi_one_vQuartic_mem :
    kappaXi 1 vQuartic ∈ Icc kap9Quartic (kap9Quartic + eps9) := by
  rw [kappaXi_one, integral_vQuartic, integral_vQuartic_sq]
  unfold kap9Quartic
  have ha : (0:ℝ) < (2777 / 3000 : ℝ) ^ 2 := by norm_num
  constructor
  · rw [le_div_iff₀ ha]
    have := le_jWin_D1_one_vQuartic; norm_num at this ⊢; linarith
  · rw [div_le_iff₀ ha]
    have := jWin_D1_one_vQuartic_le; norm_num at this ⊢; linarith

theorem kappaXi_one_vFlat_le : kappaXi 1 vFlat ≤ kap9Flat + eps9 := kappaXi_one_vFlat_mem.2
theorem kappaXi_one_vQuartic_le : kappaXi 1 vQuartic ≤ kap9Quartic + eps9 :=
  kappaXi_one_vQuartic_mem.2

/-! ### the sharp certified decimals at λ = 1 -/

/-- **2 − κ₁(1, flat) ≥ 0.85838371**  [XF′: "≥ 0.858383"]. -/
theorem cert_flat_one : (0.85838371 : ℝ) ≤ 2 - kappaXi 1 vFlat := by
  have h := kappaXi_one_vFlat_le; unfold kap9Flat eps9 at h; norm_num at h ⊢; linarith

/-- **3/2 − κ₁(1, flat)/2 ≥ 0.92919185**  [XF′: "≥ 0.929191"]. -/
theorem cert_flat_dist_one : (0.92919185 : ℝ) ≤ 3 / 2 - kappaXi 1 vFlat / 2 := by
  have h := kappaXi_one_vFlat_le; unfold kap9Flat eps9 at h; norm_num at h ⊢; linarith

/-- **2 − κ₁(1, quartic) ≥ 0.86864017**  [XF′: "≥ 0.868640"]. -/
theorem cert_quartic_one : (0.86864017 : ℝ) ≤ 2 - kappaXi 1 vQuartic := by
  have h := kappaXi_one_vQuartic_le; unfold kap9Quartic eps9 at h; norm_num at h ⊢; linarith

/-- **3/2 − κ₁(1, quartic)/2 ≥ 0.93432008**  [XF′: "≥ 0.934320"]. -/
theorem cert_quartic_dist_one : (0.93432008 : ℝ) ≤ 3 / 2 - kappaXi 1 vQuartic / 2 := by
  have h := kappaXi_one_vQuartic_le; unfold kap9Quartic eps9 at h; norm_num at h ⊢; linarith

/-- strict forms at the FIVE-decimal interface constants (used with continuity in λ to produce
CertFlat / CertQuartic of Statement.lean). -/
theorem cert_flat_one_strict :
    (0.85838 : ℝ) < 2 - kappaXi 1 vFlat ∧ (0.92919 : ℝ) < 3 / 2 - kappaXi 1 vFlat / 2 := by
  constructor <;> linarith [cert_flat_one, cert_flat_dist_one]

theorem cert_quartic_one_strict :
    (0.86864 : ℝ) < 2 - kappaXi 1 vQuartic ∧ (0.93432 : ℝ) < 3 / 2 - kappaXi 1 vQuartic / 2 := by
  constructor <;> linarith [cert_quartic_one, cert_quartic_dist_one]

end XiPrime
end Zeta23
