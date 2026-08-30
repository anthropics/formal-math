/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Certificate/Poly.lean — exact rational evaluation of the window integrals for the two
certificate windows ("Certified constants").

  vConv vFlat r = 1 − r,            ∫vFlat = ∫vFlat² = 1,
  vConv vQuartic r = explicit degree-9 polynomial,  ∫vQuartic = 2777/3000,  ∫vQuartic² = 518783/600000,
  jWin (D1trunc 9) 1 vFlat    = 12517210259/88388425125,
  jWin (D1trunc 9) 1 vQuartic = 29965280330934234270211/285991090937677125000000.

Device: a polynomial given by a coefficient list integrates to a finite rational sum
(polyEval / polyInt); every closed form is computer-algebra-generated
and Lean-checked by ring / norm_num.
-/
import Zeta23.XiPrime.Certificate.D1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators
open Set intervalIntegral

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### polynomial interval integrals via coefficient lists -/

/-- evaluate a coefficient list as a polynomial: Σ_k c[k]·x^k. -/
def polyEval (c : List ℝ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range c.length, c.getD k 0 * x ^ k

/-- its interval integral: Σ_k c[k]·(b^{k+1} − a^{k+1})/(k+1). -/
def polyInt (c : List ℝ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range c.length, c.getD k 0 * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1))

theorem integral_polyEval (c : List ℝ) (a b : ℝ) :
    ∫ x in a..b, polyEval c x = polyInt c a b := by
  unfold polyEval polyInt
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
  · intro k _
    exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _

/-! ### D1trunc 9 written out -/

/-- the degree-19 polynomial D1trunc 9 with its rational coefficients. -/
def T9 (r : ℝ) : ℝ :=
  r - 4 * r ^ 2 + 4 * r ^ 3 + 4 / 3 * r ^ 5 + 16 / 45 * r ^ 7 + 8 / 105 * r ^ 9
    + 64 / 4725 * r ^ 11 + 64 / 31185 * r ^ 13 + 256 / 945945 * r ^ 15 + 64 / 2027025 * r ^ 17
    + 1024 / 310134825 * r ^ 19

theorem D1trunc9_eq (r : ℝ) : D1trunc 9 r = T9 r := by
  simp only [D1trunc, D1coeff, T9, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    Nat.cast_ofNat, Nat.cast_mul, Nat.cast_succ]
  norm_num
  ring

/-! ### the flat window -/

theorem vConv_vFlat (r : ℝ) : vConv vFlat r = 1 - r := by
  simp [vConv, vFlat]
  ring

theorem integral_vFlat : ∫ s in (-(1:ℝ)/2)..(1/2), vFlat s = 1 := by
  simp [vFlat]; norm_num

theorem integral_vFlat_sq : ∫ s in (-(1:ℝ)/2)..(1/2), vFlat s ^ 2 = 1 := by
  simp [vFlat]; norm_num

/-- coefficients of r ↦ T9(r)·(1 − r). -/
def prodFlat : List ℝ :=
  [0, 1, -5, 8, -4, 4/3, -4/3, 16/45, -16/45, 8/105, -8/105, 64/4725, -64/4725, 64/31185,
    -64/31185, 256/945945, -256/945945, 64/2027025, -64/2027025, 1024/310134825, -1024/310134825]

theorem T9_mul_flat_eq : (fun r => T9 r * (1 - r)) = polyEval prodFlat := by
  ext r
  simp [T9, polyEval, prodFlat, Finset.sum_range_succ]
  ring

/-- ∫₀¹ D1trunc 9 (r)·(1 − r) dr, exactly. -/
theorem integral_T9_flat : ∫ r in (0:ℝ)..1, T9 r * (1 - r) = 12517210259 / 176776850250 := by
  rw [show (fun r => T9 r * (1 - r)) = polyEval prodFlat from T9_mul_flat_eq, integral_polyEval]
  simp [polyInt, prodFlat, Finset.sum_range_succ]
  norm_num

theorem jWin_trunc9_vFlat : jWin (D1trunc 9) 1 vFlat = 12517210259 / 88388425125 := by
  unfold jWin
  have h : (fun r => D1trunc 9 (1 * r) * vConv vFlat r) = fun r => T9 r * (1 - r) := by
    ext r; rw [one_mul, D1trunc9_eq, vConv_vFlat]
  rw [h, integral_T9_flat]
  norm_num

/-! ### the quartic window v(s) = 1 − (7/100)(2s)² − (51/200)(2s)⁴ -/

theorem vQuartic_eq (s : ℝ) : vQuartic s = 1 - 7 / 25 * s ^ 2 - 102 / 25 * s ^ 4 := by
  unfold vQuartic; ring

theorem integral_vQuartic : ∫ s in (-(1:ℝ)/2)..(1/2), vQuartic s = 2777 / 3000 := by
  have h : (fun s => vQuartic s) = polyEval [1, 0, -7/25, 0, -102/25] := by
    ext s; simp [vQuartic_eq, polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, Finset.sum_range_succ]
  norm_num

theorem integral_vQuartic_sq : ∫ s in (-(1:ℝ)/2)..(1/2), vQuartic s ^ 2 = 518783 / 600000 := by
  have h : (fun s => vQuartic s ^ 2)
      = polyEval [1, 0, -14/25, 0, -5051/625, 0, 1428/625, 0, 10404/625] := by
    ext s; simp [vQuartic_eq, polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, Finset.sum_range_succ]
  norm_num

/-- closed form of (v⋆v)(r) for the quartic window (degree 9 in r; valid for every real r). -/
def convQ (r : ℝ) : ℝ :=
  518783 / 600000 - 729 / 1600 * r - 522523 / 262500 * r ^ 2 + 7082 / 1875 * r ^ 3
    - 47209 / 12500 * r ^ 4 + 30551 / 18750 * r ^ 5 - 68 / 3125 * r ^ 7 - 578 / 21875 * r ^ 9

/-- the coefficients of s ↦ v(s)·v(s+r). -/
def coeffS (r : ℝ) : List ℝ :=
  [-102 * r ^ 4 / 25 - 7 * r ^ 2 / 25 + 1,
    -408 * r ^ 3 / 25 - 14 * r / 25,
    714 * r ^ 4 / 625 - 15251 * r ^ 2 / 625 - 14 / 25,
    2856 * r ^ 3 / 625 - 10102 * r / 625,
    10404 * r ^ 4 / 625 + 4998 * r ^ 2 / 625 - 5051 / 625,
    41616 * r ^ 3 / 625 + 4284 * r / 625,
    62424 * r ^ 2 / 625 + 1428 / 625,
    41616 * r / 625,
    10404 / 625]

theorem vConv_vQuartic (r : ℝ) : vConv vQuartic r = convQ r := by
  unfold vConv
  have h : (fun s => vQuartic s * vQuartic (s + r)) = polyEval (coeffS r) := by
    ext s; simp [vQuartic_eq, polyEval, coeffS, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, coeffS, Finset.sum_range_succ, convQ]
  ring

/-- coefficients of r ↦ T9(r)·convQ(r) (degree 28). -/
def prodQuartic : List ℝ :=
  [0, 518783/600000, -2348507/600000, 1727507/525000, 10412663/1050000, -80937331/3150000,
    937111/30000, -283158439/11812500, 1279111/112500, -18867821/3375000, 15910471/4725000,
    -427006369/310078125, 2144671/2953125, -3202160069/10232578125, 2561099/19490625,
    -7317191036/133023515625, 2480296796/133023515625, -591808741/71628046875,
    38839601/19003359375, -22023206368/20352597890625, 353129072/2261399765625,
    -512137232/4070519578125, 1004576/264319453125, -710912/57010078125,
    -350177024/142468185234375, 0, -14464/15962821875, 0, -34816/399070546875]

theorem T9_mul_convQ_eq : (fun r => T9 r * convQ r) = polyEval prodQuartic := by
  ext r
  simp [T9, convQ, polyEval, prodQuartic, Finset.sum_range_succ]
  ring

/-- ∫₀¹ D1trunc 9 (r)·(v⋆v)(r) dr for the quartic window, exactly. -/
theorem integral_T9_quartic :
    ∫ r in (0:ℝ)..1, T9 r * convQ r = 29965280330934234270211 / 571982181875354250000000 := by
  rw [show (fun r => T9 r * convQ r) = polyEval prodQuartic from T9_mul_convQ_eq, integral_polyEval]
  simp [polyInt, prodQuartic, Finset.sum_range_succ]
  norm_num

theorem jWin_trunc9_vQuartic :
    jWin (D1trunc 9) 1 vQuartic = 29965280330934234270211 / 285991090937677125000000 := by
  unfold jWin
  have h : (fun r => D1trunc 9 (1 * r) * vConv vQuartic r) = fun r => T9 r * convQ r := by
    ext r; rw [one_mul, D1trunc9_eq, vConv_vQuartic]
  rw [h, integral_T9_quartic]
  norm_num

/-! ### positivity / range / continuity facts of the two profiles -/

theorem vQuartic_le_one (s : ℝ) : vQuartic s ≤ 1 := by
  rw [vQuartic_eq]; nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]

/-- min over [−1/2,1/2] is 27/40, at the endpoints (v is decreasing in s²). -/
theorem vQuartic_ge {s : ℝ} (hs : s ∈ Icc (-(1/2 : ℝ)) (1/2)) : 27 / 40 ≤ vQuartic s := by
  rw [vQuartic_eq]
  have h2 : s ^ 2 ≤ 1 / 4 := by nlinarith [hs.1, hs.2]
  have h4 : s ^ 4 ≤ 1 / 16 := by nlinarith [sq_nonneg s]
  nlinarith

theorem vQuartic_pos {s : ℝ} (hs : s ∈ Icc (-(1/2 : ℝ)) (1/2)) : 0 < vQuartic s :=
  lt_of_lt_of_le (by norm_num) (vQuartic_ge hs)

theorem vQuartic_even (s : ℝ) : vQuartic (-s) = vQuartic s := by
  unfold vQuartic; ring

theorem continuous_vQuartic : Continuous vQuartic := by unfold vQuartic; fun_prop

theorem vQuartic_nonneg_on {s : ℝ} (hs : s ∈ Icc (-(1:ℝ)/2) (1/2)) : 0 ≤ vQuartic s :=
  (vQuartic_pos ⟨by linarith [hs.1], hs.2⟩).le

theorem continuous_vFlat : Continuous vFlat := continuous_const

theorem vFlat_nonneg (s : ℝ) : 0 ≤ vFlat s := by simp [vFlat]

theorem convQ_nonneg {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : 0 ≤ convQ r := by
  -- (v⋆v)(r) is an integral of a product of positive functions over an interval of length 1 − r ≥ 0
  rw [← vConv_vQuartic]
  unfold vConv
  apply intervalIntegral.integral_nonneg (by linarith [hr.2])
  intro s hs
  have hs' : s ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨by linarith [hs.1], by linarith [hs.2, hr.1]⟩
  have hsr : s + r ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨by linarith [hs.1, hr.1], by linarith [hs.2]⟩
  exact mul_nonneg (vQuartic_pos hs').le (vQuartic_pos hsr).le

end XiPrime
end Zeta23
