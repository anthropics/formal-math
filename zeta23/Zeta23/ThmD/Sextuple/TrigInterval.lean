/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Interval
import Mathlib.Analysis.Real.Pi.Bounds

open Finset

noncomputable section

namespace Complex

private theorem cos_bound_14_sextuple {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
      - x ^ 10 / 3628800 + x ^ 12 / 479001600)‖ ≤
      ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  calc
    ‖cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
      - x ^ 10 / 3628800 + x ^ 12 / 479001600)‖ =
        ‖(exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial) / 2 +
         (exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial) / 2‖ := by
      simp [cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ ≤ ‖exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ ≤ ‖-x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (n := 14) (by simpa) (by norm_num),
        Complex.exp_bound (n := 14) (by simpa) (by norm_num)]
    _ = ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by norm_num

private theorem sin_bound_14_sextuple {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
      - x ^ 11 / 39916800 + x ^ 13 / 6227020800)‖ ≤
      ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  calc
    ‖sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
      - x ^ 11 / 39916800 + x ^ 13 / 6227020800)‖ =
        ‖(exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial) * I / 2 -
         (exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial) * I / 2‖ := by
      simp [sin, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ ≤ ‖exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_sub_le]
      simp
    _ ≤ ‖-x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (n := 14) (by simpa) (by norm_num),
        Complex.exp_bound (n := 14) (by simpa) (by norm_num)]
    _ = ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by norm_num

end Complex

namespace Real

private theorem cos_bound_14_sextuple {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
      - x ^ 10 / 3628800 + x ^ 12 / 479001600)| ≤
      |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  simpa [← Complex.ofReal_cos, ← norm_eq_abs, ← Complex.norm_real] using
    Complex.cos_bound_14_sextuple (x := (x : ℂ)) (by simpa)

private theorem sin_bound_14_sextuple {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
      - x ^ 11 / 39916800 + x ^ 13 / 6227020800)| ≤
      |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  simpa [← Complex.ofReal_sin, ← norm_eq_abs, ← Complex.norm_real] using
    Complex.sin_bound_14_sextuple (x := (x : ℂ)) (by simpa)

end Real

namespace Zeta23.ThmD.Sextuple

open RatInterval

/-- Degree-13 Taylor polynomial for sine, evaluated exactly in `ℚ`. -/
def sinPoly (x : ℚ) : ℚ :=
  x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 + x^13/6227020800

/-- Degree-12 Taylor polynomial for cosine, evaluated exactly in `ℚ`. -/
def cosPoly (x : ℚ) : ℚ :=
  1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 + x^12/479001600

/-- The common degree-14 Taylor remainder bound. -/
def trigError (x : ℚ) : ℚ := |x|^14 * (15 / (Nat.factorial 14 * 14))

def sinPoint (x : ℚ) : RatInterval := ⟨sinPoly x - trigError x, sinPoly x + trigError x⟩
def cosPoint (x : ℚ) : RatInterval := ⟨cosPoly x - trigError x, cosPoly x + trigError x⟩

def widen (i : RatInterval) (r : ℚ) : RatInterval := ⟨i.lo-r, i.hi+r⟩

lemma holds_widen {i : RatInterval} {x y : ℝ} {r : ℚ} (_hr : 0 ≤ r)
    (hx : Holds i x) (hxy : |y-x| ≤ r) : Holds (widen i r) y := by
  simp only [Holds, widen, Rat.cast_sub, Rat.cast_add] at hx ⊢
  have := abs_le.mp hxy
  constructor <;> linarith

lemma holds_sinPoint (x : ℚ) (hx : |x| ≤ 1) : Holds (sinPoint x) (Real.sin (x : ℝ)) := by
  have h := Real.sin_bound_14_sextuple (x := (x : ℝ)) (by exact_mod_cast hx)
  rw [show (x : ℝ) - (x : ℝ)^3/6 + (x : ℝ)^5/120 - (x : ℝ)^7/5040 +
      (x : ℝ)^9/362880 - (x : ℝ)^11/39916800 + (x : ℝ)^13/6227020800 =
      (sinPoly x : ℚ) by simp [sinPoly]] at h
  change ((sinPoly x - trigError x : ℚ) : ℝ) ≤ Real.sin (x : ℝ) ∧
    Real.sin (x : ℝ) ≤ ((sinPoly x + trigError x : ℚ) : ℝ)
  rw [abs_le] at h
  have herr : ((trigError x : ℚ) : ℝ) = |(x : ℝ)|^14 *
      ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
    simp [trigError]
  rw [Rat.cast_sub, Rat.cast_add, herr]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma holds_cosPoint (x : ℚ) (hx : |x| ≤ 1) : Holds (cosPoint x) (Real.cos (x : ℝ)) := by
  have h := Real.cos_bound_14_sextuple (x := (x : ℝ)) (by exact_mod_cast hx)
  rw [show 1 - (x : ℝ)^2/2 + (x : ℝ)^4/24 - (x : ℝ)^6/720 +
      (x : ℝ)^8/40320 - (x : ℝ)^10/3628800 + (x : ℝ)^12/479001600 =
      (cosPoly x : ℚ) by simp [cosPoly]] at h
  change ((cosPoly x - trigError x : ℚ) : ℝ) ≤ Real.cos (x : ℝ) ∧
    Real.cos (x : ℝ) ≤ ((cosPoly x + trigError x : ℚ) : ℝ)
  rw [abs_le] at h
  have herr : ((trigError x : ℚ) : ℝ) = |(x : ℝ)|^14 *
      ((15 : ℝ) / (Nat.factorial 14 * 14)) := by simp [trigError]
  rw [Rat.cast_sub, Rat.cast_add, herr]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Exact twenty-decimal rational enclosure used only for range reduction. -/
def piInterval : RatInterval :=
  ⟨314159265358979323846 / 10^20, 314159265358979323847 / 10^20⟩

theorem pi_mem : Holds piInterval Real.pi := by
  simp only [Holds, piInterval, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  constructor
  · calc
      (314159265358979323846 / 10^20 : ℝ) = 3.14159265358979323846 := by norm_num
      _ ≤ Real.pi := Real.pi_gt_d20.le
  · calc
      Real.pi ≤ 3.14159265358979323847 := Real.pi_lt_d20.le
      _ = (314159265358979323847 / 10^20 : ℝ) := by norm_num

/-- Rotate a sine/cosine interval pair by `n` quarter turns. -/
def quarterTurn : ℕ → RatInterval × RatInterval → RatInterval × RatInterval
  | 0, z => z
  | n+1, z => quarterTurn n (z.2, neg z.1)

lemma quarterTurn_sound (n : ℕ) (r : ℝ) {si ci : RatInterval}
    (hs : Holds si (Real.sin r)) (hc : Holds ci (Real.cos r)) :
    Holds (quarterTurn n (si,ci)).1 (Real.sin (n * Real.pi / 2 + r)) ∧
      Holds (quarterTurn n (si,ci)).2 (Real.cos (n * Real.pi / 2 + r)) := by
  induction n generalizing r si ci with
  | zero =>
      simpa only [quarterTurn, Nat.cast_zero, zero_mul, zero_div, zero_add] using And.intro hs hc
  | succ n ih =>
      have hs' : Holds ci (Real.sin (Real.pi / 2 + r)) := by
        simpa [Real.sin_add] using hc
      have hc' : Holds (neg si) (Real.cos (Real.pi / 2 + r)) := by
        simpa [Real.cos_add] using holds_neg hs
      have h := ih (r := Real.pi / 2 + r) hs' hc'
      have hang : ((n + 1 : ℕ) : ℝ) * Real.pi / 2 + r =
          n * Real.pi / 2 + (Real.pi / 2 + r) := by
        push_cast
        ring
      simpa only [quarterTurn, hang] using h

/-- Rational midpoint of the reduced angle for a rational point and a chosen quarter turn. -/
def reducedMid (x : ℚ) (n : ℕ) : ℚ :=
  x - n * (piInterval.lo + piInterval.hi) / 4

def reducedRadius (n : ℕ) : ℚ := n * (piInterval.hi - piInterval.lo) / 4

/-- Sine/cosine enclosure at a rational point, using a supplied quarter-turn index. -/
def trigPoint (x : ℚ) (n : ℕ) : RatInterval × RatInterval :=
  let r := reducedMid x n
  let e := reducedRadius n
  quarterTurn n (widen (sinPoint r) e, widen (cosPoint r) e)

lemma trigPoint_sound (x : ℚ) (n : ℕ) (hr : |reducedMid x n| ≤ 1) :
    Holds (trigPoint x n).1 (Real.sin (x : ℝ)) ∧
      Holds (trigPoint x n).2 (Real.cos (x : ℝ)) := by
  let r : ℝ := (x : ℝ) - n * Real.pi / 2
  let m : ℚ := reducedMid x n
  let e : ℚ := reducedRadius n
  have he : 0 ≤ e := by
    dsimp [e, reducedRadius, piInterval]
    positivity
  have hrm : |r - (m : ℝ)| ≤ (e : ℝ) := by
    have hp := pi_mem
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hplo := mul_le_mul_of_nonneg_left hp.1 hn
    have hphi := mul_le_mul_of_nonneg_left hp.2 hn
    dsimp [r, m, e, reducedMid, reducedRadius, piInterval]
    simp only [Holds, piInterval] at hp hplo hphi
    rw [abs_le]
    push_cast at hplo hphi ⊢
    norm_num at hplo hphi ⊢
    constructor <;> nlinarith
  have hsinm := holds_sinPoint m hr
  have hcosm := holds_cosPoint m hr
  have hsinr : Holds (widen (sinPoint m) e) (Real.sin r) :=
    holds_widen he hsinm ((Real.abs_sin_sub_sin_le r (m : ℝ)).trans (by simpa [abs_sub_comm] using hrm))
  have hcosr : Holds (widen (cosPoint m) e) (Real.cos r) :=
    holds_widen he hcosm ((Real.abs_cos_sub_cos_le r (m : ℝ)).trans (by simpa [abs_sub_comm] using hrm))
  have hturn := quarterTurn_sound n r hsinr hcosr
  have hx : (x : ℝ) = n * Real.pi / 2 + r := by simp [r]
  rw [hx]
  simpa [trigPoint, m, e] using hturn

/-- Enclose sine and cosine over an input interval, starting from its rational midpoint. -/
def trigRange (i : RatInterval) (n : ℕ) : RatInterval × RatInterval :=
  let m := (i.lo+i.hi)/2
  let r := (i.hi-i.lo)/2
  (widen (trigPoint m n).1 r, widen (trigPoint m n).2 r)

lemma trigRange_sound {i : RatInterval} {x : ℝ} (n : ℕ) (hi : i.lo ≤ i.hi)
    (hr : |reducedMid ((i.lo+i.hi)/2) n| ≤ 1) (hx : Holds i x) :
    Holds (trigRange i n).1 (Real.sin x) ∧ Holds (trigRange i n).2 (Real.cos x) := by
  let m : ℚ := (i.lo+i.hi)/2
  let r : ℚ := (i.hi-i.lo)/2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hxm : |x-(m : ℝ)| ≤ (r : ℝ) := by
    dsimp [m,r]
    simp only [Holds] at hx
    rw [abs_le]
    push_cast
    constructor <;> linarith
  obtain ⟨hs,hc⟩ := trigPoint_sound m n hr
  constructor
  · exact holds_widen hr0 hs ((Real.abs_sin_sub_sin_le x (m : ℝ)).trans hxm)
  · exact holds_widen hr0 hc ((Real.abs_cos_sub_cos_le x (m : ℝ)).trans hxm)

end Zeta23.ThmD.Sextuple
