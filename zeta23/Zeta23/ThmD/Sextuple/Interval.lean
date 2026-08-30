/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

noncomputable section

namespace Zeta23.ThmD.Sextuple

/-- A closed interval with exact rational endpoints. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RatInterval

/-- A real number is enclosed by a rational interval. -/
def Holds (i : RatInterval) (x : ℝ) : Prop := (i.lo : ℝ) ≤ x ∧ x ≤ (i.hi : ℝ)

@[simp] theorem holds_point (q : ℚ) : Holds ⟨q, q⟩ (q : ℝ) := ⟨le_rfl, le_rfl⟩

def add (i j : RatInterval) : RatInterval := ⟨i.lo + j.lo, i.hi + j.hi⟩
def neg (i : RatInterval) : RatInterval := ⟨-i.hi, -i.lo⟩
def sub (i j : RatInterval) : RatInterval := add i (neg j)
def scale (q : ℚ) (i : RatInterval) : RatInterval :=
  if 0 ≤ q then ⟨q * i.lo, q * i.hi⟩ else ⟨q * i.hi, q * i.lo⟩

/-- Exact interval product using the four corner values. -/
def mul (i j : RatInterval) : RatInterval :=
  ⟨min (min (i.lo * j.lo) (i.lo * j.hi)) (min (i.hi * j.lo) (i.hi * j.hi)),
   max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi))⟩

def sq (i : RatInterval) : RatInterval := mul i i

/-- Reciprocal of a strictly positive interval.  Callers check `0 < lo`. -/
def invPos (i : RatInterval) : RatInterval := ⟨i.hi⁻¹, i.lo⁻¹⟩
def divPos (i j : RatInterval) : RatInterval := mul i (invPos j)

lemma holds_add {i j : RatInterval} {x y : ℝ} (hx : Holds i x) (hy : Holds j y) :
    Holds (add i j) (x + y) := by
  simp only [Holds, add, Rat.cast_add] at hx hy ⊢
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

lemma holds_neg {i : RatInterval} {x : ℝ} (hx : Holds i x) : Holds (neg i) (-x) := by
  simp only [Holds, neg, Rat.cast_neg] at hx ⊢
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

lemma holds_sub {i j : RatInterval} {x y : ℝ} (hx : Holds i x) (hy : Holds j y) :
    Holds (sub i j) (x - y) := by
  simpa [sub_eq_add_neg, sub] using holds_add hx (holds_neg hy)

lemma holds_scale {q : ℚ} {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    Holds (scale q i) ((q : ℝ) * x) := by
  simp only [scale]
  split_ifs with hq
  · simp only [Holds, Rat.cast_mul] at hx ⊢
    exact ⟨mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hq),
      mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast hq)⟩
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hq
    simp only [Holds, Rat.cast_mul] at hx ⊢
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hq', mul_le_mul_of_nonpos_left hx.1 hq'⟩

private lemma mul_aux {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hLac : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hLad : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hLbc : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hLbd : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hUac : a*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hUad : a*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hUbc : b*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hUbd : b*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxa : 0 ≤ x-a := sub_nonneg.mpr hx.1
  have hbx : 0 ≤ b-x := sub_nonneg.mpr hx.2
  have hyc : 0 ≤ y-c := sub_nonneg.mpr hy.1
  have hdy : 0 ≤ d-y := sub_nonneg.mpr hy.2
  rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
  · constructor
    · rcases le_total 0 a with ha0 | ha0
      · apply hLac.trans
        nlinarith [mul_nonneg hxa hy0, mul_nonneg ha0 hyc]
      · apply hLad.trans
        have hd0 : 0 ≤ d := hy0.trans hy.2
        nlinarith [mul_nonpos_of_nonpos_of_nonneg ha0 hd0, mul_nonneg hx0 hy0]
    · apply le_trans ?_ hUbd
      have hd0 : 0 ≤ d := hy0.trans hy.2
      nlinarith [mul_nonneg hbx hd0, mul_nonneg hx0 hdy]
  · constructor
    · apply hLbc.trans
      have hb0 : 0 ≤ b := hx0.trans hx.2
      have hc0 : c ≤ 0 := hy.1.trans hy0
      nlinarith [mul_nonneg hbx (neg_nonneg.mpr hc0), mul_nonneg hx0 hyc]
    · rcases le_total 0 a with ha0 | ha0
      · apply le_trans ?_ hUad
        nlinarith [mul_nonneg hxa (neg_nonneg.mpr hy0), mul_nonneg ha0 hdy]
      · apply le_trans ?_ hUac
        have hc0 : c ≤ 0 := hy.1.trans hy0
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hx0 hy0,
          mul_nonneg_of_nonpos_of_nonpos ha0 hc0]
  · constructor
    · apply hLad.trans
      have ha0 : a ≤ 0 := hx.1.trans hx0
      have hd0 : 0 ≤ d := hy0.trans hy.2
      nlinarith [mul_nonneg hxa hd0, mul_nonneg (neg_nonneg.mpr hx0) hdy]
    · rcases le_total 0 c with hc0 | hc0
      · apply le_trans ?_ hUbc
        rcases le_total 0 b with hb0 | hb0
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg hx0 hy0,
            mul_nonneg hb0 hc0]
        · nlinarith [mul_nonneg hbx hy0, mul_nonneg (neg_nonneg.mpr hb0) hyc]
      · apply le_trans ?_ hUac
        have ha0 : a ≤ 0 := hx.1.trans hx0
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hx0 hy0,
          mul_nonneg_of_nonpos_of_nonpos ha0 hc0]
  · constructor
    · rcases le_total b 0 with hb0 | hb0
      · rcases le_total d 0 with hd0 | hd0
        · apply hLbd.trans
          nlinarith [mul_nonneg hbx (neg_nonneg.mpr hy0),
            mul_nonneg (neg_nonneg.mpr hb0) hdy]
        · apply hLad.trans
          have ha0 : a ≤ 0 := hx.1.trans hx0
          nlinarith [mul_nonpos_of_nonpos_of_nonneg ha0 hd0,
            mul_nonneg_of_nonpos_of_nonpos hx0 hy0]
      · apply hLbc.trans
        have hc0 : c ≤ 0 := hy.1.trans hy0
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hb0 hc0,
          mul_nonneg_of_nonpos_of_nonpos hx0 hy0]
    · apply le_trans ?_ hUac
      have ha0 : a ≤ 0 := hx.1.trans hx0
      have hc0 : c ≤ 0 := hy.1.trans hy0
      nlinarith [mul_nonneg hxa (neg_nonneg.mpr hy0),
        mul_nonneg (neg_nonneg.mpr ha0) hyc]

lemma holds_mul {i j : RatInterval} {x y : ℝ} (hx : Holds i x) (hy : Holds j y) :
    Holds (mul i j) (x * y) := by
  simpa only [mul, Holds, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using mul_aux hx hy

lemma holds_sq {i : RatInterval} {x : ℝ} (hx : Holds i x) : Holds (sq i) (x ^ 2) := by
  simpa [sq, pow_two] using holds_mul hx hx

lemma holds_invPos {i : RatInterval} {x : ℝ} (hi : (0 : ℚ) < i.lo) (hx : Holds i x) :
    Holds (invPos i) x⁻¹ := by
  have hlo : (0 : ℝ) < (i.lo : ℝ) := by exact_mod_cast hi
  have hxpos : 0 < x := hlo.trans_le hx.1
  have hhipos : (0 : ℝ) < (i.hi : ℝ) := hxpos.trans_le hx.2
  simp only [Holds, invPos, Rat.cast_inv]
  exact ⟨inv_le_inv₀ hhipos hxpos |>.2 hx.2, inv_le_inv₀ hxpos hlo |>.2 hx.1⟩

lemma holds_divPos {i j : RatInterval} {x y : ℝ} (hj : (0 : ℚ) < j.lo)
    (hx : Holds i x) (hy : Holds j y) : Holds (divPos i j) (x / y) := by
  simpa [divPos, div_eq_mul_inv] using holds_mul hx (holds_invPos hj hy)

end RatInterval
end Zeta23.ThmD.Sextuple
