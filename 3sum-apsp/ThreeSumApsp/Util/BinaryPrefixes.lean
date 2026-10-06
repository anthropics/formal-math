/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.List
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The prefixes of a binary representation, one bit at a time

The prefixes `⌊z/2^ℓ⌋` of a number `0 ≤ z < 2^L` are computed without division, from the level
`ℓ = L` down to `ℓ = 0`.  Next to the prefix `q = ⌊z/2^ℓ⌋` (`prefQ`) one keeps the rest of the
number, moved to the top: `r = (z mod 2^ℓ) 2^(L-ℓ) < 2^L` (`prefR`).  One step doubles `r`; if the
result reaches `2^L`, then the next bit of `z` is 1 (`pref_step`).  The bit is the binary digit
number `ℓ` of `z` (`testBit_iff_shift`).  One step on lists of numbers is `zipWith_shiftQ` and
`map_shiftR`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Prefixes, one bit at a time -/

/-- The prefix `⌊z/2^ℓ⌋`. -/
def prefQ (ℓ : ℕ) (z : ℤ) : ℤ := z / 2 ^ ℓ

/-- The rest `z mod 2^ℓ`, moved to the top of `L` bits. -/
def prefR (L ℓ : ℕ) (z : ℤ) : ℤ := z % 2 ^ ℓ * 2 ^ (L - ℓ)

/-- The new prefix after one step: the old one with the next bit appended. -/
def shiftQ (P q r : ℤ) : ℤ := if 2 * r < P then 2 * q else 2 * q + 1

/-- The new rest after one step. -/
def shiftR (P r : ℤ) : ℤ := if 2 * r < P then 2 * r else 2 * r - P

/-- At the top level the prefix is 0. -/
theorem prefQ_start {L : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z < 2 ^ L) : prefQ L z = 0 :=
  Int.ediv_eq_zero_of_lt h0 h

/-- At the top level the rest is the number itself. -/
theorem prefR_start {L : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z < 2 ^ L) : prefR L L z = z := by
  simp [prefR, Int.emod_eq_of_lt h0 h]

/-- **One step**: the prefix and the rest at the level `ℓ` are `shiftQ` and `shiftR` of those at the
level `ℓ + 1`. -/
theorem pref_step {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (z : ℤ) :
    prefQ ℓ z = shiftQ (2 ^ L) (prefQ (ℓ + 1) z) (prefR L (ℓ + 1) z) ∧
      prefR L ℓ z = shiftR (2 ^ L) (prefR L (ℓ + 1) z) := by
  -- In terms of `m = 2^ℓ` and `s = 2^(L - ℓ - 1)`.
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [prefQ, prefR, shiftQ, shiftR, Nat.add_sub_cancel_left,
    show ℓ + 1 + j - ℓ = j + 1 by omega]
  rw [show (2 : ℤ) ^ (ℓ + 1 + j) = 2 * 2 ^ ℓ * 2 ^ j by ring,
    show (2 : ℤ) ^ (ℓ + 1) = 2 * 2 ^ ℓ by ring, show (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j by ring]
  have hm : (0 : ℤ) < 2 ^ ℓ := by positivity
  have hs : (0 : ℤ) < 2 ^ j := by positivity
  generalize (2 : ℤ) ^ ℓ = m at hm
  generalize (2 : ℤ) ^ j = s at hs
  -- Write `z = 2 m a + b` with `0 ≤ b < 2 m`; the next bit of `z` is 0 exactly if `b < m`.
  have hz := Int.mul_ediv_add_emod z (2 * m)
  have hb0 := Int.emod_nonneg z (show 2 * m ≠ 0 by omega)
  have hb2 := Int.emod_lt_of_pos z (show 0 < 2 * m by omega)
  generalize z / (2 * m) = a at hz
  generalize z % (2 * m) = b at hz hb0 hb2
  by_cases hb : b < m
  · have hcond : 2 * (b * s) < 2 * m * s := by linarith [mul_pos (sub_pos.2 hb) hs]
    obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique hm (a := z) (q := 2 * a) (r := b)).2
      ⟨by linarith, hb0, hb⟩
    rw [if_pos hcond, if_pos hcond, hq, hr]
    exact ⟨rfl, by ring⟩
  · have hcond : ¬ 2 * (b * s) < 2 * m * s := by
      linarith [mul_nonneg (sub_nonneg.2 (not_lt.1 hb)) hs.le]
    obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique hm (a := z) (q := 2 * a + 1) (r := b - m)).2
      ⟨by linarith, by omega, by omega⟩
    rw [if_neg hcond, if_neg hcond, hq, hr]
    exact ⟨rfl, by ring⟩

/-- The prefixes of a nonnegative number are nonnegative. -/
theorem prefQ_nonneg {z : ℤ} (h0 : 0 ≤ z) (ℓ : ℕ) : 0 ≤ prefQ ℓ z :=
  Int.ediv_nonneg h0 (by positivity)

/-- The prefixes of a nonnegative number are at most the number. -/
theorem prefQ_le {z : ℤ} (h0 : 0 ≤ z) (ℓ : ℕ) : prefQ ℓ z ≤ z := Int.ediv_le_self _ h0

/-- The rests are nonnegative. -/
theorem prefR_nonneg (L ℓ : ℕ) (z : ℤ) : 0 ≤ prefR L ℓ z :=
  mul_nonneg (Int.emod_nonneg _ (by positivity)) (by positivity)

/-- The rests have `L` bits. -/
theorem prefR_lt {L ℓ : ℕ} (h : ℓ ≤ L) (z : ℤ) : prefR L ℓ z < 2 ^ L := by
  have hmod : z % 2 ^ ℓ < 2 ^ ℓ := Int.emod_lt_of_pos _ (by positivity)
  rw [prefR, ← Nat.add_sub_cancel' h, pow_add, Nat.add_sub_cancel' h]
  exact mul_lt_mul_of_pos_right hmod (by positivity)

/-- The prefix of a natural number is the quotient of natural numbers. -/
theorem prefQ_natCast (ℓ z : ℕ) : prefQ ℓ (z : ℤ) = ((z / 2 ^ ℓ : ℕ) : ℤ) := by
  simp [prefQ]

/-- The bit that a step moves from the rest to the prefix is the binary digit number `ℓ`. -/
theorem testBit_iff_shift {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (z : ℕ) :
    z.testBit ℓ = true ↔ ¬ 2 * prefR L (ℓ + 1) (z : ℤ) < 2 ^ L := by
  have hstep := (pref_step h (z : ℤ)).1
  rw [prefQ_natCast, prefQ_natCast, shiftQ] at hstep
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  split_ifs at hstep with hc
  · exact iff_of_false (by omega) (not_not.2 hc)
  · exact iff_of_true (by omega) hc

/-! ## The lists of the prefixes and of the rests -/

/-- One step on the list of the prefixes. -/
theorem zipWith_shiftQ {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (Z : List ℤ) :
    List.zipWith (shiftQ (2 ^ L)) (Z.map (prefQ (ℓ + 1))) (Z.map (prefR L (ℓ + 1))) =
      Z.map (prefQ ℓ) := by
  rw [List.zipWith_map, List.zipWith_self]
  exact List.map_congr_left fun z _ => (pref_step h z).1.symm

/-- One step on the list of the rests. -/
theorem map_shiftR {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (Z : List ℤ) :
    (Z.map (prefR L (ℓ + 1))).map (shiftR (2 ^ L)) = Z.map (prefR L ℓ) := by
  rw [List.map_map]
  exact List.map_congr_left fun z _ => (pref_step h z).2.symm

/-- At the top level the rests are the numbers themselves. -/
theorem map_prefR_start {L : ℕ} {Z : List ℤ} (h : ∀ z ∈ Z, 0 ≤ z ∧ z < 2 ^ L) :
    Z.map (prefR L L) = Z := by
  conv_rhs => rw [← List.map_id Z]
  exact List.map_congr_left fun z hz => prefR_start (h z hz).1 (h z hz).2

end ThreeSumApsp
