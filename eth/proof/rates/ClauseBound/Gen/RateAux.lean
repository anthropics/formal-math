/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs

/-! # Arithmetic for the rate of the general recursion

Bit lengths of sums, products and powers; the bit length of a number below a power of X in terms of
log X; and the polynomial inequalities
between natural numbers by which lower-order quantities of one level are bounded by powers of X =
g²·(λ + B). -/

public section

namespace ClauseBound.Gen.Rate

open Nat (size)

/-! ### Bit lengths -/

/-- size n ≤ n. -/
theorem size_le_self (n : ℕ) : size n ≤ n := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

/-- size (a·b) ≤ size a + size b. -/
theorem size_mul_le (a b : ℕ) : size (a * b) ≤ size a + size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

/-- size (a + b) ≤ size a + size b. -/
theorem size_add_le (a b : ℕ) : size (a + b) ≤ size a + size b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rw [Nat.size_le, pow_add]
  have h1 := Nat.lt_size_self a
  have h2 := Nat.lt_size_self b
  have hA : 2 ≤ 2 ^ size a := by omega
  have hB : 2 ≤ 2 ^ size b := by omega
  nlinarith

/-- size (2·a) ≤ size a + 1. -/
theorem size_two_mul_le (a : ℕ) : size (2 * a) ≤ size a + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self a
  omega

/-- size (8·a) ≤ size a + 3. -/
theorem size_eight_mul_le (a : ℕ) : size (8 * a) ≤ size a + 3 := by
  rw [Nat.size_le, pow_add]
  have := Nat.lt_size_self a
  omega

/-- size (2^k·b) ≤ k + 1 + size b. -/
theorem size_two_pow_mul_le (k b : ℕ) : size (2 ^ k * b) ≤ k + 1 + size b := by
  have := size_mul_le (2 ^ k) b
  rwa [Nat.size_pow] at this

/-- size (a^n) ≤ n·size a + 1. -/
theorem size_pow_le (a n : ℕ) : size (a ^ n) ≤ n * size a + 1 := by
  rw [Nat.size_le]
  calc a ^ n ≤ (2 ^ size a) ^ n := Nat.pow_le_pow_left (Nat.lt_size_self a).le n
    _ = 2 ^ (n * size a) := by rw [← pow_mul, mul_comm]
    _ < 2 ^ (n * size a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- If n ≤ X^k then size n ≤ k·log X + 1. -/
theorem size_cast_le {n X k : ℕ} (hX : 1 ≤ X) (h : n ≤ X ^ k) : (size n : ℝ) ≤ k * Real.logb 2 X + 1 := by
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hL : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.size_zero, Nat.cast_zero]; positivity
  obtain ⟨m, hm⟩ : ∃ m, size n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.size_pos.2 hn).ne'
  have h1 : 2 ^ m ≤ n := Nat.lt_size.1 (by omega)
  have h2 : (2 : ℝ) ^ m ≤ (X : ℝ) ^ k := by exact_mod_cast h1.trans h
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h2
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h3
  rw [hm]; push_cast; linarith

/-! ### The length of an instance -/

/-- The bit length of the first budget, with the parts that depend on cnt and z split off. -/
theorem size_first_le (Kup lam B cnt z : ℕ) :
    size (cnt * PaddedDescent.F.instLen Kup lam B + 8 * z + 4 * lam + 40) ≤
      size cnt + size z + (Kup - 1) * lam + size (4 * lam + Kup * (3 * B + 14) + 10) + size (4 * lam + 40) + 4 := by
  have h1 : PaddedDescent.F.instLen Kup lam B ≤ 2 ^ ((Kup - 1) * lam) * (4 * lam + Kup * (3 * B + 14) + 10) := by
    unfold PaddedDescent.F.instLen
    have hE : 1 ≤ 2 ^ ((Kup - 1) * lam) := Nat.one_le_two_pow
    generalize 2 ^ ((Kup - 1) * lam) = E at *
    have e1 : 4 * lam ≤ E * (4 * lam) := Nat.le_mul_of_pos_left _ hE
    have e2 : Kup * 4 ≤ E * (Kup * 4) := Nat.le_mul_of_pos_left _ hE
    have e3 : 10 ≤ E * 10 := Nat.le_mul_of_pos_left _ hE
    calc 4 * lam + Kup * (E * (3 * B + 10) + 4) + 10
        = 4 * lam + (E * (Kup * (3 * B + 10)) + Kup * 4) + 10 := by ring
      _ ≤ E * (4 * lam) + (E * (Kup * (3 * B + 10)) + E * (Kup * 4)) + E * 10 := by gcongr
      _ = E * (4 * lam + Kup * (3 * B + 14) + 10) := by ring
  have h2 : size (PaddedDescent.F.instLen Kup lam B) ≤ (Kup - 1) * lam + 1 + size (4 * lam + Kup * (3 * B + 14) + 10) :=
    (Nat.size_le_size h1).trans (size_two_pow_mul_le _ _)
  have h3 : cnt * PaddedDescent.F.instLen Kup lam B + 8 * z + 4 * lam + 40 =
      cnt * PaddedDescent.F.instLen Kup lam B + (8 * z + (4 * lam + 40)) := by ring
  have h4 := size_add_le (cnt * PaddedDescent.F.instLen Kup lam B) (8 * z + (4 * lam + 40))
  have h5 := size_add_le (8 * z) (4 * lam + 40)
  have h6 := size_mul_le cnt (PaddedDescent.F.instLen Kup lam B)
  have h7 := size_eight_mul_le z
  rw [h3]
  omega

/-- The two small numbers of the first budget are below X², X = K·(λ + B). -/
theorem small_le_sq (Kup lam B : ℕ) (hK : 44 ≤ Kup) (hlam : 1 ≤ lam) :
    4 * lam + Kup * (3 * B + 14) + 10 ≤ (Kup * (lam + B)) ^ 2 ∧ 4 * lam + 40 ≤ (Kup * (lam + B)) ^ 2 := by
  have h1 : lam + B ≤ Kup * (lam + B) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : 44 * (lam + B) ≤ Kup * (lam + B) := Nat.mul_le_mul_right _ hK
  generalize hX : Kup * (lam + B) = X at *
  have h3 : 44 * X ≤ X ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  have h4 : Kup * (3 * B + 14) ≤ 14 * X := by
    rw [← hX]
    calc Kup * (3 * B + 14) ≤ Kup * (14 * (lam + B)) := Nat.mul_le_mul_left _ (by omega)
      _ = 14 * (Kup * (lam + B)) := by ring
  constructor <;> omega

/-! ### Polynomial inequalities of one level -/

/-- 4·(number of rectangles) ≤ g⁴. -/
theorem four_nRect_le (g : ℕ) : 4 * ClauseBound.Alg.nRectG g g ≤ g ^ 4 := by
  have h1 : 2 * Groundwork.Grid.c2 g ≤ g * g := by
    unfold Groundwork.Grid.c2
    calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
      _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  unfold ClauseBound.Alg.nRectG
  calc 4 * (Groundwork.Grid.c2 g * Groundwork.Grid.c2 g) = (2 * Groundwork.Grid.c2 g) * (2 * Groundwork.Grid.c2 g) := by ring
    _ ≤ (g * g) * (g * g) := Nat.mul_le_mul h1 h1
    _ = g ^ 4 := by ring

/-- What is added to z + size cnt at one level, apart from a doubling, is at most X^(c+3). -/
theorem rest_le (g c lam B bits sd R sp : ℕ) (hc : 1 ≤ c) (hlam : 1 ≤ lam) (hg : 6 ≤ g) (hbits : bits ≤ (2 * lam) ^ c)
    (hsd : sd ≤ (2 * lam) ^ c) (hR : R ≤ g ^ 4) (hsp : sp ≤ R * (2 * lam) ^ c + 1) :
    R * sd + (g * g) ^ 2 * lam + g ^ 2 * (g * B + g ^ 2 * bits + 1) + 2 + 2 * sp ≤ (g ^ 2 * (lam + B)) ^ (c + 3) := by
  obtain ⟨a, ha⟩ : ∃ a, a = g ^ 2 := ⟨_, rfl⟩
  have hga : g ≤ a := by rw [ha, sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have ha6 : 6 ≤ a := by omega
  have hg4 : g ^ 4 = a * a := by rw [ha]; ring
  have hgg : (g * g) ^ 2 = a * a := by rw [ha]; ring
  rw [hg4] at hR
  rw [hgg, ← ha]
  obtain ⟨X, hX⟩ : ∃ X, X = a * (lam + B) := ⟨_, rfl⟩
  rw [← hX]
  have haX : a ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ c := ⟨_, rfl⟩
  have hXY : X ≤ Y := by rw [hY]; exact Nat.le_self_pow (by omega) X
  have hY1 : 1 ≤ Y := by omega
  have h1 : a * lam ≤ Y := le_trans (by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)) hXY
  have h2 : a * B ≤ Y := le_trans (by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)) hXY
  have h2l : 2 * lam ≤ X := by
    calc 2 * lam ≤ a * lam := Nat.mul_le_mul_right _ (by omega)
      _ ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have ht : (2 * lam) ^ c ≤ Y := by rw [hY]; exact Nat.pow_le_pow_left h2l c
  have h3 : bits ≤ Y := hbits.trans ht
  have h4 : sd ≤ Y := hsd.trans ht
  have hgB : g * B ≤ Y := le_trans (Nat.mul_le_mul_right _ hga) h2
  have h5 : sp ≤ a * a * Y + Y := by
    calc sp ≤ R * (2 * lam) ^ c + 1 := hsp
      _ ≤ a * a * Y + Y := by gcongr
  have h6 : a * a * lam ≤ a * Y := by
    calc a * a * lam = a * (a * lam) := by ring
      _ ≤ a * Y := by gcongr
  have q1 : 6 * a ≤ a ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ ha6
  have q2 : 6 * a ^ 2 ≤ a ^ 3 := by rw [pow_succ a 2, mul_comm]; exact Nat.mul_le_mul_left _ ha6
  calc R * sd + a * a * lam + a * (g * B + a * bits + 1) + 2 + 2 * sp
      ≤ a * a * Y + a * Y + a * (Y + a * Y + Y) + 2 * Y + 2 * (a * a * Y + Y) := by gcongr; omega
    _ = (4 * a ^ 2 + 3 * a + 4) * Y := by ring
    _ ≤ a ^ 3 * Y := Nat.mul_le_mul_right _ (by omega)
    _ ≤ X ^ 3 * Y := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left haX 3)
    _ = X ^ (c + 3) := by rw [hY]; ring

end ClauseBound.Gen.Rate
