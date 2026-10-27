/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Prog
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum

/-! What one level of the recursion does to the numbers of an instance (label length, bits per
entry), as inequalities between natural numbers about the functions Pn, Ubar, lamNext, bNext,
instLen of PaddedDescent.F.Prog. No programs occur here. -/

@[expose] public section

namespace PaddedDescent.F.Arith

open PaddedDescent PaddedDescent.F

/-! ### One level: the label length -/

/-- 800·Ubar ≤ 800g³Λ + 717g⁴Λ + 400g⁴ + 800. -/
theorem mul_Ubar_le (g lam : ℕ) :
    800 * Ubar g lam ≤ 800 * (g ^ 3 * lam) + 717 * (g ^ 4 * lam) + 400 * g ^ 4 + 800 := by
  have h1 : g ^ 2 * (g - 1) * lam ≤ g ^ 3 * lam := by
    refine Nat.mul_le_mul_right _ ?_
    calc g ^ 2 * (g - 1) ≤ g ^ 2 * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ 3 := by ring
  have h2 : 800 * (717 * g ^ 4 * lam / 800) ≤ 717 * g ^ 4 * lam := Nat.mul_div_le _ _
  have h3 : 2 * (g ^ 4 / 2) ≤ g ^ 4 := Nat.mul_div_le _ _
  have h4 : 717 * g ^ 4 * lam = 717 * (g ^ 4 * lam) := by ring
  unfold Ubar
  omega

/-- D·K²·lamNext ≤ D·Ubar + 3g³Λ + 6g⁴Λ + D·K², with D = `Dcol`. -/
theorem lamNext_mul_le (K g lam : ℕ) :
    Dcol * (K ^ 2 * lamNext K g lam) ≤ Dcol * Ubar g lam + 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) + Dcol * K ^ 2 := by
  have h := Nat.div_mul_le_self (Dcol * Ubar g lam + 3 * g ^ 2 * capM g lam) (Dcol * K ^ 2)
  have e : 3 * g ^ 2 * capM g lam = 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) := by unfold capM; ring
  rw [e] at h
  unfold lamNext
  rw [e]
  calc Dcol * (K ^ 2 * ((Dcol * Ubar g lam + (3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam))) / (Dcol * K ^ 2) + 1))
      = (Dcol * Ubar g lam + (3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam))) / (Dcol * K ^ 2) * (Dcol * K ^ 2) + Dcol * K ^ 2 := by ring
    _ ≤ Dcol * Ubar g lam + 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) + Dcol * K ^ 2 := by omega

/-- The contraction of one level. With Q = g⁴Λ (the square of the number of nodes times the label
length) before the level and
Q' = K²·lamNext after it: Q' ≤ (8963/10000)·Q + g⁴. -/
theorem lamNext_contract {K g : ℕ} (hg : K ≤ g) (hg20 : 2 ^ 20 ≤ g) (lam : ℕ) :
    10000 * (K ^ 2 * lamNext K g lam) ≤ 8963 * (g ^ 4 * lam) + 10000 * g ^ 4 := by
  have h0 := lamNext_mul_le K g lam
  have h1 := mul_Ubar_le g lam
  have hD : Dcol = 262144 := by norm_num [Dcol]
  rw [hD] at h0
  have f1 : 2 ^ 20 * (g ^ 3 * lam) ≤ g ^ 4 * lam := by
    calc 2 ^ 20 * (g ^ 3 * lam) ≤ g * (g ^ 3 * lam) := Nat.mul_le_mul_right _ hg20
      _ = g ^ 4 * lam := by ring
  have f3 : 4 * (K ^ 2 + 1) ≤ g ^ 4 := by
    have a1 : K ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
    have a2 : 8 ≤ g ^ 2 := by nlinarith
    have a3 : 8 * g ^ 2 ≤ g ^ 2 * g ^ 2 := Nat.mul_le_mul_right _ a2
    have a4 : g ^ 2 * g ^ 2 = g ^ 4 := by ring
    omega
  norm_num at f1
  omega

/-! ### One level: the number of bits of an entry -/

/-- The entries after one level have at most g³B + 2g⁴Λ bits. -/
theorem bNext_le {K g : ℕ} (hK : 256 ≤ K) (hg : K ≤ g) (lam B : ℕ) :
    bNext K g lam B ≤ g ^ 3 * B + 2 * (g ^ 4 * lam) := by
  set m := 2 * g / K with hm
  have m1 : m * K ≤ 2 * g := Nat.div_mul_le_self _ _
  have m2 : 128 * m ≤ g := by nlinarith
  have a1 : Pn g lam * m ≤ g ^ 4 * lam := by
    calc Pn g lam * m = 2 * m * (g ^ 3 * lam) := by unfold Pn; ring
      _ ≤ g * (g ^ 3 * lam) := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ 4 * lam := by ring
  have a2 : (m + m * m) * K ≤ g ^ 2 := by
    calc (m + m * m) * K = (1 + m) * (m * K) := by ring
      _ ≤ (1 + m) * (2 * g) := Nat.mul_le_mul_left _ m1
      _ = (2 + 2 * m) * g := by ring
      _ ≤ g * g := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ 2 := by ring
  have a3 : (g * B + g ^ 2 * lam) * (m + m * m) * K ≤ g ^ 3 * B + g ^ 4 * lam := by
    calc (g * B + g ^ 2 * lam) * (m + m * m) * K = (g * B + g ^ 2 * lam) * ((m + m * m) * K) := by ring
      _ ≤ (g * B + g ^ 2 * lam) * g ^ 2 := Nat.mul_le_mul_left _ a2
      _ = g ^ 3 * B + g ^ 4 * lam := by ring
  unfold bNext
  rw [← hm]
  omega

/-- A weaker form of `bNext_le`: 6g³B + 8g⁴Λ instead of g³B + 2g⁴Λ. -/
theorem bNext_le' {K g : ℕ} (hK : 256 ≤ K) (hg : K ≤ g) (lam B : ℕ) :
    bNext K g lam B ≤ 6 * (g ^ 3 * B) + 8 * (g ^ 4 * lam) := by
  have h := bNext_le hK hg lam B
  omega

/-! ### The exponents of the budgets of one level -/

/-- The states of a class: K times the exponent is at most 4g⁴Λ. -/
theorem mul_Pn_mul_le (K g lam : ℕ) : K * (Pn g lam * (2 * g / K)) ≤ 4 * (g ^ 4 * lam) := by
  have m1 : 2 * g / K * K ≤ 2 * g := Nat.div_mul_le_self _ _
  calc K * (Pn g lam * (2 * g / K)) = Pn g lam * (2 * g / K * K) := by ring
    _ ≤ Pn g lam * (2 * g) := Nat.mul_le_mul_left _ m1
    _ = 4 * (g ^ 4 * lam) := by unfold Pn; ring

/-- The labels inside a class: g times the exponent is 2g⁴Λ. -/
theorem mul_Pn_eq (g lam : ℕ) : g * Pn g lam = 2 * (g ^ 4 * lam) := by
  unfold Pn; ring

/-- The number of rectangles is at most g⁴/4. -/
theorem four_mul_nRect_le (g : ℕ) : 4 * Groundwork.Prog.nRect g ≤ g ^ 4 := Groundwork.GridArith.four_mul_choose_sq_le g

/-- The number of rectangles is at most g⁴. -/
theorem nRect_le (g : ℕ) : Groundwork.Prog.nRect g ≤ g ^ 4 := by
  have := four_mul_nRect_le g
  omega

/-- The colourings: K^g ≤ 2^{Kg}. -/
theorem pow_le_two_pow_mul (K g : ℕ) : K ^ g ≤ 2 ^ (K * g) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le g

/-- The colourings: K^g ≤ 2^{g·g}. -/
theorem pow_le_two_pow_sq {K g : ℕ} (hg : K ≤ g) : K ^ g ≤ 2 ^ (g * g) :=
  le_trans (pow_le_two_pow_mul K g) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hg))

/-- The length of an instance: the number of table entries of a row times a polynomial factor. -/
theorem instLen_le (K lam B : ℕ) : instLen K lam B ≤ 2 ^ ((K - 1) * lam) * (K * (3 * B + 14) + 4 * lam + 10) := by
  have h1 : 1 ≤ 2 ^ ((K - 1) * lam) := Nat.one_le_two_pow
  obtain ⟨p, hp⟩ : ∃ p, 2 ^ ((K - 1) * lam) = p + 1 := ⟨2 ^ ((K - 1) * lam) - 1, by omega⟩
  unfold instLen
  rw [hp]
  nlinarith [Nat.zero_le (p * lam), Nat.zero_le (p * K), Nat.zero_le p]

/-! ### The next level is much bigger -/

/-- 6g³·K³ ≤ (g·g)³, if 2K ≤ g. -/
theorem six_cube_mul_cube_le {K g : ℕ} (hg : 2 * K ≤ g) : 6 * g ^ 3 * K ^ 3 ≤ (g * g) ^ 3 := by
  have h : (2 * K) ^ 3 ≤ g ^ 3 := Nat.pow_le_pow_left hg 3
  calc 6 * g ^ 3 * K ^ 3 ≤ g ^ 3 * (2 * K) ^ 3 := by
        have : (2 * K) ^ 3 = 8 * K ^ 3 := by ring
        rw [this]; nlinarith [Nat.zero_le (g ^ 3 * K ^ 3)]
    _ ≤ g ^ 3 * g ^ 3 := Nat.mul_le_mul_left _ h
    _ = (g * g) ^ 3 := by ring

/-- 24K³ ≤ 16(g·g)³ and 2K² ≤ (g·g)², if 2K ≤ g. -/
theorem pow_facts {K g : ℕ} (hg : 2 * K ≤ g) :
    24 * K ^ 3 ≤ 16 * (g * g) ^ 3 ∧ 2 * K ^ 2 ≤ (g * g) ^ 2 := by
  have hgg : 2 * K ≤ g * g := le_trans hg (Nat.le_mul_self g)
  have h3 : (2 * K) ^ 3 ≤ (g * g) ^ 3 := Nat.pow_le_pow_left hgg 3
  have h2 : (2 * K) ^ 2 ≤ (g * g) ^ 2 := Nat.pow_le_pow_left hgg 2
  have e3 : (2 * K) ^ 3 = 8 * K ^ 3 := by ring
  have e2 : (2 * K) ^ 2 = 4 * K ^ 2 := by ring
  constructor <;> omega

end PaddedDescent.F.Arith
