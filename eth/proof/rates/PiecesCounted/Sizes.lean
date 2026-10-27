/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCounted.Basic
import GeneralPieces.DefGenPieces.Conv
import Mathlib.Tactic

/-! # The sizes of questions and answers
For data that satisfy parts (a) and (b) of Definition 7 (pieces with parameters (ρ,c)) and the size
bounds of its part (c): a question that has an answer has size at most (2λ)^c + 14λ + 2cλ + 11
(with λ in unary), and the answer has size at most (2λ)^c·((2λ)^c + 2) + cλ + 4λ + 2. Both are far
below `room c λ`; the lemmas at the end put the two bounds in the form in which the later files
compare them with `room` (multiplied out by `room_eq`). -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog

/-! ### Sizes of lists and numbers -/

/-- A list of n units has size 2n + 1. -/
theorem size_units (l : List Unit) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_unit, List.length_cons] at ih ⊢
    omega

/-- A list of n bits has size 2n + 1. -/
theorem size_bitList (l : List Bool) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢
    omega

/-- An integer below 2^X in absolute value has size at most X + 1. -/
theorem size_int_le {z : ℤ} {X : ℕ} (h : |z| < 2 ^ X) : size z ≤ X + 1 := by
  have h1 : (z.natAbs : ℤ) < 2 ^ X := by rw [Int.natCast_natAbs]; exact h
  have h2 : z.natAbs < 2 ^ X := by exact_mod_cast h1
  have := Nat.size_le.2 h2
  rw [size_int]
  omega

/-- A natural number n, as an integer, has size at most n + 1. -/
theorem size_natCast_le (n : ℕ) : size (n : ℤ) ≤ n + 1 := by
  have := Nat.size_le.2 (Nat.lt_two_pow_self (n := n))
  rw [size_int, Int.natAbs_natCast]
  omega

/-- A list of integers, each of size at most s. -/
theorem size_ints_le {l : List ℤ} {s : ℕ} (h : ∀ x ∈ l, size x ≤ s) : size l ≤ l.length * (s + 1) + 1 := by
  induction l with
  | nil => simp [size_list]
  | cons a l ih =>
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h a List.mem_cons_self
    simp only [size_list, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at h1 ⊢
    omega

/-! ### The numbers of bits -/

/-- c^row_i, c^col_i ≤ cλ + 4λ, from the bound of (b). -/
theorem Data.Is.cap_le {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {lam : ℕ} (hl : 1 ≤ lam) {i : ℤ} (hi : i ∈ (D.fam lam).I) (tr : Bool) : D.cap lam tr i ≤ c * lam + 4 * lam := by
  have h0 := h.caps lam hl i hi
  have h1 := GeneralPieces.DefGenPieces.logb_le hl
  have h2 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have h4 : 4 * ρ * lam ≤ 4 * 1 * lam := mul_le_mul_of_nonneg_right (by linarith [h.rho_lt]) h2
  have h5 : (c : ℝ) * Real.logb 2 (2 * lam) ≤ c * lam := mul_le_mul_of_nonneg_left h1 h3
  have h6 : ((D.cap lam false i + D.cap lam true i : ℕ) : ℝ) ≤ ((c * lam + 4 * lam : ℕ) : ℝ) := by
    push_cast at h0 ⊢
    linarith
  have h7 : D.cap lam false i + D.cap lam true i ≤ c * lam + 4 * lam := by exact_mod_cast h6
  cases tr <;> omega

/-! ### Questions and answers -/

/-- A question that has an answer, with λ in unary, has size at most (2λ)^c + 14λ + 2cλ + 11. -/
theorem Data.Is.size_question_le {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size g ≤ (2 * g.1.length) ^ c + 14 * g.1.length + 2 * (c * g.1.length) + 11 := by
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha ⊢
  rcases q with q | q | q | q | q
  · simp only [size_prod, size_inl, size_unit, size_units]
    omega
  · simp only [size_prod, size_inl, size_inr, size_unit, size_units]
    omega
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      have := size_int_le (h.size_I _ hl _ hi)
      simp only [size_prod, size_inl, size_inr, size_bool, size_units]
      omega
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain ⟨hi, e1, e2, e3, e4⟩ := hi
      have := size_int_le (h.size_I _ hl _ hi)
      simp only [size_prod, size_inl, size_inr, size_bitList, size_units, e1, e2, e3, e4]
      omega
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain ⟨hi, e1, e2, e3⟩ := hi
      have := size_int_le (h.size_I _ hl _ hi)
      have := h.cap_le hl hi q.1.1
      simp only [size_prod, size_inr, size_bool, size_bitList, size_units, e1, e2, e3]
      omega
    · cases ha

/-- An answer has size at most (2λ)^c·((2λ)^c + 2) + cλ + 4λ + 2. -/
theorem Data.Is.size_answer_le {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size a ≤ (2 * g.1.length) ^ c * ((2 * g.1.length) ^ c + 2) + (c * g.1.length + 4 * g.1.length) + 2 := by
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha ⊢
  have hX : (2 * u.length) ^ c ≤ (2 * u.length) ^ c * ((2 * u.length) ^ c + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rcases q with q | q | q | q | q
  · obtain rfl : Sum.inl (D.fam u.length).d = a := Option.some.inj ha
    have h0 : (0 : ℤ) ≤ (D.fam u.length).d := by have := h.d_pos _ hl; omega
    have h1 : |(D.fam u.length).d| < 2 ^ (2 * u.length) ^ c := by rw [abs_of_nonneg h0]; exact h.size_d _ hl
    have := size_int_le h1
    rw [size_inl]
    omega
  · obtain rfl := Option.some.inj ha
    have h1 : size (D.fam u.length).I.sort ≤ (D.fam u.length).I.sort.length * ((2 * u.length) ^ c + 2) + 1 :=
      size_ints_le (s := (2 * u.length) ^ c + 1) fun x hx => size_int_le (h.size_I _ hl x ((Finset.mem_sort _).1 hx))
    rw [Finset.length_sort] at h1
    have h2 := Nat.mul_le_mul_right ((2 * u.length) ^ c + 2) (h.card _ hl)
    rw [size_inr]
    omega
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      have := size_natCast_le (D.cap u.length q.1 q.2)
      have := h.cap_le hl hi q.1
      rw [size_inl]
      omega
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      have := size_int_le (h.size_A _ hl _ hi.1 (toBits _ q.2.1) (toBits _ q.2.2.1) (toBits _ q.2.2.2.1) (toBits _ q.2.2.2.2))
      rw [size_inl]
      omega
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      have := size_int_le (h.size_f _ hl _ hi.1 q.1.1 q.1.2 (toBits _ q.2.2.1, toBits _ q.2.2.2.1) q.2.2.2.2 (mem_words.2 hi.2.2.2))
      rw [size_inl]
      omega
    · cases ha

/-! ### How they fit the bound on the states -/

/-- The bound on the states, multiplied out. -/
theorem room_eq (c lam : ℕ) : room c lam = 2 ^ (c * lam) * (2 * lam) ^ c + 8 * 2 ^ (c * lam) + (2 * lam) ^ c * (2 * lam) ^ c + 16 * (2 * lam) ^ c + 64 := by
  unfold room
  ring

/-- 2λ ≤ (2λ)^c for c ≥ 1. -/
theorem two_mul_le_pow {c : ℕ} (hc : 1 ≤ c) (lam : ℕ) : 2 * lam ≤ (2 * lam) ^ c := Nat.le_self_pow (by omega) _

/-- A question that has an answer: at most 8·(2λ)^c + 2·2^{cλ} + 11. -/
theorem Data.Is.size_question_le' {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size g ≤ 8 * (2 * g.1.length) ^ c + 2 * 2 ^ (c * g.1.length) + 11 := by
  have h1 := h.size_question_le hg
  have h2 := two_mul_le_pow h.c_pos g.1.length
  have h3 := Nat.lt_two_pow_self (n := c * g.1.length)
  omega

/-- An answer: at most (2λ)^c·(2λ)^c + 4·(2λ)^c + 2^{cλ} + 2. -/
theorem Data.Is.size_answer_le' {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size a ≤ (2 * g.1.length) ^ c * (2 * g.1.length) ^ c + 4 * (2 * g.1.length) ^ c + 2 ^ (c * g.1.length) + 2 := by
  have h1 := h.size_answer_le hg
  have h2 := two_mul_le_pow h.c_pos g.1.length
  have h3 := Nat.lt_two_pow_self (n := c * g.1.length)
  rw [Nat.mul_add] at h1
  omega

end PiecesCounted
