/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Binary numbers, the first bit is the highest
-/

namespace Nc.Uni

/-- The value of a word of bits. -/
def bv : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 2 ^ w.length else 0) + bv w

theorem bv_lt (w : List Bool) : bv w < 2 ^ w.length := by
  induction w with
  | nil => simp [bv]
  | cons b w ih =>
    simp only [bv, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem bv_inj {w w' : List Bool} (h : w.length = w'.length) (e : bv w = bv w') : w = w' := by
  induction w generalizing w' with
  | nil => exact (List.length_eq_zero_iff.1 h.symm).symm
  | cons b w ih =>
    rcases w' with _ | ⟨b', w'⟩
    · simp at h
    · have hl : w.length = w'.length := by simpa using h
      have h1 := bv_lt w
      have h2 := bv_lt w'
      simp only [bv, hl] at e
      rw [hl] at h1
      have hb : b = b' := by
        cases b <;> cases b' <;> simp at e ⊢ <;> omega
      subst hb
      have : bv w = bv w' := by omega
      rw [ih hl this]

/-- The word of L bits of a number. -/
def bin : ℕ → ℕ → List Bool
  | 0, _ => []
  | L + 1, n => decide (2 ^ L ≤ n) :: bin L (if 2 ^ L ≤ n then n - 2 ^ L else n)

theorem length_bin (L n : ℕ) : (bin L n).length = L := by
  induction L generalizing n with
  | zero => rfl
  | succ L ih => rw [bin, List.length_cons, ih]

theorem bv_bin {L n : ℕ} (h : n < 2 ^ L) : bv (bin L n) = n := by
  induction L generalizing n with
  | zero =>
    simp at h
    simp [bin, bv, h]
  | succ L ih =>
    rw [bin, bv, length_bin]
    rw [pow_succ] at h
    by_cases hn : 2 ^ L ≤ n
    · simp only [hn, decide_true, if_true]
      rw [ih (by omega)]
      omega
    · simp only [hn, decide_false, Bool.false_eq_true, if_false]
      rw [ih (by omega)]
      omega

theorem bin_bv (w : List Bool) : bin w.length (bv w) = w :=
  bv_inj (length_bin _ _) (bv_bin (bv_lt w))

theorem bv_append (u v : List Bool) : bv (u ++ v) = bv u * 2 ^ v.length + bv v := by
  induction u with
  | nil => simp [bv]
  | cons b u ih =>
    rw [List.cons_append, bv, bv, ih, List.length_append, pow_add]
    split_ifs <;> ring

theorem bv_false (k : ℕ) : bv (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, bv, ih]

theorem bv_true (k : ℕ) : bv (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, bv, List.length_replicate, if_pos rfl, pow_succ]
    omega

/-- The successor of a word. -/
theorem bv_succ (u : List Bool) (k : ℕ) :
    bv (u ++ true :: List.replicate k false) = bv (u ++ false :: List.replicate k true) + 1 := by
  have h := bv_true k
  rw [bv_append, bv_append, bv, bv, bv_false]
  simp only [if_true, Bool.false_eq_true, if_false, List.length_cons, List.length_replicate]
  omega

/-- A word that has a successor ends with 0 1 ⋯ 1. -/
theorem exists_cut {w : List Bool} (h : bv w + 1 < 2 ^ w.length) :
    ∃ u k, w = u ++ false :: List.replicate k true := by
  induction w using List.reverseRecOn with
  | nil => simp [bv] at h
  | append_singleton w b ih =>
    cases b
    · exact ⟨w, 0, rfl⟩
    · rw [bv_append, List.length_append, pow_add] at h
      simp only [bv, List.length_nil, List.length_singleton, pow_zero, pow_one, if_true] at h
      obtain ⟨u, k, rfl⟩ := ih (by omega)
      refine ⟨u, k + 1, ?_⟩
      rw [List.replicate_succ', List.append_assoc]
      rfl

theorem cut_unique {u u' : List Bool} {k k' : ℕ}
    (h : u ++ false :: List.replicate k true = u' ++ false :: List.replicate k' true) : u = u' ∧ k = k' := by
  have h1 := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append] at h1
  have key : ∀ (k k' : ℕ) (a b : List Bool), List.replicate k true ++ false :: a = List.replicate k' true ++ false :: b →
      k = k' ∧ a = b := by
    intro k
    induction k with
    | zero =>
      intro k' a b e
      cases k' with
      | zero => simpa using e
      | succ k' => simp [List.replicate_succ] at e
    | succ k ih =>
      intro k' a b e
      cases k' with
      | zero => simp [List.replicate_succ] at e
      | succ k' =>
        simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at e
        obtain ⟨h2, h3⟩ := ih k' a b e
        exact ⟨by rw [h2], h3⟩
  obtain ⟨h2, h3⟩ := key k k' _ _ h1
  exact ⟨List.reverse_injective h3, h2⟩

end Nc.Uni
