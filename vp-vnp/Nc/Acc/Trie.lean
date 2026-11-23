/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Util

/-!
# Full tries of constants; reading in a tree of pairs
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

/-- All names of length `n`. -/
def full : ℕ → (List Bool → R) → KT R
  | 0, f => leaf (f [])
  | n + 1, f => node (full n fun w => f (false :: w)) (full n fun w => f (true :: w))

theorem lk_full {n : ℕ} (f : List Bool → R) {w : List Bool} (h : w.length = n) : (full n f).lk (w ++ [false]) = f w := by
  induction n generalizing f w with
  | zero =>
    rw [List.length_eq_zero_iff] at h
    subst h
    rfl
  | succ n ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      rw [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b with
      | true => exact ih (fun w => f (true :: w)) h
      | false => exact ih (fun w => f (false :: w)) h

theorem inB_full {n : ℕ} (f : List Bool → R) {w : List Bool} (h : w.length = n) : (full n f).InB 1 (w ++ [false]) := by
  induction n generalizing f w with
  | zero =>
    rw [List.length_eq_zero_iff] at h
    subst h
    exact ⟨0, zero_lt_one, rfl⟩
  | succ n ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      rw [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b with
      | true => exact ih (fun w => f (true :: w)) h
      | false => exact ih (fun w => f (false :: w)) h

theorem nds_full (n : ℕ) (f : List Bool → R) : (full n f).nds + 1 = 2 ^ (n + 1) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have h1 := ih fun w => f (false :: w)
    have h2 := ih fun w => f (true :: w)
    rw [full, nds, pow_succ]
    omega

theorem ht_full (n : ℕ) (f : List Bool → R) : (full n f).ht = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [full, ht, ih, ih, max_self]

end KT

/-- All words of a given length. -/
def wd : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (wd m).map (true :: ·) ++ (wd m).map (false :: ·)

theorem length_of_mem_wd {m : ℕ} {w : List Bool} (h : w ∈ wd m) : w.length = m := by
  induction m generalizing w with
  | zero =>
    simp only [wd, List.mem_singleton] at h
    subst h
    rfl
  | succ m ih =>
    simp only [wd, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

theorem val_lt_of_length {m : ℕ} {w : List Bool} (h : w.length = m) : KT.val w < 2 ^ m := by
  induction w generalizing m with
  | nil =>
    subst h
    simp [KT.val]
  | cons b w ih =>
    subst h
    have := ih rfl
    rw [KT.val, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem exists_word {m k : ℕ} (h : k < 2 ^ m) : ∃ w : List Bool, w.length = m ∧ KT.val w = k := by
  induction m generalizing k with
  | zero => exact ⟨[], rfl, by simp [KT.val]; omega⟩
  | succ m ih =>
    rw [pow_succ] at h
    obtain ⟨w, h1, h2⟩ := ih (k := k / 2) (by omega)
    refine ⟨decide (k % 2 = 1) :: w, by simp [h1], ?_⟩
    rw [KT.val, h2]
    by_cases h3 : k % 2 = 1
    · simp [h3]
      omega
    · simp [h3]
      omega

/-- Sums over words. -/
theorem sum_wd (m : ℕ) (f : ℕ → R) : ((wd m).map fun w => f (KT.val w)).sum = ∑ k ∈ Finset.range (2 ^ m), f k := by
  induction m generalizing f with
  | zero => simp [wd, KT.val]
  | succ m ih =>
    have h1 := ih fun k => f (1 + 2 * k)
    have h2 := ih fun k => f (2 * k)
    have e1 : ((wd (m + 1)).map fun w => f (KT.val w)).sum =
        ((wd m).map fun w => f (1 + 2 * KT.val w)).sum + ((wd m).map fun w => f (2 * KT.val w)).sum := by
      simp [wd, KT.val, Function.comp_def]
    rw [e1, h1, h2, pow_succ, mul_comm]
    clear e1 h1 h2 ih
    induction 2 ^ m with
    | zero => simp
    | succ n ih =>
      rw [mul_add, mul_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        ← ih]
      have e : 1 + 2 * n = 2 * n + 1 := by ring
      rw [e]
      ring

/-- Sums over reversed words. -/
theorem sum_wd_reverse (m : ℕ) (f : List Bool → R) :
    ((wd m).map fun w => f w.reverse).sum = ((wd m).map f).sum := by
  have h : ∀ (n : ℕ) (f : List Bool → R), ((wd (n + 1)).map f).sum =
      ((wd n).map fun w => f (w ++ [true])).sum + ((wd n).map fun w => f (w ++ [false])).sum := by
    intro n
    induction n with
    | zero => intro f; simp [wd]
    | succ n ih =>
      intro f
      have e : ((wd (n + 1 + 1)).map f).sum = ((wd (n + 1)).map fun w => f (true :: w)).sum +
          ((wd (n + 1)).map fun w => f (false :: w)).sum := by
        rw [wd]
        simp [Function.comp_def]
      rw [e, ih, ih]
      have e2 : ∀ b : Bool, ((wd (n + 1)).map fun w => f (w ++ [b])).sum =
          ((wd n).map fun w => f (true :: (w ++ [b]))).sum + ((wd n).map fun w => f (false :: (w ++ [b]))).sum := by
        intro b
        simp [wd, Function.comp_def]
      rw [e2, e2]
      ring
  induction m generalizing f with
  | zero => simp [wd]
  | succ m ih =>
    rw [h m f]
    have e : ((wd (m + 1)).map fun w => f w.reverse).sum = ((wd m).map fun w => f (w.reverse ++ [true])).sum +
        ((wd m).map fun w => f (w.reverse ++ [false])).sum := by
      simp [wd, Function.comp_def]
    rw [e, ih fun w => f (w ++ [true]), ih fun w => f (w ++ [false])]

/-- Reading along a path. -/
def look : List Bool → Tree → Tree
  | [], t => t
  | true :: p, t => look p t.tl
  | false :: p, t => look p t.hd

theorem look_append (p q : List Bool) (t : Tree) : look (p ++ q) t = look q (look p t) := by
  induction p generalizing t with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih _

/-- Pairs of neighbours. -/
def pairL : List Tree → List Tree
  | [] => []
  | [a] => [.cons a .nil]
  | a :: b :: l => .cons a b :: pairL l

theorem length_pairL (l : List Tree) : (pairL l).length = (l.length + 1) / 2 := by
  induction l using pairL.induct with
  | case1 => rfl
  | case2 a => simp [pairL]
  | case3 a b l ih =>
    simp only [pairL, List.length_cons, ih]
    omega

theorem getD_pairL (l : List Tree) (k : ℕ) : ((pairL l).getD k .nil).hd = l.getD (2 * k) .nil ∧
    ((pairL l).getD k .nil).tl = l.getD (1 + 2 * k) .nil := by
  induction l using pairL.induct generalizing k with
  | case1 => simp [pairL]
  | case2 a =>
    cases k with
    | zero => simp [pairL]
    | succ k => simp [pairL]
  | case3 a b l ih =>
    cases k with
    | zero => simp [pairL]
    | succ k =>
      have h := ih k
      have e1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have e2 : 1 + 2 * (k + 1) = 1 + 2 * k + 1 + 1 := by ring
      rw [e2, e1]
      simpa only [pairL, List.getD_cons_succ] using h

/-- Reading in the tree of pairs. -/
theorem look_pairs (m : ℕ) (xs : List Tree) (hx : xs.length ≤ 2 ^ m) (p : List Bool) (hp : p.length = m) :
    look p (listT (pairL^[m] xs)).hd = xs.getD (KT.val p.reverse) .nil := by
  induction m generalizing xs p with
  | zero =>
    rw [List.length_eq_zero_iff] at hp
    subst hp
    cases xs <;> rfl
  | succ m ih =>
    obtain ⟨p, b, rfl⟩ : ∃ q b, p = q ++ [b] := by
      rcases List.eq_nil_or_concat p with rfl | ⟨q, b, h⟩
      · simp at hp
      · exact ⟨q, b, by simpa using h⟩
    rw [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hp
    rw [Function.iterate_succ_apply, look_append, ih (pairL xs) (by rw [length_pairL]; rw [pow_succ] at hx; omega) p hp,
      List.reverse_append, List.reverse_singleton, List.singleton_append, KT.val]
    have h := getD_pairL xs (KT.val p.reverse)
    cases b with
    | true => exact h.2
    | false =>
      have e : (if false = true then 1 else 0) + 2 * KT.val p.reverse = 2 * KT.val p.reverse := by simp
      rw [e]
      exact h.1

end NS1
