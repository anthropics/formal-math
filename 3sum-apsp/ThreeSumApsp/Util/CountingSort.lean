/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.SuccPred

/-!
# The pure side of counting sort

`N` items `0, …, N - 1` have keys `kf 0, …, kf (N - 1)`.  A stable sort by key puts item `j` at the
place `sortPos kf N j`: the number of items with a smaller key plus the number of earlier items with
the same key.

This is a bijection of `{0, …, N - 1}` (`eq_of_sortPos_eq`, `exists_sortPos_eq`) that is increasing
for the order "smaller key, or same key and earlier" (`sortPos_lt_sortPos_iff`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- The number of items `i < j` with key `t`. -/
def cntEq (kf : ℕ → ℕ) (t j : ℕ) : ℕ := Nat.count (fun i => kf i = t) j

/-- The number of items `i < j` with a key smaller than `t`. -/
def cntLt (kf : ℕ → ℕ) (t j : ℕ) : ℕ := Nat.count (fun i => kf i < t) j

/-- The place of item `j` after a stable sort of the items `0, …, N - 1` by key. -/
def sortPos (kf : ℕ → ℕ) (N j : ℕ) : ℕ := cntLt kf (kf j) N + cntEq kf (kf j) j

section
variable (kf : ℕ → ℕ)

@[simp] theorem cntEq_zero (t : ℕ) : cntEq kf t 0 = 0 := rfl

@[simp] theorem cntLt_zero_right (t : ℕ) : cntLt kf t 0 = 0 := rfl

@[simp] theorem cntLt_zero_left (j : ℕ) : cntLt kf 0 j = 0 := by simp [cntLt]

/-- One more item: it is counted if its key is `t`. -/
theorem cntEq_succ (t j : ℕ) : cntEq kf t (j + 1) = cntEq kf t j + if kf j = t then 1 else 0 :=
  Nat.count_succ _ _

/-- One more item: it is counted if its key is below `t`. -/
theorem cntLt_succ_right (t j : ℕ) :
    cntLt kf t (j + 1) = cntLt kf t j + if kf j < t then 1 else 0 := Nat.count_succ _ _

/-- Keys below `t + 1` are keys below `t` or equal to `t`. -/
theorem cntLt_succ_left (t j : ℕ) : cntLt kf (t + 1) j = cntLt kf t j + cntEq kf t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [cntLt_succ_right, cntLt_succ_right, cntEq_succ, ih]
    split_ifs <;> omega

/-- A larger bound counts more keys. -/
theorem cntLt_mono_left {s t : ℕ} (h : s ≤ t) (j : ℕ) : cntLt kf s j ≤ cntLt kf t j :=
  Nat.count_mono_left fun _ _ hlt => hlt.trans_le h

/-- At most all items are counted. -/
theorem cntLt_le (t j : ℕ) : cntLt kf t j ≤ j := Nat.count_le _

end

variable {kf : ℕ → ℕ} {N K : ℕ}

/-- The number of keys below `s` among the first `m` items depends on these items only. -/
theorem cntLt_congr {kf' : ℕ → ℕ} (s : ℕ) {m : ℕ} (h : ∀ i < m, kf i = kf' i) :
    cntLt kf s m = cntLt kf' s m :=
  le_antisymm (Nat.count_mono_left fun i hi hlt => h i hi ▸ hlt)
    (Nat.count_mono_left fun i hi hlt => (h i hi).symm ▸ hlt)

/-- If all keys are below `K`, all items are counted. -/
theorem cntLt_of_forall_lt (h : ∀ i < N, kf i < K) : cntLt kf K N = N :=
  Nat.count_iff_forall.mpr h

/-- Item `j` is itself one of the `N` items with its key. -/
theorem cntEq_lt_of_lt {j : ℕ} (hj : j < N) : cntEq kf (kf j) j < cntEq kf (kf j) N :=
  Nat.count_strict_mono (p := fun i => kf i = kf j) rfl hj

/-- The place of an item lies before the places of the larger keys. -/
theorem sortPos_lt_cntLt_succ {j : ℕ} (hj : j < N) : sortPos kf N j < cntLt kf (kf j + 1) N := by
  rw [cntLt_succ_left, sortPos]
  exact Nat.add_lt_add_left (cntEq_lt_of_lt hj) _

/-- The places are below `N`. -/
theorem sortPos_lt (kf : ℕ → ℕ) {j : ℕ} (hj : j < N) : sortPos kf N j < N :=
  calc sortPos kf N j < cntLt kf (kf j + 1) N := sortPos_lt_cntLt_succ hj
    _ ≤ N := cntLt_le ..

/-- A smaller key comes first; among equal keys the earlier item comes first. -/
theorem sortPos_lt_sortPos {i j : ℕ} (hi : i < N) (h : kf i < kf j ∨ (kf i = kf j ∧ i < j)) :
    sortPos kf N i < sortPos kf N j := by
  rcases h with hlt | ⟨heq, hij⟩
  · calc sortPos kf N i < cntLt kf (kf i + 1) N := sortPos_lt_cntLt_succ hi
      _ ≤ cntLt kf (kf j) N := cntLt_mono_left kf hlt N
      _ ≤ sortPos kf N j := Nat.le_add_right ..
  · rw [sortPos, sortPos, heq]
    exact Nat.add_lt_add_left (heq ▸ cntEq_lt_of_lt hij) _

/-- The order of the places is the order "smaller key, or same key and earlier". -/
theorem sortPos_lt_sortPos_iff {i j : ℕ} (hi : i < N) (hj : j < N) :
    sortPos kf N i < sortPos kf N j ↔ kf i < kf j ∨ (kf i = kf j ∧ i < j) := by
  refine ⟨fun h => ?_, sortPos_lt_sortPos hi⟩
  by_contra hc
  rcases (by omega : i = j ∨ kf j < kf i ∨ (kf j = kf i ∧ j < i)) with rfl | h'
  · omega
  · have := sortPos_lt_sortPos hj h'
    omega

/-- Different items get different places. -/
theorem eq_of_sortPos_eq {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : sortPos kf N i = sortPos kf N j) : i = j := by
  have hij := sortPos_lt_sortPos_iff (kf := kf) hi hj
  have hji := sortPos_lt_sortPos_iff (kf := kf) hj hi
  omega

/-- Every place is taken. -/
theorem exists_sortPos_eq (kf : ℕ → ℕ) {q : ℕ} (hq : q < N) : ∃ j < N, sortPos kf N j = q := by
  have hsurj := Finset.surjOn_of_injOn_of_card_le (s := Finset.range N) (t := Finset.range N)
    (sortPos kf N) (fun j hj => by simpa using sortPos_lt kf (by simpa using hj))
    (fun i hi j hj => eq_of_sortPos_eq (by simpa using hi) (by simpa using hj)) le_rfl
  simpa using hsurj (by simpa using hq)

end ThreeSumApsp
