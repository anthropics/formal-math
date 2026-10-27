/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.EncLemmas

/-! Three small facts about lists: the length of the word of a list whose members are short, the
length of a `flatMap`, and a sum over a
`flatMap`. They are used for the work list of the descent and for the stack of the walk. Here `len`
is the length of the word that stands
for a value on a stack. -/

public section

namespace PaddedDescent.F.Lists

open Groundwork

/-- A list of k values, each with a word of length at most c − 2, has a word of length at most k·c + 2. -/
theorem len_list_le {α : Type} [Enc α] (w : List α) (c : ℕ) (h : ∀ a ∈ w, len a + 2 ≤ c) : len w ≤ w.length * c + 2 := by
  induction w with
  | nil => simp [len_nil]
  | cons a w ih =>
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    rw [len_cons, List.length_cons]
    nlinarith

/-- The same when only a bound k on the number of members is known. -/
theorem len_list_le' {α : Type} [Enc α] (w : List α) {k : ℕ} (c : ℕ) (hk : w.length ≤ k) (h : ∀ a ∈ w, len a + 2 ≤ c) :
    len w ≤ k * c + 2 :=
  (len_list_le w c h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 2)

/-- If e a has at most c members for every member a of w, then w.flatMap e has at most (length of
w)·c members. -/
theorem length_flatMap_le {α β : Type*} (w : List α) (e : α → List β) (c : ℕ) (h : ∀ a ∈ w, (e a).length ≤ c) :
    (w.flatMap e).length ≤ w.length * c := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-- The sum of z over w.flatMap e is the sum, over the members a of w, of the sums of z over e a. -/
theorem sum_map_flatMap {α β : Type*} (w : List α) (e : α → List β) (z : β → ℤ) :
    ((w.flatMap e).map z).sum = (w.map fun a => ((e a).map z).sum).sum := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [List.flatMap_cons, ih]

end PaddedDescent.F.Lists
