/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Enc

/-! The words of the constructors, their lengths, and `Carried` for every type former: the word of a
value is linear in its
size. -/

@[expose] public section

namespace Groundwork

open TM Enc

variable {α β : Type} [Enc α] [Enc β]

theorem wd_pair (a : α) (b : β) : wd (a, b) = .L :: (wd a ++ wd b ++ [.R]) := rfl
theorem wd_nil : wd ([] : List α) = [.L, .R] := rfl
theorem wd_cons (a : α) (l : List α) : wd (a :: l) = .L :: (wd a ++ wd l ++ [.R]) := rfl
theorem wd_none : wd (none : Option α) = [.L, .R] := rfl
theorem wd_some (a : α) : wd (some a) = .L :: (wd a ++ [.L, .R] ++ [.R]) := rfl
theorem wd_inl (a : α) : wd (Sum.inl a : α ⊕ β) = .L :: ([.bit false] ++ wd a ++ [.R]) := rfl
theorem wd_inr (b : β) : wd (Sum.inr b : α ⊕ β) = .L :: ([.bit true] ++ wd b ++ [.R]) := rfl
theorem wd_bool (b : Bool) : wd b = [.bit b] := rfl
/-- An integer is written as the pair of its sign (`true` if negative) and its absolute value. -/
theorem wd_int (z : ℤ) : wd z = wd (decide (z < 0), z.natAbs) := rfl

theorem len_pair (a : α) (b : β) : len (a, b) = len a + len b + 2 := by
  simp only [len, wd_pair, List.length_cons, List.length_append, List.length_nil]
theorem len_nil : len ([] : List α) = 2 := rfl
theorem len_cons (a : α) (l : List α) : len (a :: l) = len a + len l + 2 := by
  simp only [len, wd_cons, List.length_cons, List.length_append, List.length_nil]
/-- The word of `none` is a pair of brackets. -/
theorem len_none : len (none : Option α) = 2 := rfl
/-- The word of `some a` adds four brackets to the word of `a`. -/
theorem len_some (a : α) : len (some a) = len a + 4 := by
  simp only [len, wd_some, List.length_cons, List.length_append, List.length_nil]
/-- The word of a left injection adds a tag bit and two brackets. -/
theorem len_inl (a : α) : len (Sum.inl a : α ⊕ β) = len a + 3 := by
  simp only [len, wd_inl, List.length_cons, List.length_append, List.length_nil]; omega
/-- The word of a right injection adds a tag bit and two brackets. -/
theorem len_inr (b : β) : len (Sum.inr b : α ⊕ β) = len b + 3 := by
  simp only [len, wd_inr, List.length_cons, List.length_append, List.length_nil]; omega
/-- The word of a list has the words of its entries, two brackets for each entry and two more at the
end. -/
theorem len_list (l : List α) : len l = (l.map fun a => len a + 2).sum + 2 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [len_cons, ih, List.map_cons, List.sum_cons]; omega
/-- The words of `l` and `l'` together have two symbols more than the word of `l ++ l'`. -/
theorem len_append (l l' : List α) : len (l ++ l') + 2 = len l + len l' := by
  induction l with
  | nil => rw [List.nil_append, len_nil]; omega
  | cons a l ih => rw [List.cons_append, len_cons, len_cons]; omega
/-- A list has at most as many entries as its word has symbols. -/
theorem length_le_len (l : List α) : l.length ≤ len l := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => rw [len_cons, List.length_cons]; omega
/-- The word of an entry is no longer than the word of the list. -/
theorem len_le_of_mem {a : α} {l : List α} (h : a ∈ l) : len a ≤ len l := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [len_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega
/-- The word of a list has at least its two brackets. -/
theorem two_le_len_list (l : List α) : 2 ≤ len l := by
  rw [len_list]; omega
theorem len_drop_le (l : List α) (k : ℕ) : len (l.drop k) ≤ len l := by
  have h := len_append (l.take k) (l.drop k)
  rw [List.take_append_drop] at h
  have := two_le_len_list (l.take k)
  omega
/-- A truth value is one symbol. -/
theorem len_bool (b : Bool) : len b = 1 := rfl
/-- The one value of `Unit` is a pair of brackets. -/
theorem len_unit (u : Unit) : len u = 2 := rfl
/-- A list of truth values takes three symbols for each entry and two more at the end. -/
theorem len_bools (w : List Bool) : len w = 3 * w.length + 2 := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [len_cons, ih, List.length_cons, len_bool]; omega
/-- A list over `Unit` takes four symbols for each entry and two more at the end. -/
theorem len_units (w : List Unit) : len w = 4 * w.length + 2 := by
  induction w with
  | nil => rfl
  | cons u w ih => rw [len_cons, ih, List.length_cons, len_unit]; omega
/-- A natural number takes three symbols for each binary digit and two more at the end. -/
theorem len_nat (n : ℕ) : len n = 3 * Nat.size n + 2 := by
  rw [← Nat.size_eq_bits_len, ← len_bools]; rfl
/-- An integer takes the word of its absolute value, a sign bit and two brackets. -/
theorem len_int (z : ℤ) : len z = 3 * Nat.size z.natAbs + 5 := by
  have h : len z = len (decide (z < 0), z.natAbs) := rfl
  rw [h, len_pair, len_bool, len_nat]; omega
/-- A larger natural number has a word at least as long. -/
theorem len_nat_mono {m n : ℕ} (h : m ≤ n) : len m ≤ len n := by
  rw [len_nat, len_nat]; have := Nat.size_le_size h; omega
instance : Carried Unit := ⟨fun u => by rw [len_unit, size_unit]; omega⟩
instance : Carried Bool := ⟨fun b => by rw [len_bool, size_bool]; omega⟩
instance : Carried ℕ := ⟨fun n => by rw [len_nat, size_nat]; omega⟩
instance : Carried ℤ := ⟨fun z => by rw [len_int, size_int]; omega⟩
instance [HasSize α] [HasSize β] [Carried α] [Carried β] : Carried (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    have h₁ := Carried.le a
    have h₂ := Carried.le b
    rw [len_pair, size_prod]; dsimp only; omega⟩
instance [HasSize α] [HasSize β] [Carried α] [Carried β] : Carried (α ⊕ β) :=
  ⟨fun s => by
    rcases s with a | b
    · have := Carried.le a; rw [len_inl, size_inl]; omega
    · have := Carried.le b; rw [len_inr, size_inr]; omega⟩
instance [HasSize α] [Carried α] : Carried (Option α) :=
  ⟨fun o => by
    rcases o with _ | a
    · rw [len_none, size_none]; omega
    · have := Carried.le a; rw [len_some, size_some]; omega⟩
instance [HasSize α] [Carried α] : Carried (List α) :=
  ⟨fun l => by
    induction l with
    | nil => rw [len_nil]; simp
    | cons a l ih =>
      have := Carried.le a
      rw [size_list] at ih
      rw [len_cons, size_list, List.map_cons, List.sum_cons]; omega⟩

end Groundwork
