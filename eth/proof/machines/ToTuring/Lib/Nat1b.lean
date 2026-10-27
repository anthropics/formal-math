/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Nat1

/-! Polynomial time for binary numbers: size, log2, single bits, and numbers computed from a list
(length, sum, counts, index
of an element). -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-! Helpers: how the number of binary digits grows, and the folds that compute the functions below. -/

private theorem size_succ_le (c : ℕ) : Nat.size (c + 1) ≤ Nat.size c + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self c
  omega

private theorem size_add_le (c e : ℕ) : Nat.size (c + e) ≤ Nat.size c + Nat.size e + 1 := by
  rw [Nat.size_le]
  have h1 := Nat.lt_size_self c
  have h2 := Nat.lt_size_self e
  have h3 : 2 ^ Nat.size c ≤ 2 ^ (Nat.size c + Nat.size e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ Nat.size e ≤ 2 ^ (Nat.size c + Nat.size e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

private theorem size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

private theorem foldl_succ_eq {β : Type} (l : List β) (n : ℕ) : l.foldl (fun c _ => c + 1) n = n + l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons e r ih => rw [List.foldl_cons, ih, List.length_cons]; omega

private theorem foldl_add_eq (l : List ℕ) (n : ℕ) : l.foldl (fun c e => c + e) n = n + l.sum := by
  induction l generalizing n with
  | nil => rfl
  | cons e r ih => rw [List.foldl_cons, ih, List.sum_cons]; omega

private theorem foldr_idxOf_eq {β : Type} [DecidableEq β] [BEq β] [LawfulBEq β] (a : β) (w : List β) :
    w.foldr (fun e c => if e = a then 0 else c + 1) 0 = w.idxOf a := by
  induction w with
  | nil => rfl
  | cons e r ih => simp [List.idxOf_cons, ih]

private theorem foldl_testBit_eq (i : ℕ) (w : List Bool) (c : ℕ) (r : Bool) :
    (w.foldl (fun (s : ℕ × Bool) e => (s.1 + 1, if s.1 = i then e else s.2)) (c, r)).2
      = if i < c then r else w.getD (i - c) r := by
  induction w generalizing c r with
  | nil => simp
  | cons e w ih =>
    rw [List.foldl_cons, ih]
    rcases lt_trichotomy i c with h | h | h
    · have h1 : i < c + 1 := by omega
      have h2 : c ≠ i := by omega
      simp [h, h1, h2]
    · subst h
      simp
    · have h1 : ¬ i < c + 1 := by omega
      have h2 : c ≠ i := by omega
      have h3 : ¬ i < c := by omega
      obtain ⟨d, rfl⟩ : ∃ d, i = c + 1 + d := ⟨i - (c + 1), by omega⟩
      have h4 : c + 1 + d - c = d + 1 := by omega
      simp [h1, h2, h3, h4]

private theorem log2_eq_size_sub (n : ℕ) : Nat.log2 n = Nat.size n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · have hs : 0 < Nat.size n := Nat.size_pos.2 h
    rw [Nat.log2_eq_iff (by omega)]
    refine ⟨Nat.lt_size.1 (by omega), ?_⟩
    have := Nat.lt_size_self n
    rwa [Nat.sub_add_cancel hs]

/-- The length of a list, in binary: a fold that adds 1 for every element. -/
@[fun_prop] theorem length {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).length) := by
  have h : PolyT (fun x => (l x).foldl (fun c _ => c + 1) 0) := by
    refine foldl_add (g := fun _ c _ => c + 1) hl (by fun_prop) (by fun_prop) ⟨fun _ => 3, PB.const 3, ?_⟩
    intro x c e _
    show len (c + 1) ≤ len c + 3
    have := size_succ_le c
    rw [len_nat, len_nat]
    omega
  exact h.congr fun x => by rw [foldl_succ_eq, Nat.zero_add]

/-- The number of binary digits of a number: the length of its list of digits. -/
@[fun_prop] theorem size' {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => Nat.size (f x)) :=
  (length (bits hf)).congr fun x => Nat.size_eq_bits_len (f x)

/-- The binary logarithm, rounded down: the number of binary digits minus 1. -/
@[fun_prop] theorem log2' {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => Nat.log2 (f x)) :=
  (pred (size' hf)).congr fun x => (log2_eq_size_sub (f x)).symm

/-- Bit number `g x` of `f x`: a fold over the binary digits that carries the position and the bit
found so far. -/
@[fun_prop] theorem testBit {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => (f x).testBit (g x)) := by
  have h : PolyT (fun x => (Nat.bits (f x)).foldl
      (fun (s : ℕ × Bool) e => (s.1 + 1, if s.1 = g x then e else s.2)) (0, false)) := by
    refine foldl_add (g := fun x (s : ℕ × Bool) e => (s.1 + 1, if s.1 = g x then e else s.2)) (bits hf) (by fun_prop)
      (by fun_prop) ⟨fun _ => 3, PB.const 3, ?_⟩
    rintro x ⟨c, r⟩ e _
    show len (c + 1, if c = g x then e else r) ≤ len (c, r) + 3
    have := size_succ_le c
    have hb : ∀ b : Bool, len b = 1 := fun _ => rfl
    rw [len_pair, len_pair, len_nat, len_nat, hb, hb]
    omega
  refine (snd h).congr fun x => ?_
  rw [foldl_testBit_eq, Nat.testBit_eq_inth]
  simp [List.getI_eq_getElem?_getD]

/-- The sum of a list of numbers: a fold that adds the elements. -/
@[fun_prop] theorem sum {l : α → List ℕ} (hl : PolyT l) :
    PolyT (fun x => (l x).sum) := by
  obtain ⟨_, t, ht, -, -, hlen⟩ := hl.elim
  have h : PolyT (fun x => (l x).foldl (fun c e => c + e) 0) := by
    refine foldl_add (g := fun _ c e => c + e) hl (by fun_prop) (by fun_prop)
      ⟨fun n => t n + 1, ht.add (PB.const 1), ?_⟩
    intro x c e he
    show len (c + e) ≤ len c + (t (len x) + 1)
    have h1 := len_le_of_mem he
    have h2 := hlen x
    have h3 := size_add_le c e
    rw [len_nat] at h1
    rw [len_nat, len_nat]
    omega
  exact h.congr fun x => by rw [foldl_add_eq, Nat.zero_add]

/-- The number of elements that pass a test: the length of the filtered list. -/
@[fun_prop] theorem countP {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).countP (f x)) :=
  (length (filter hf hl)).congr fun _ => List.countP_eq_length_filter.symm

/-- The number of occurrences of an element: `countP` with the test of equality (`BEq` as for
`PolyT.beq'`). -/
@[fun_prop] theorem count [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).count (b x)) :=
  (countP (f := fun x e => decide (e = b x)) (by fun_prop) hl).congr fun x => by
    rw [List.count]
    exact congrArg (fun p => List.countP p (l x)) (funext fun e => (beq_eq_decide e (b x)).symm)

/-- The index of the first occurrence of an element (the length of the list if there is none): a
fold from the right (`BEq` as
for `PolyT.beq'`). -/
@[fun_prop] theorem idxOf [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).idxOf (b x)) := by
  obtain ⟨_, t, ht, -, -, hlen⟩ := hl.elim
  have h : PolyT (fun x => (l x).foldr (fun e c => if e = b x then 0 else c + 1) 0) := by
    refine foldr (g := fun x e c => if e = b x then 0 else c + 1) hl (by fun_prop) (by fun_prop)
      ⟨fun n => 3 * t n + 2, ((PB.const 3).mul ht).add (PB.const 2), ?_⟩
    intro x k
    show len (((l x).drop k).foldr (fun e c => if e = b x then 0 else c + 1) 0) ≤ 3 * t (len x) + 2
    rw [foldr_idxOf_eq, len_nat]
    have h1 : ((l x).drop k).idxOf (b x) ≤ ((l x).drop k).length := List.idxOf_le_length
    have h2 : ((l x).drop k).length ≤ (l x).length := by rw [List.length_drop]; omega
    have h3 := size_le_self (((l x).drop k).idxOf (b x))
    have h4 := length_le_len (l x)
    have h5 := hlen x
    omega
  exact h.congr fun x => foldr_idxOf_eq (b x) (l x)

end Groundwork.PolyT
