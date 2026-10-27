/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Nat1b
public import StepMachines.Prog.Chunks

/-! Polynomial time for lists indexed by numbers: drop, take and lookup at a binary position; range
with a unary
length; words of binary digits and chunks. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-- The loop behind drop: a counter that goes down and a list that loses its head as long as the
counter is positive. -/
private theorem foldl_drop {ε β : Type} (m : List ε) (n : ℕ) (l : List β) :
    m.foldl (fun (s : ℕ × List β) (_ : ε) => (s.1 - 1, if s.1 = 0 then s.2 else s.2.tail)) (n, l)
      = (n - m.length, l.drop (min n m.length)) := by
  induction m generalizing n l with
  | nil => simp
  | cons e m ih =>
    rw [List.foldl_cons, ih]
    cases n with
    | zero => simp
    | succ n => simp

private theorem drop_min_length {β : Type} (n : ℕ) (l : List β) : l.drop (min n l.length) = l.drop n := by
  rcases Nat.le_total n l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_length, List.drop_eq_nil_of_le h]

@[fun_prop] theorem drop {n : α → ℕ} {l : α → List β} (hn : PolyT n) (hl : PolyT l) :
    PolyT (fun x => (l x).drop (n x)) := by
  have h : PolyT fun x => (l x).foldl
      (fun (s : ℕ × List β) (_ : β) => (s.1 - 1, if s.1 = 0 then s.2 else s.2.tail)) (n x, l x) := by
    refine foldl_add (g := fun _ (s : ℕ × List β) (_ : β) => (s.1 - 1, if s.1 = 0 then s.2 else s.2.tail))
      hl (by fun_prop) (by fun_prop) ⟨fun _ => 0, PB.const 0, ?_⟩
    rintro x ⟨k, r⟩ e -
    have h1 : len (k - 1) ≤ len k := len_nat_mono (Nat.sub_le k 1)
    have h2 : len (if k = 0 then r else r.tail) ≤ len r := by
      split_ifs
      · exact le_rfl
      · rw [← List.drop_one]; exact len_drop_le r 1
    simp only [len_pair]
    omega
  exact h.snd.congr fun x => by rw [foldl_drop, drop_min_length]

@[fun_prop] theorem take {n : α → ℕ} {l : α → List β} (hn : PolyT n) (hl : PolyT l) :
    PolyT (fun x => (l x).take (n x)) := by
  have h : PolyT fun x => ((l x).reverse.drop ((l x).length - n x)).reverse := by fun_prop
  exact h.congr fun x => by
    have := List.take_reverse (xs := (l x).reverse) (i := n x)
    simpa using this.symm

@[fun_prop] theorem getElem? {n : α → ℕ} {l : α → List β} (hl : PolyT l) (hn : PolyT n) :
    PolyT (fun x => (l x)[n x]?) := by
  have h : PolyT fun x => ((l x).drop (n x)).head? := by fun_prop
  exact h.congr fun x => List.head?_drop

@[fun_prop] theorem getD {n : α → ℕ} {l : α → List β} {d : α → β} (hl : PolyT l) (hn : PolyT n) (hd : PolyT d) :
    PolyT (fun x => (l x).getD (n x) (d x)) := by
  have h : PolyT fun x => ((l x)[n x]?).getD (d x) := by fun_prop
  exact h.congr fun x => List.getD_eq_getElem?_getD.symm

/-- The loop behind range: append the length. -/
private theorem foldl_range {ε : Type} (m : List ε) (j : ℕ) :
    m.foldl (fun (a : List ℕ) (_ : ε) => a ++ [a.length]) (List.range j) = List.range (j + m.length) := by
  induction m generalizing j with
  | nil => simp
  | cons e m ih =>
    rw [List.foldl_cons, List.length_range, ← List.range_succ, ih, List.length_cons]
    congr 1; omega

private theorem len_range_le {m M : ℕ} (h : m ≤ M) : len (List.range m) ≤ m * (3 * M + 4) + 2 := by
  induction m with
  | zero => simp [len_nil]
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := len_append (List.range m) [m]
    have h3 : len [m] = len m + 4 := by rw [len_cons, len_nil]
    have h4 : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self
    rw [List.range_succ, Nat.succ_mul]
    rw [h3, len_nat] at h2
    omega

/-- The length must be given in unary, since the result is that long. -/
theorem range {n : α → ℕ} (hn : Unary n) :
    PolyT (fun x => List.range (n x)) := by
  have hn' : PolyT fun x => List.replicate (n x) () := hn
  obtain ⟨-, t, ht, -, -, hlen⟩ := hn'.elim
  have h : PolyT fun x => (List.replicate (n x) ()).foldl
      (fun (a : List ℕ) (_ : Unit) => a ++ [a.length]) (List.range 0) := by
    refine foldl (g := fun _ (a : List ℕ) (_ : Unit) => a ++ [a.length]) hn' (by fun_prop) (by fun_prop)
      ⟨fun N => t N * (3 * t N + 4) + 2, (ht.mul (((PB.const 3).mul ht).add (PB.const 4))).add (PB.const 2), ?_⟩
    intro x k
    rw [foldl_range]
    have h1 : 0 + ((List.replicate (n x) ()).take k).length ≤ t (len x) := by
      have := length_le_len (List.replicate (n x) ())
      have := hlen x
      have := List.length_take_le' k (List.replicate (n x) ())
      omega
    exact (len_range_le h1).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h1) 2)
  exact h.congr fun x => by rw [foldl_range]; simp

private theorem foldr_bit (w : List Bool) : w.foldr Nat.bit 0 = ofWord w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [List.foldr_cons, ih, ofWord, Nat.bit_val, Nat.add_comm]

/-- The number whose binary digits are the word, lowest digit first. -/
@[fun_prop] theorem ofWord' {w : α → List Bool} (hw : PolyT w) :
    PolyT (fun x => ofWord (w x)) :=
  (ofBits hw).congr fun x => foldr_bit (w x)

private theorem toWord_eq (n y : ℕ) : toWord n y = (List.range n).map fun i => y.testBit i := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp [toWord, ih, List.range_succ_eq_map, Nat.testBit_succ, Function.comp_def]

/-- The n lowest binary digits of y, lowest digit first; the length n must be given in unary. -/
theorem toWord' {n y : α → ℕ} (hn : Unary n) (hy : PolyT y) :
    PolyT (fun x => toWord (n x) (y x)) := by
  have hr := range hn
  have h : PolyT fun x => (List.range (n x)).map fun i => (y x).testBit i := by fun_prop
  exact h.congr fun x => (toWord_eq _ _).symm

/-- The loop behind chunks: what is left of the word, and the chunks cut so far, last one first. -/
private theorem foldl_chunks (cs : List ℕ) (w : List Bool) (a : List (List Bool)) :
    (cs.foldl (fun (s : List Bool × List (List Bool)) (c : ℕ) => (s.1.drop c, s.1.take c :: s.2)) (w, a)).2
      = (chunks cs w).reverse ++ a := by
  induction cs generalizing w a with
  | nil => rfl
  | cons c cs ih => rw [List.foldl_cons, ih, chunks, List.reverse_cons, List.append_assoc]; rfl

/-- Cutting a word into consecutive pieces of the given lengths. -/
@[fun_prop] theorem chunks' {cs : α → List ℕ} {w : α → List Bool} (hc : PolyT cs) (hw : PolyT w) :
    PolyT (fun x => chunks (cs x) (w x)) := by
  have h : PolyT fun x => (cs x).foldl
      (fun (s : List Bool × List (List Bool)) (c : ℕ) => (s.1.drop c, s.1.take c :: s.2)) (w x, []) := by
    refine foldl_add (g := fun _ (s : List Bool × List (List Bool)) (c : ℕ) => (s.1.drop c, s.1.take c :: s.2))
      hc (by fun_prop) (by fun_prop) ⟨fun _ => 4, PB.const 4, ?_⟩
    rintro x ⟨v, a⟩ c -
    have h1 := len_append (v.take c) (v.drop c)
    rw [List.take_append_drop] at h1
    simp only [len_pair, len_cons]
    omega
  exact h.snd.reverse.congr fun x => by rw [foldl_chunks]; simp

end Groundwork.PolyT
