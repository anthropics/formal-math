/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.PolyT
import ToTuring.Closure.Fold
import ToTuring.Lib.List1b
import ToTuring.Lib.Nat1b
import ToTuring.Lib.Bool

/-! # The word of a value against a padding string

A fragment sees the tree of a value and not its type. `vSplit` takes a tree apart (empty, a bit, or
a pair); its fragment, with the head statement `bitHead`, is the one piece of code for the Turing
machine that this file adds. `visit` works on a list of trees still to be visited and a count: it
takes the first tree off the list, adds the number of symbols that are its own (2 for the empty tree
and for a pair, 1 for
a bit) to the count, and puts the two parts of a pair back on the list. Every round visits one node,
and a word has at least as many symbols as its tree has nodes. So after as many rounds as the
padding string has units either the list is empty, and the count is the length of the word, or the
word is longer than the padding
string. -/

public section

namespace QueryMachines.Bridge.Proof

open Turing Groundwork Groundwork.TM Groundwork.PolyT

/-- The coding of a tree is the tree itself. -/
scoped instance encV : Enc V := ⟨id⟩

/-! ### Taking a tree apart -/

/-- Takes a tree apart: empty, a bit, or the two parts of a pair. -/
def vSplit : V → Unit ⊕ (Bool ⊕ V × V)
  | .nil => .inl ()
  | .bit b => .inr (.inl b)
  | .cons x y => .inr (.inr (x, y))

/-- Look at the symbol on top of the main stack: an opening bracket gives the label false, anything
else the label true. At the start of the word of a tree the symbol is an opening bracket or a bit,
so there the label true means a bit. The stack is left as it was. -/
def bitHead : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym) :=
  .peek .main (fun _ o => o) <|
    .branch (fun s => s == some .L) (.load (fun _ => none) <| .goto fun _ => false) (.load (fun _ => none) <| .goto fun _ => true)

/-- On a bit the head statement gives the label true and leaves the stacks as they were. -/
theorem bitHead_bit (b : Bool) (M A B N : List Sym) : TM2.stepAux bitHead none (st (.bit b :: M) A B N) = ⟨some true, none, st (.bit b :: M) A B N⟩ := by
  simp [bitHead, TM2.stepAux]

/-- On an opening bracket the head statement gives the label false and leaves the stacks as they
were. -/
theorem bitHead_L (M A B N : List Sym) : TM2.stepAux bitHead none (st (.L :: M) A B N) = ⟨some false, none, st (.L :: M) A B N⟩ := by
  simp [bitHead, TM2.stepAux]

/-- A tag in front adds three symbols to the word. -/
theorem length_code_tag (b : Bool) (x : V) : (code (.cons (.bit b) x)).length = (code x).length + 3 := by
  simp [code]

/-- Taking a tree apart is polynomial-time: look at the first symbol, for a bracket at the second,
and put the one or two tags in front. -/
theorem vSplit_poly : PolyT vSplit := by
  refine PolyT.of (Frag.branch bitHead ((tagF false).seq (tagF true)) (Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)))
    (t := fun n => 4 * n + 30) (s := fun n => n + 6) (((PB.const 4).mul PB.id').add (PB.const 30)) (PB.id'.add (PB.const 6)) (fun v M A B N => ?_) (fun v => ?_)
  · have hl : len v = (code v).length := rfl
    cases v with
    | nil =>
      have c := tagF_within false .nil M A B N
      have h1 := within_branch (P := (tagF true).seq (tagF true)) (Q := tagF false) false (nilHead_nil M A B N) c
      have h2 := within_branch (P := (tagF false).seq (tagF true)) (Q := Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)) false (bitHead_L (.R :: M) A B N) h1
      exact h2.mono (by rw [hl]; omega)
    | bit b =>
      have c1 := tagF_within false (.bit b) M A B N
      have c2 := tagF_within true (.cons (.bit false) (.bit b)) M A B N
      have h2 := within_branch (P := (tagF false).seq (tagF true)) (Q := Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)) true (bitHead_bit b M A B N) (c1.seq c2)
      exact h2.mono (by rw [hl, length_code_tag]; omega)
    | cons x y =>
      have e0 : code (.cons x y) ++ M = .L :: (code x ++ (code y ++ [.R] ++ M)) := by simp [code]
      have hn := nilHead_cons x (code y ++ [.R] ++ M) A B N
      have hb := bitHead_L (code x ++ (code y ++ [.R] ++ M)) A B N
      rw [← e0] at hn hb
      have c1 := tagF_within true (.cons x y) M A B N
      have c2 := tagF_within true (.cons (.bit true) (.cons x y)) M A B N
      have h1 := within_branch (P := (tagF true).seq (tagF true)) (Q := tagF false) true hn (c1.seq c2)
      have h2 := within_branch (P := (tagF false).seq (tagF true)) (Q := Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)) false hb h1
      exact h2.mono (by rw [hl, length_code_tag]; omega)
  · cases v with
    | nil => exact (by decide : (5 : ℕ) ≤ 2 + 6)
    | bit b => exact (by decide : (7 : ℕ) ≤ 1 + 6)
    | cons x y =>
      show (code (.cons (.bit true) (.cons (.bit true) (.cons x y)))).length ≤ (code (.cons x y)).length + 6
      rw [length_code_tag, length_code_tag]

/-- The same in the form that the tactic `fun_prop` uses; in this file only. -/
@[local fun_prop] theorem vSplit' {α : Type} [Enc α] {f : α → V} (hf : PolyT f) : PolyT fun x => vSplit (f x) := comp vSplit_poly hf

/-! ### One round -/

/-- Visit the first tree of the list. -/
def visit (s : List V × ℕ) : List V × ℕ :=
  s.1.head?.elim s fun v => (vSplit v).elim (fun _ => (s.1.tail, s.2 + 2)) fun t => t.elim (fun _ => (s.1.tail, s.2 + 1)) fun p => (p.1 :: p.2 :: s.1.tail, s.2 + 2)

/-- One round is polynomial-time. -/
theorem visit_poly : PolyT visit := by unfold visit; fun_prop

/-- The symbols of the trees still to be visited. -/
def total (w : List V) : ℕ := (w.map fun v => (code v).length).sum

/-- The number of nodes of a tree. -/
def nodes : V → ℕ
  | .nil => 1
  | .bit _ => 1
  | .cons x y => nodes x + nodes y + 1

/-- The nodes still to be visited. -/
def work (w : List V) : ℕ := (w.map nodes).sum

/-- A tree has at least one node. -/
theorem nodes_pos : ∀ v : V, 1 ≤ nodes v
  | .nil => le_rfl
  | .bit _ => le_rfl
  | .cons _ _ => Nat.le_add_left _ _

/-- A tree has at most as many nodes as its word has symbols. -/
theorem nodes_le : ∀ v : V, nodes v ≤ (code v).length
  | .nil => by simp [nodes, code]
  | .bit _ => by simp [nodes, code]
  | .cons x y => by have := nodes_le x; have := nodes_le y; simp [nodes, code]; omega

/-- A round keeps the sum of the count and the symbols still to be visited. -/
theorem visit_total (s : List V × ℕ) : (visit s).2 + total (visit s).1 = s.2 + total s.1 := by
  rcases s with ⟨_ | ⟨v, r⟩, c⟩
  · rfl
  · cases v <;> simp [visit, vSplit, total, code] <;> omega

/-- A round on a list that is not empty visits exactly one node. -/
theorem visit_work (v : V) (r : List V) (c : ℕ) : work (visit (v :: r, c)).1 + 1 = work (v :: r) := by
  cases v <;> simp [visit, vSplit, work, nodes] <;> omega

/-- So do any number of rounds keep that sum. -/
theorem fold_total (l : List Unit) : ∀ s : List V × ℕ, (l.foldl (fun s _ => visit s) s).2 + total (l.foldl (fun s _ => visit s) s).1 = s.2 + total s.1 := by
  induction l with
  | nil => intro s; rfl
  | cons u l ih => intro s; rw [List.foldl_cons, ih, visit_total]

/-- After at least as many rounds as there are nodes the list is empty. -/
theorem fold_done (l : List Unit) : ∀ s : List V × ℕ, work s.1 ≤ l.length → (l.foldl (fun s _ => visit s) s).1 = [] := by
  induction l with
  | nil =>
    rintro ⟨_ | ⟨v, r⟩, c⟩ h
    · rfl
    · have := nodes_pos v
      simp [work] at h
      omega
  | cons u l ih =>
    rintro ⟨_ | ⟨v, r⟩, c⟩ h
    · exact ih ([], c) (Nat.zero_le _)
    · rw [List.foldl_cons]
      refine ih _ ?_
      have h1 := visit_work v r c
      have h2 : work (v :: r) ≤ l.length + 1 := h
      omega

/-! ### The comparison -/

/-- As many rounds as the padding string has units; then: is the list empty, and the count within
the padding string? -/
def cmp (p : List Unit × V) : Bool := (p.1.foldl (fun s _ => visit s) ([p.2], 0)).1.isEmpty && decide ((p.1.foldl (fun s _ => visit s) ([p.2], 0)).2 ≤ p.1.length)

/-- The comparison decides whether the word is at most as long as the padding string. -/
theorem cmp_eq (p : List Unit × V) : cmp p = decide ((code p.2).length ≤ p.1.length) := by
  obtain ⟨l, v⟩ := p
  have ht := fold_total l ([v], 0)
  have h0 : total [v] = (code v).length := by simp [total]
  simp only [h0, Nat.zero_add] at ht
  unfold cmp
  dsimp only
  by_cases h : (code v).length ≤ l.length
  · have hd := fold_done l ([v], 0) (by simpa [work] using (nodes_le v).trans h)
    rw [hd] at ht ⊢
    simp only [total, List.map_nil, List.sum_nil, Nat.add_zero] at ht
    rw [ht]
    simp [h]
  · rw [decide_eq_false h]
    rcases hw : (l.foldl (fun s _ => visit s) ([v], 0)).1 with _ | ⟨a, r⟩
    · rw [hw] at ht
      simp only [total, List.map_nil, List.sum_nil, Nat.add_zero] at ht
      rw [ht]
      simp [h]
    · simp

/-- The word of the list of trees has at most three times their symbols, and two more. -/
theorem sum_len_le (w : List V) : (w.map fun a => len a + 2).sum ≤ 3 * total w := by
  induction w with
  | nil => simp [total]
  | cons v r ih =>
    have h1 : 1 ≤ (code v).length := (nodes_pos v).trans (nodes_le v)
    have h2 : len v = (code v).length := rfl
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- The comparison is polynomial-time: the states of the fold are at most three times as long as the
input, and six more. -/
theorem cmp_poly : PolyT cmp := by
  have hv := visit_poly
  have hf : PolyT fun p : List Unit × V => p.1.foldl (fun s _ => visit s) ([p.2], 0) := by
    refine PolyT.foldl (l := fun p : List Unit × V => p.1) (a := fun p => (([p.2], 0) : List V × ℕ)) (g := fun _ s _ => visit s) (by fun_prop) (by fun_prop) (comp hv (by fun_prop))
      ⟨fun n => 3 * n + 6, ((PB.const 3).mul PB.id').add (PB.const 6), fun p k => ?_⟩
    have ht := fold_total (p.1.take k) ([p.2], 0)
    have h0 : total [p.2] = (code p.2).length := by simp [total]
    simp only [h0, Nat.zero_add] at ht
    generalize (p.1.take k).foldl (fun s _ => visit s) ([p.2], 0) = s at ht ⊢
    have h1 := sum_len_le s.1
    have h2 : Nat.size s.2 ≤ s.2 := Nat.size_le.2 Nat.lt_two_pow_self
    have h3 : len p = len p.1 + (code p.2).length + 2 := len_pair p.1 p.2
    have h4 : len s = len s.1 + len s.2 + 2 := len_pair s.1 s.2
    show len s ≤ 3 * len p + 6
    rw [h4, len_list, len_nat, h3]
    omega
  unfold cmp
  fun_prop

/-- Whether the word of a value has at most as many symbols as a padding string has units is decided
in polynomial time, for every type and every coding. -/
theorem wordCompared (α : Type) [Enc α] : PolyT fun p : List Unit × α => decide (len p.2 ≤ p.1.length) :=
  PolyT.of_wd (f := cmp) cmp_poly (fun p => (p.1, Enc.toV p.2)) (fun _ => rfl) fun p => by rw [cmp_eq]; rfl

end QueryMachines.Bridge.Proof
