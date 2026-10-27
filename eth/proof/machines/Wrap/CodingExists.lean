/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Wrap.Coding
import CircuitLowerBound.Tab.Sound
import ToTuring.Lib.Table
import ToTuring.Lib.List2
import ToTuring.Lib.Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith

/-! # Every machine with finite alphabets has a coding of its configurations

Labels, states and symbols are numbered. A configuration is written as the pair of the numbers of
its label and state, and the list of its stacks, in a fixed order, each stack as the list of the
numbers of its symbols (`repOf`).
One step sees only the label, the state and the top d symbols of every stack
(`CircuitLowerBound.Tab.stay_eq`). These make a configuration of their own, `top M c`, and there are
finitely many of them. So the step on values (`stepOf`) cuts the top d
numbers off every stack, looks the result up in a fixed finite table, which holds the value of the
next configuration, and puts the stacks found there in front of what was left of the old stacks.
`coding_exists` collects the fields of `Coding M`; everything before it stands in the namespace
`Wrap.Conf`. -/

public section

namespace Wrap.Conf

open Turing Groundwork CircuitLowerBound.Tab

/-! ### Numbers for the elements of a finite type -/

/-- The number of an element of a finite type, in some fixed order of the type. -/
noncomputable def num {α : Type} [Finite α] (x : α) : ℕ := (Finite.equivFin α x).val

/-- Different elements have different numbers. -/
theorem num_injective {α : Type} [Finite α] : Function.Injective (num : α → ℕ) :=
  fun _ _ h => (Finite.equivFin α).injective (Fin.val_injective h)

/-- The numbers are below the number of elements. -/
theorem num_lt {α : Type} [Finite α] (x : α) : num x < Nat.card α := (Finite.equivFin α x).isLt

/-! ### Sizes of lists -/

/-- If n ≤ b, the size of n is at most the number of bits of b, plus 1. -/
theorem size_nat_le {n b : ℕ} (h : n ≤ b) : size n ≤ Nat.size b + 1 := by
  rw [size_nat]; have := Nat.size_le_size h; omega

/-- The sizes of two lists add up to the size of the joined list and 1. -/
theorem size_append {α : Type} [HasSize α] (l l' : List α) : size (l ++ l') + 1 = size l + size l' := by
  simp only [size_list, List.map_append, List.sum_append]; omega

/-- Dropping entries does not make a list larger. -/
theorem size_drop_le {α : Type} [HasSize α] (l : List α) (d : ℕ) : size (l.drop d) ≤ size l := by
  have h := size_append (l.take d) (l.drop d)
  rw [List.take_append_drop] at h
  have : 1 ≤ size (l.take d) := by rw [size_list]; omega
  omega

/-- A list whose entries have size at most B has size at most (number of entries)·(B + 1) + 1. -/
theorem size_le_of_forall {α : Type} [HasSize α] {l : List α} {B : ℕ} (h : ∀ x ∈ l, size x ≤ B) :
    size l ≤ l.length * (B + 1) + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih fun n hn => h n (by simp [hn])
    rw [size_list] at h2 ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- If every entry grows by at most e, the list grows by at most (number of entries)·e. -/
theorem size_map_le {ι α : Type} [HasSize α] (ks : List ι) (f g : ι → α) (e : ℕ) (h : ∀ k ∈ ks, size (f k) ≤ size (g k) + e) :
    size (ks.map f) ≤ size (ks.map g) + ks.length * e := by
  induction ks with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih fun n hn => h n (by simp [hn])
    rw [size_list, size_list] at h2 ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- A fixed list of polynomial-time functions, applied to one argument, is polynomial-time. -/
theorem polyT_map_const {ι α β : Type} [Enc α] [Enc β] (l : List ι) (g : ι → α → β) (h : ∀ i, PolyT (g i)) :
    PolyT fun x => l.map fun i => g i x := by
  induction l with
  | nil => exact PolyT.const []
  | cons i l ih => exact PolyT.cons' (h i) ih

/-! ### Configurations as values -/

variable (M : TM2ComputableAux Bool Bool)

/-- The names of the stacks, each once, in a fixed order. -/
noncomputable def ks : List M.tm.K := Finset.univ.toList

/-- Every stack is in the list. -/
theorem mem_ks (k : M.tm.K) : k ∈ ks M := Finset.mem_toList.2 (Finset.mem_univ k)

/-- The configuration made of the label, the state and the top d symbols of every stack, where d is
the number of symbols that one step can see. -/
def top (c : M.tm.Cfg) : M.tm.Cfg := ⟨c.l, c.var, fun k => (c.stk k).take (dep M)⟩

/-- The step on the tops alone, as the table of the machine has it, is the step of the configuration
made of the tops. -/
theorem nxt_caseOf (c : M.tm.Cfg) : nxt M (caseOf M c) = stay M (top M c) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp only [nxt, caseOf, pref_ofFn]; rfl
  | some l => simp only [nxt, caseOf, pref_ofFn]; rfl

/-- One step: do the step on the tops alone, and put the new tops in front of what lies below the
top d symbols. -/
theorem stay_eq_top (c : M.tm.Cfg) : stay M c =
    ⟨(stay M (top M c)).l, (stay M (top M c)).var, fun k => (stay M (top M c)).stk k ++ (c.stk k).drop (dep M)⟩ := by
  rw [← nxt_caseOf]; exact stay_eq M c

/-- After a step on the tops alone a stack has at most 2d symbols. -/
theorem length_stay_top_le (c : M.tm.Cfg) (k : M.tm.K) : ((stay M (top M c)).stk k).length ≤ 2 * dep M := by
  rw [← nxt_caseOf]; exact length_nxt_le M _ k

variable [∀ i, Finite (M.tm.Γ i)]

/-- The number of a symbol of stack k. -/
noncomputable def sym (k : M.tm.K) (x : M.tm.Γ k) : ℕ := num (⟨k, x⟩ : Σ k, M.tm.Γ k)

/-- Different symbols of a stack have different numbers. -/
theorem sym_injective (k : M.tm.K) : Function.Injective (sym M k) :=
  fun _ _ h => sigma_mk_injective (num_injective h)

/-- The numbers of the symbols are below the number of all symbols of all stacks. -/
theorem sym_lt (k : M.tm.K) (x : M.tm.Γ k) : sym M k x < Nat.card (Σ k, M.tm.Γ k) := num_lt _

/-- A bound on the size of every number that stands for a label, a state or a symbol. -/
noncomputable def bnd : ℕ := Nat.size (Nat.card (Option M.tm.Λ) + Nat.card M.tm.σ + Nat.card (Σ k, M.tm.Γ k)) + 1

omit [∀ i, Finite (M.tm.Γ i)] in
/-- The number of a label, or of «halted», has size at most the bound. -/
theorem size_lab_le (l : Option M.tm.Λ) : size (num l) ≤ bnd M := size_nat_le (by have := num_lt l; omega)

omit [∀ i, Finite (M.tm.Γ i)] in
/-- The number of a state has size at most the bound. -/
theorem size_var_le (v : M.tm.σ) : size (num v) ≤ bnd M := size_nat_le (by have := num_lt v; omega)

/-- The number of a symbol has size at most the bound. -/
theorem size_sym_le (k : M.tm.K) (x : M.tm.Γ k) : size (sym M k x) ≤ bnd M :=
  size_nat_le (by have := num_lt (⟨k, x⟩ : Σ k, M.tm.Γ k); unfold sym; omega)

/-- The value that stands for a configuration: the numbers of the label and of the state, and the
stacks as lists of numbers. -/
noncomputable def repOf (c : M.tm.Cfg) : Rep :=
  ((num c.l, num c.var), (ks M).map fun k => (c.stk k).map (sym M k))

/-- Different configurations have different values. -/
theorem repOf_injective : Function.Injective (repOf M) := by
  rintro ⟨l, v, S⟩ ⟨l', v', S'⟩ h
  simp only [repOf, Prod.mk.injEq, List.map_inj_left] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain rfl := num_injective h1
  obtain rfl := num_injective h2
  obtain rfl : S = S' := funext fun k => (List.map_injective_iff.2 (sym_injective M k)) (h3 k (mem_ks M k))
  rfl

/-! ### The step -/

/-- The first two numbers and the top d entries of every list. -/
def key (d : ℕ) (r : Rep) : Rep := (r.1, r.2.map fun l => l.take d)

/-- Cutting the value of a configuration gives the value of the configuration made of the tops. -/
theorem key_repOf (c : M.tm.Cfg) : key (dep M) (repOf M c) = repOf M (top M c) := by
  simp [key, repOf, top, List.map_take]

/-- A fixed list that holds the values of all configurations made of tops. -/
noncomputable def keys : List Rep :=
  (Finite.exists_univ_list (Case M)).choose.map fun γ => repOf M ⟨γ.1, γ.2.1, fun k => pref (List.ofFn (γ.2.2 k))⟩

/-- The value of a configuration made of tops is in the list. -/
theorem repOf_top_mem (c : M.tm.Cfg) : repOf M (top M c) ∈ keys M := by
  refine List.mem_map.2 ⟨caseOf M c, (Finite.exists_univ_list (Case M)).choose_spec.2 _, ?_⟩
  simp only [caseOf, pref_ofFn]; rfl

/-- The entry of the table at the value of a configuration: the value of the next configuration. -/
noncomputable def entry (r : Rep) : Rep := repOf M (stay M (Function.invFun (repOf M) r))

/-- At the value of c the table holds the value of the configuration after c. -/
theorem entry_repOf (c : M.tm.Cfg) : entry M (repOf M c) = repOf M (stay M c) := by
  rw [entry, Function.leftInverse_invFun (repOf_injective M)]

/-- Reading the table, which has an entry for each value in `keys M`. -/
noncomputable def tab (r : Rep) : Rep := PolyT.lookup (entry M) ((0, 0), []) (keys M) r

/-- Reading the table is polynomial-time, because the table is fixed and finite. -/
theorem tab_polyT : PolyT (tab M) := PolyT.lookup_polyT _ _ _

/-- One step on values: cut off the tops, look them up, put the new tops in front of the rest. -/
noncomputable def stepOf (r : Rep) : Rep :=
  ((tab M (key (dep M) r)).1, ((tab M (key (dep M) r)).2.zip (r.2.map fun l => l.drop (dep M))).map fun p => p.1 ++ p.2)

/-- The step on values is polynomial-time. -/
theorem stepOf_polyT : PolyT (stepOf M) := by
  have h := tab_polyT M
  unfold stepOf key
  fun_prop

/-- The step on values is the step of the machine. -/
theorem stepOf_repOf (c : M.tm.Cfg) : stepOf M (repOf M c) = repOf M (stay M c) := by
  have h : tab M (key (dep M) (repOf M c)) = repOf M (stay M (top M c)) := by
    rw [key_repOf, tab, PolyT.lookup_eq _ _ (repOf_top_mem M c), entry_repOf]
  rw [stepOf, h, stay_eq_top M c]
  simp [repOf, List.zip_map', List.map_drop]

/-! ### The start -/

/-- The number of the symbol of the input stack that stands for a bit. -/
noncomputable def inSym (b : Bool) : ℕ := sym M M.tm.k₀ (M.inputAlphabet.invFun b)

/-- The start configuration on the bit string x, as a value: the input stack holds the numbers of
the symbols that stand for the bits of x, the other stacks are empty. -/
noncomputable def initOf (x : List Bool) : Rep :=
  ((num (some M.tm.main), num M.tm.initialState),
    (ks M).map fun k => if k = M.tm.k₀ then x.map (inSym M) else [])

/-- The start on values is polynomial-time. -/
theorem initOf_polyT : PolyT (initOf M) := by
  have h1 : PolyT (inSym M) := PolyT.table _
  have h2 : PolyT fun x : List Bool => (ks M).map fun k =>
      if k = M.tm.k₀ then x.map (inSym M) else [] := by
    refine polyT_map_const (ks M) (fun k (x : List Bool) => if k = M.tm.k₀ then x.map (inSym M) else []) fun k => ?_
    by_cases e : k = M.tm.k₀
    · simp only [e, if_true]
      exact PolyT.map (f := fun _ b => inSym M b) (PolyT.comp h1 (PolyT.snd PolyT.id')) PolyT.id'
    · simp only [e, if_false]; fun_prop
  unfold initOf
  fun_prop

/-- The start on values is the value of the start configuration of the machine. -/
theorem initOf_eq (x : List Bool) : initOf M x = repOf M (initList M.tm (x.map M.inputAlphabet.invFun)) := by
  have h : ∀ k ∈ ks M, (if k = M.tm.k₀ then x.map (inSym M) else []) =
      ((initList M.tm (x.map M.inputAlphabet.invFun)).stk k).map (sym M k) := by
    intro k _
    by_cases e : k = M.tm.k₀
    · subst e; rw [initList_stk_self]; simp [Function.comp_def, inSym]
    · rw [initList_stk_of_ne M _ e]; simp [e]
  rw [initOf, repOf, List.map_congr_left h]
  rfl

/-! ### The output -/

/-- The place of the output stack in the list of the stacks. -/
noncomputable def outIdx : ℕ := (List.mem_iff_getElem?.1 (mem_ks M M.tm.k₁)).choose

omit [∀ i, Finite (M.tm.Γ i)] in
/-- At that place stands the output stack. -/
theorem ks_outIdx : (ks M)[outIdx M]? = some M.tm.k₁ := (List.mem_iff_getElem?.1 (mem_ks M M.tm.k₁)).choose_spec

/-- The bit for which a symbol of the output stack stands, from the number of the symbol: a fixed
finite table. -/
noncomputable def bitOf (n : ℕ) : Bool :=
  haveI : Nonempty (M.tm.Γ M.tm.k₁) := ⟨M.outputAlphabet.symm false⟩
  PolyT.lookup (fun n => M.outputAlphabet (Function.invFun (sym M M.tm.k₁) n)) false (List.range (Nat.card (Σ k, M.tm.Γ k))) n

/-- Reading that table is polynomial-time. -/
theorem bitOf_polyT : PolyT (bitOf M) := PolyT.lookup_polyT _ _ _

/-- The table gives back the bit of a symbol. -/
theorem bitOf_sym (y : M.tm.Γ M.tm.k₁) : bitOf M (sym M M.tm.k₁ y) = M.outputAlphabet y := by
  have : Nonempty (M.tm.Γ M.tm.k₁) := ⟨y⟩
  rw [bitOf, PolyT.lookup_eq _ _ (List.mem_range.2 (sym_lt M _ y))]
  exact congrArg _ (Function.leftInverse_invFun (sym_injective M _) y)

/-- The output: if the first number is that of «halted», the bits of the output stack; otherwise
nothing. -/
noncomputable def outOf (r : Rep) : Option (List Bool) :=
  if r.1.1 = num (none : Option M.tm.Λ) then some ((r.2.getD (outIdx M) []).map fun n => bitOf M n) else none

/-- Reading the output is polynomial-time. -/
theorem outOf_polyT : PolyT (outOf M) := by
  have h := bitOf_polyT M
  unfold outOf
  fun_prop

/-- On a halted configuration the output is the content of the output stack, as bits. -/
theorem outOf_halted (c : M.tm.Cfg) (h : c.l = none) : outOf M (repOf M c) = some ((c.stk M.tm.k₁).map M.outputAlphabet) := by
  simp [outOf, repOf, h, List.getD_eq_getElem?_getD, ks_outIdx, Function.comp_def, bitOf_sym]

/-- On a configuration that is not halted there is no output. -/
theorem outOf_running (c : M.tm.Cfg) (h : c.l ≠ none) : outOf M (repOf M c) = none :=
  if_neg fun e => h (num_injective e)

/-! ### Sizes -/

/-- A stack of n symbols, as a list of numbers, has size at most n·(bound + 1) + 1. -/
theorem size_stack_le (k : M.tm.K) (S : List (M.tm.Γ k)) : size (S.map (sym M k)) ≤ S.length * (bnd M + 1) + 1 := by
  have := size_le_of_forall (l := S.map (sym M k)) (B := bnd M) fun n hn => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hn
    exact size_sym_le M k y
  rwa [List.length_map] at this

/-- If every stack of c has at most n symbols, the value of c has size at most 2·bnd + (number of
stacks)·(n·(bnd + 1) + 2) + 1. -/
theorem size_repOf_le (c : M.tm.Cfg) (n : ℕ) (h : ∀ k, (c.stk k).length ≤ n) :
    size (repOf M c) ≤ 2 * bnd M + ((ks M).length * (n * (bnd M + 1) + 1 + 1) + 1) := by
  have h1 := size_lab_le M c.l
  have h2 := size_var_le M c.var
  have h3 := size_le_of_forall (l := (ks M).map fun k => (c.stk k).map (sym M k)) (B := n * (bnd M + 1) + 1) fun s hs => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hs
    exact (size_stack_le M k _).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (h k)) 1)
  rw [List.length_map] at h3
  simp only [repOf, size_prod]
  omega

/-- A step adds at most a constant to the size of the value. -/
theorem size_repOf_stay_le (c : M.tm.Cfg) :
    size (repOf M (stay M c)) ≤ size (repOf M c) + (2 * bnd M + (ks M).length * (2 * dep M * (bnd M + 1))) := by
  have h1 := size_lab_le M (stay M (top M c)).l
  have h2 := size_var_le M (stay M (top M c)).var
  have h3 := size_map_le (ks M) (fun k => ((stay M (top M c)).stk k ++ (c.stk k).drop (dep M)).map (sym M k))
    (fun k => (c.stk k).map (sym M k)) (2 * dep M * (bnd M + 1)) fun k _ => by
      have e1 := size_append (((stay M (top M c)).stk k).map (sym M k)) (((c.stk k).drop (dep M)).map (sym M k))
      have e2 := size_stack_le M k ((stay M (top M c)).stk k)
      have e3 := Nat.mul_le_mul_right (bnd M + 1) (length_stay_top_le M c k)
      have e4 := size_drop_le ((c.stk k).map (sym M k)) (dep M)
      rw [← List.map_drop] at e4
      rw [List.map_append]
      omega
  rw [stay_eq_top M c]
  simp only [repOf, size_prod]
  omega

/-- The value of the start configuration is at most linear in the input. -/
theorem size_initOf_le (x : List Bool) :
    size (initOf M x) ≤ (2 * bnd M + (ks M).length * (bnd M + 3) + 1) * (x.length + 1) := by
  have h := size_repOf_le M (initList M.tm (x.map M.inputAlphabet.invFun)) x.length fun k => by
    by_cases e : k = M.tm.k₀
    · subst e; rw [initList_stk_self]; simp
    · rw [initList_stk_of_ne M _ e]; simp
  rw [← initOf_eq] at h
  refine h.trans ?_
  have e1 : x.length * (bnd M + 1) + 1 + 1 ≤ (bnd M + 3) * (x.length + 1) := by nlinarith
  have e2 := Nat.mul_le_mul_left (ks M).length e1
  nlinarith [Nat.zero_le (bnd M * x.length)]

end Wrap.Conf

namespace Wrap

open Turing Groundwork CircuitLowerBound.Tab Conf

/-- Every machine with finite alphabets has a coding of its configurations as values of the type
`Rep`: polynomial-time functions on values for the start, for one step and for reading the output,
and bounds on the sizes. -/
theorem coding_exists (M : TM2ComputableAux Bool Bool) (hfin : ∀ i, Finite (M.tm.Γ i)) : Nonempty (Coding M) :=
  ⟨{ rep := repOf M
     step := stepOf M
     init := initOf M
     out := outOf M
     a := (2 * bnd M + (ks M).length * (2 * dep M * (bnd M + 1))) + (2 * bnd M + (ks M).length * (bnd M + 3) + 1)
     step_poly := stepOf_polyT M
     init_poly := initOf_polyT M
     out_poly := outOf_polyT M
     step_rep := stepOf_repOf M
     init_rep := initOf_eq M
     out_halted := outOf_halted M
     out_running := outOf_running M
     size_init := fun x => (size_initOf_le M x).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
     size_step := fun c => (size_repOf_stay_le M c).trans (Nat.add_le_add_left (Nat.le_add_right _ _) _) }⟩

end Wrap
