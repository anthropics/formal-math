/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.DefsProg
public import StepMachines.Prog.Walk
public import StepMachines.Prog.Comb
public import StepMachines.Prog.Sat
public import StepMachines.Prog.Chunks
public import Mathlib.Data.Fintype.Pi

/-! # The counting program: definitions

The sparsification tree of the branching rule `pickK` writes a k-CNF as an OR of sparse formulas,
which may share satisfying assignments. Dell, Husfeldt, Marx, Taslaman and Wahlén
(arXiv 1206.1775, Appendix A) make the branches exclude each other. In the notation of Appendix C,
where a node branches on a set H of literals (the heart) and the clauses Q = {E∖H : E ∈ F} (the
petals), the child that gets Q also gets «every literal of H is false».
Here a node of the tree is a pair: the formula that the branching rule looks at, and a side list of
clauses that the rule never looks at. The clauses «every literal of H is false» go on
the side list, so the first components of the nodes form exactly the tree of `pickK` alone, as in
Appendix C. The side list starts with the clauses xᵢ ∨ ¬xᵢ, i < n. They are always true,
and they make every variable occur, so that the value of the network of a leaf is its number of
satisfying assignments on all n variables.
This file has definitions only. -/

@[expose] public section

namespace CountKSat

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Groundwork.Stepped

/-! ### The tree -/

/-- A node: the formula that the rule looks at, and the side list. -/
abbrev CNode : Type := PFml × PFml

/-- «Every literal of H is false», as clauses of one literal. -/
def negU (H : PCl) : PFml := H.map fun l => [(l.1, !l.2)]

/-- The light child (the first component; the call on ψ ∪ {H} in Appendix C) gets the heart H as a
clause. The heavy child (the second component; the call on ψ ∪ Q) gets the petals Q = {E∖H : E ∈ F},
and on its side list «every literal of H is false». -/
def stepC (θ : ℕ → ℕ) (k : ℕ) (x : CNode) : Option (CNode × CNode) :=
  (pickK θ k x.1).map fun HP => ((addP [HP.1] x.1, x.2), (addP HP.2 x.1, negU HP.1 ++ x.2))

/-- The clauses xᵢ ∨ ¬xᵢ for i < n. -/
def taut (n : ℕ) : PFml := (List.range n).map fun i => [(i, true), (i, false)]

/-- The root, from the number of variables in unary and the formula. -/
def rootC (p : List Unit × Fml) : CNode := (rootP p.2, taut p.1.length)

/-- The formula of a node: the side list and the formula that the rule looks at. -/
def leafF (x : CNode) : Fml := x.2 ++ x.1

/-! ### Counting on n variables -/

/-- An assignment to x₀ … xₙ₋₁, continued by false. -/
def ext {n : ℕ} (a : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then a ⟨i, h⟩ else false

/-- The number of assignments to x₀ … xₙ₋₁ that make a literal of every clause of x true. -/
def cntN (n : ℕ) (x : Fml) : ℕ := (Finset.univ.filter fun a : Fin n → Bool => ∀ C ∈ x, ∃ l ∈ C, ext a l.1 = l.2).card

/-! ### The machine cut into steps -/

variable {α ν : Type}

/-- The sum, over the leaves below root a, of the numbers that T returns. -/
def walkSum [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν ℕ) : Stepped α ℕ :=
  foldWhile (fun a => some [root a]) (walkNext step) (guard (walkSel step) T 0) (fun c _ b => c + b) fun _ => 0

/-- The result as a word: n + 1 bits, lowest first. -/
def outW (q : (List Unit × Fml) × ℕ) : List Bool := toWord (q.1.1.length + 1) q.2

/-- The counting machine: read the input by `decU` as (n in unary, formula); the count is 0 if there
is an empty clause; otherwise walk the tree of `step`
and add up the counts of the leaves; write the sum as a word. M returns the count of one sparse
formula. -/
def countMK (decU : List Bool → List Unit × Fml) (step : CNode → Option (CNode × CNode)) (M : Stepped Fml ℤ) :
    Stepped (List Bool) (List Bool) :=
  Stepped.mapIn decU (Stepped.bind
    (Stepped.ite (fun p => hasNil p.2) (Stepped.const 0) (walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat))))
    (Stepped.ofFun outW))

end CountKSat
