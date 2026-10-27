/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.FinRange

/-! # Section 7, proof of Corollary 6: the width reduction that keeps the number of satisfying assignments (definitions and statements only)

The paper: «each of these is turned into a 3-CNF with O(n) clauses and O(n) variables and the same
number of satisfying assignments, by the standard width reduction, which introduces a constant
number of [fresh] variables for each clause.
The number is preserved if each [fresh] variable is forced, by three clauses of at most 3 literals,
to equal the disjunction of the two literals that it replaces in a long clause; Dell et al. do not
spell this out.»

One step: a clause l₁ ∨ l₂ ∨ l₃ ∨ l₄ ∨ … (more than 3 literals) becomes y ∨ l₃ ∨ l₄ ∨ …, with a
variable y that occurs nowhere else, and the three clauses ¬y ∨ l₁ ∨ l₂, y ∨ ¬l₁, y ∨ ¬l₂ (`forced`)
are added. The step is repeated on the
shorter clause until 3 literals are left (`splitClause`), so a clause with s > 3 literals takes s −
3 fresh variables and becomes 1 + 3(s − 3) clauses. `splitAll` does this for every clause, each with
fresh variables of its own.
`widthReduce φ` is the result for a formula φ on x₀ … xₙ₋₁ in the sense of `ThreeSatStatement.lean`:
a formula on x₀ … x_{n+N−1}, where N = `numFresh φ` and the fresh variables are xₙ … x_{n+N−1}.

The statements, proved in `Width.lean`: `StForced` (the three clauses say y = l₁ ∨ l₂), `StRestrict`
and `StExtend` (a satisfying assignment of the image, read on x₀ … xₙ₋₁, satisfies φ; a satisfying
assignment of φ extends to one of the image in exactly one way),
and `StWidth` (the image is an instance of 3-SAT with the same number of satisfying assignments; at
most (k − 3)·m fresh variables and at most m + 3(k − 3)·m clauses for a k-CNF with m clauses).

Different from the paper: a clause is a list here, so a literal may stand twice in it. If l₁ = l₂,
the step writes the clause y ∨ ¬l₁ twice, and an instance (`SatK.IsKCNF`) may not have a clause
written twice. So `widthReduce` ends by striking out repetitions
of clauses (`List.dedup`). This changes neither the set of clauses nor the satisfying assignments.
The first four definitions are for any type V of variables, because they are used for V = Fin (n +
N) here and for V = ℕ in programs. This file imports only `CountKSatStatement.lean` (and Mathlib). -/

@[expose] public section

namespace Eight.Width

open Sat3 (Lit CNF)

variable {V : Type}

/-- The opposite literal. A literal is a variable with the value of it that makes the literal true,
as in `Sat3.Lit`. -/
def neg (l : V × Bool) : V × Bool := (l.1, !l.2)

/-- The three clauses ¬y ∨ l₁ ∨ l₂, y ∨ ¬l₁, y ∨ ¬l₂. -/
def forced (y : V) (l₁ l₂ : V × Bool) : List (List (V × Bool)) :=
  [[(y, false), l₁, l₂], [(y, true), neg l₁], [(y, true), neg l₂]]

/-- One clause, with a list of fresh variables: while the clause has more than 3 literals and a
fresh variable y is left, put y in the place of the first two literals and add the three clauses for
y. -/
def splitClause : List V → List (V × Bool) → List (List (V × Bool))
  | y :: ys, l₁ :: l₂ :: l₃ :: l₄ :: r => forced y l₁ l₂ ++ splitClause ys ((y, true) :: l₃ :: l₄ :: r)
  | _, C => [C]

/-- All clauses: a clause with s literals takes the next s − 3 fresh variables of the list (none if
s ≤ 3). -/
def splitAll : List V → List (List (V × Bool)) → List (List (V × Bool))
  | _, [] => []
  | ys, C :: φ => splitClause (ys.take (C.length - 3)) C ++ splitAll (ys.drop (C.length - 3)) φ

/-- The number of fresh variables: s − 3 for each clause with s > 3 literals. -/
def numFresh (φ : List (List (V × Bool))) : ℕ := (φ.map fun C => C.length - 3).sum

/-- The assignment a makes a literal of every clause true (the condition in `Sat3.Satisfiable` and
in `SatK.numSat`). -/
def Holds (a : V → Bool) (φ : List (List (V × Bool))) : Prop := ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2

/-- The width reduction of a formula on x₀ … xₙ₋₁. The variables of φ keep their numbers, the fresh
ones are xₙ … x_{n+N−1}, N = `numFresh φ`; a clause that comes out several times is kept once. -/
def widthReduce {n : ℕ} (φ : CNF n) : CNF (n + numFresh φ) :=
  (splitAll ((List.finRange (numFresh φ)).map (Fin.natAdd n))
    (φ.map fun C => C.map fun l => (Fin.castAdd (numFresh φ) l.1, l.2))).dedup

/-! ### The statements -/

/-- «each [fresh] variable is forced, by three clauses of at most 3 literals, to equal the
disjunction of the two literals that it replaces»: an assignment satisfies the three clauses exactly
if it makes y true exactly when it makes l₁ or l₂ true;
and the three clauses have at most 3 literals. -/
def StForced : Prop := ∀ (V : Type) (a : V → Bool) (y : V) (l₁ l₂ : V × Bool),
  (Holds a (forced y l₁ l₂) ↔ (a y = true ↔ a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2)) ∧ ∀ C ∈ forced y l₁ l₂, C.length ≤ 3

/-- A satisfying assignment of the image, read on the variables x₀ … xₙ₋₁ of φ, satisfies φ. -/
def StRestrict : Prop := ∀ (n : ℕ) (φ : CNF n) (b : Fin (n + numFresh φ) → Bool),
  Holds b (widthReduce φ) → Holds (fun i => b (Fin.castAdd (numFresh φ) i)) φ

/-- A satisfying assignment of φ is the restriction of exactly one satisfying assignment of the
image. -/
def StExtend : Prop := ∀ (n : ℕ) (φ : CNF n) (a : Fin n → Bool), Holds a φ →
  ∃! b : Fin (n + numFresh φ) → Bool, Holds b (widthReduce φ) ∧ ∀ i, b (Fin.castAdd (numFresh φ) i) = a i

/-- The width reduction, as the proof of Corollary 6 uses it. For every formula φ on n variables the
image is an instance of 3-SAT (at most 3 literals per clause, no clause written twice) on n +
`numFresh φ` variables with the same number of
satisfying assignments. If φ has m clauses with at most k literals each, there are at most (k − 3)·m
fresh variables and at most m + 3(k − 3)·m clauses. (In ℕ, k − 3 is 0 for k ≤ 3.) -/
def StWidth : Prop := ∀ (n : ℕ) (φ : CNF n),
  SatK.IsKCNF 3 (widthReduce φ) ∧ SatK.numSat (widthReduce φ) = SatK.numSat φ ∧
    ∀ k : ℕ, (∀ C ∈ φ, C.length ≤ k) →
      numFresh φ ≤ (k - 3) * φ.length ∧ (widthReduce φ).length ≤ φ.length + 3 * ((k - 3) * φ.length)

end Eight.Width
