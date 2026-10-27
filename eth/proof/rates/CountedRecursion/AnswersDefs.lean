/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs
public import PiecesCountedStatement
public import LevelsStatement

/-! # Answers of two kinds, and the numbers of a level

Definitions and statements only; nothing is proved here.

**Why.** The recursion of Theorem A (b) is to be ONE machine (`QueryMachines.Tower.tower`), and a
tower has one type of answers. Its machines ask three things: the tables of a clique (an integer),
the pieces (an integer, or the list 𝓘), and a call of the solver (an integer). So the type of
answers is that of the pieces, `PiecesCounted.Answer` = ℤ ⊕ List ℤ, and an integer v is the answer
`Sum.inl v`.
* `asInt`, `asList`: how an answer is read. An answer of the wrong kind is read as 0, or as the
  empty list; with the oracles of the statements this does not happen.
* `askInt h`, `askList h`: ask the query h a and read the answer.
* `readAs r M`: a machine M that was built for answers of type A, run where the answers have type A'
  and are read by r. (The library of machines with query access has `mapAsk` for the queries; this
  is its counterpart for the answers. It lets `Printed.bruteMachine` be used as it is.)
* `numbersM x₀`: «K_ℓ» and «g_ℓ = 2^{3ℓ+x₀}K_ℓ» in unary from ℓ in unary. K_ℓ is doubly exponential
  in ℓ and a step must take time polynomial in the size of the state, so the numbers cannot be
  written in one step. The loop has ℓ rounds and keeps the pair (2^{3j+x₀}, K_j), both in unary; a
  round replaces (p, K) by (8p, (pK)²), which is polynomial-time in the pair. -/

@[expose] public section

namespace ExplicitCost

open Groundwork QueryMachines Printed

variable {Q A A' α β : Type}

/-- A query to the pieces: λ in unary and the question. -/
abbrev PieceQuery : Type := List Unit × PiecesCounted.Question

/-- The one type of answers: an integer, or (for 𝓘) a list of integers. -/
abbrev Ans : Type := PiecesCounted.Answer

/-- An answer read as an integer. -/
def asInt : Ans → ℤ
  | .inl v => v
  | .inr _ => 0

/-- An answer read as a list of integers. -/
def asList : Ans → List ℤ
  | .inl _ => []
  | .inr l => l

/-- Ask the query h a; the answer is read as an integer. -/
def askInt [HasSize α] (h : α → Q) : QueryMachine Q Ans α ℤ := QueryMachine.mapOut (QueryMachine.query h) asInt

/-- Ask the query h a; the answer is read as a list of integers. -/
def askList [HasSize α] (h : α → Q) : QueryMachine Q Ans α (List ℤ) := QueryMachine.mapOut (QueryMachine.query h) asList

/-- The same machine where the answers have another type and are read by r. -/
def readAs (r : A' → A) (M : QueryMachine Q A α β) : QueryMachine Q A' α β :=
  { M.toStepped with ask := M.ask, resume := fun s v => M.resume s (r v) }

/-- The runs are the same, if the new oracle, read by r, is the old one. -/
def ReadAsRuns : Prop := ∀ (Q A A' α β : Type) (r : A' → A) (M : QueryMachine Q A α β) (O : Q → Option A) (O' : Q → Option A') (a : α) (own S : ℕ) (L : List Q) (b : β),
  (∀ x, (O' x).map r = O x) → M.Runs O a own L S b → (readAs r M).Runs O' a own L S b

/-- Polynomial-time steps are kept, if r is polynomial-time. -/
def ReadAsPoly : Prop := ∀ (Q A A' α β : Type) [Enc Q] [Enc A] [Enc A'] [Enc α] [Enc β] (r : A' → A) (M : QueryMachine Q A α β), PolyT r → M.PolyTimeSteps → (readAs r M).PolyTimeSteps

/-- If every price is raised at most k times, so is the cost. (For one price for all queries this is
`QueryMachines.StSlowDown`.) -/
def PricesScale : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (w w' : Q → ℕ) (a : α) (T S k : ℕ) (b : β), 1 ≤ k → (∀ x, w' x ≤ k * w x) →
  M.Within O w a T S b → M.Within O w' a (k * T) S b

/-! ### The numbers of a level -/

/-- One round: (2^{3j+x₀}, K_j) becomes (2^{3(j+1)+x₀}, K_{j+1}) = (8·2^{3j+x₀}, (2^{3j+x₀}K_j)²),
all in unary. -/
def numbersStep (acc : List Unit × List Unit) : List Unit × List Unit := (unary (8 * acc.1.length), unary ((acc.1.length * acc.2.length) ^ 2))

/-- From ℓ in unary: (2^{3ℓ+x₀}, K_ℓ) in unary, by ℓ rounds. -/
def numbersM (x₀ : ℕ) : Stepped (List Unit) (List Unit × List Unit) :=
  Stepped.foldRange (fun l : List Unit => l.length) (Stepped.const ()) (fun acc _ (_ : Unit) => numbersStep acc) fun _ => (unary (2 ^ x₀), unary (2 ^ x₀))

/-- The loop returns (2^{3ℓ+x₀}, K_ℓ) after 2ℓ steps, on states of size linear in g_ℓ. One constant
for all x₀ and ℓ. -/
def NumbersRun : Prop := ∃ C : ℕ, ∀ x₀ l : ℕ, (numbersM x₀).Runs (unary l) (2 * l) (C * Levels.Gen.g x₀ l) (unary (2 ^ (3 * l + x₀)), unary (Levels.Gen.K x₀ l))

/-- The loop has polynomial-time steps. -/
def NumbersPoly : Prop := ∀ x₀ : ℕ, Nonempty (IsPolyT (numbersM x₀))

end ExplicitCost
