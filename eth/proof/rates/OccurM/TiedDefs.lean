/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClausesOccurStatement
public import GeneralPieces.Tied.BoundDefs
public import VariableBound.Paper.Rename.Defs
public import VariableBound.Paper.Rename.Compact
public import Wrap.Defs

/-! # The bound in m for formulas over arbitrary names: the forms that show the route

`ClausesOccur.Counts α` says «there is a machine»; by its wording it says nothing about the route of
a proof. The proof of Theorem A (c) in the paper uses a preparation that lists the occurrences and
the tests (here it also numbers the variables that occur),
the network of the formula, case (i) of Lemma 8 (the lemma on groupings with explicit cost) and the
algorithm of part (b). The statements of this file name these things. Nothing is proved here.

* `Prepares pre`: what the preparation does. On the compact code of (k, φ) the function `pre`
  returns the code `SatM.enc k ψ` of a k-CNF ψ over exactly n = `numOcc φ` variables, all of which
  occur, with as many clauses as φ and with
  as many satisfying assignments as φ has as assignments of the variables that occur.
* `prepA S pick`, `prepE S pick`: the named top level in m (`ClauseBound.Alg.AM`, `eM`) with the
  named preparation `VariableBound.Rename.rencC` in front.
* `TopOccur S pick α`: the bound in m for these two named functions; `TopOccurOfTopStmt`: it follows
  from `GeneralPieces.Tied.TopM`, the same for formulas in which every variable occurs.
* `CountsFromPiecesTied`, `BoundInClausesTied`: Theorem A (c), first sentence, and the bound in m of
  the Main Theorem, for the named programs on the recursion of part (b).
* `EveryWrapperCounts`: for EVERY machine M that counts within the bound on formulas in which every
  variable occurs, EVERY machine N that runs a preparation and then M counts within the printed
  bound on every k-CNF with k ≥ 1 and m ≥ 2. -/

@[expose] public section

namespace OccurM

open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)

/-! ### The preparation -/

/-- `pre` numbers the variables that occur: for every k ≥ 1 and every k-CNF φ over x₀ … x_(N−1),
`pre` maps the compact code of (k, φ) to the code of (k, ψ) for a k-CNF ψ over n = `numOcc φ`
variables, all of which occur in ψ, with
as many clauses as φ, whose number of satisfying assignments is that of φ as assignments of the
variables that occur. -/
def Prepares (pre : List Bool → List Bool) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
    SatK.numSat ψ = numSatOcc φ ∧ pre (encC k φ) = SatM.enc k ψ

/-- The same for the code `SatM.enc k φ`, which has N in unary. -/
def PreparesUnary (pre : List Bool → List Bool) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
    SatK.numSat ψ = numSatOcc φ ∧ pre (SatM.enc k φ) = SatM.enc k ψ

/-- The two named preparations are such, and they are polynomial-time. -/
def PreparationStmt : Prop := Prepares VariableBound.Rename.rencC ∧ PolyT VariableBound.Rename.rencC ∧ PreparesUnary VariableBound.Rename.renc ∧ PolyT VariableBound.Rename.renc

/-! ### The named programs -/

/-- The top level in m after the preparation, a function of (input, pad). -/
def prepA {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (p : List Bool × U) : List Bool := AM S pick (VariableBound.Rename.rencC p.1, p.2)

/-- Its exponent, a function of the input. -/
def prepE {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (x : List Bool) : ℕ := eM S pick (VariableBound.Rename.rencC x)

/-- The bound in m for the named top level after the named preparation, for an algorithm S for
cliques and a way to pick its level. -/
structure TopOccur {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (α : ℝ) : Prop where
  /-- both functions are polynomial-time -/
  poly_A : PolyT (prepA S pick)
  poly_e : PolyT (prepE S pick)
  /-- the function returns the number of satisfying assignments, as assignments of the n variables
  that occur, in n + 1 bits, if the pad has 2^prepE units -/
  correct : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ prepE S pick (encC k φ) ≤ pad.length →
    prepA S pick (encC k φ, pad) = SatK.binary (numOcc φ) (numSatOcc φ)
  /-- the exponent is O(k·m/(log m)^α), the O not depending on k -/
  rate : ∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (prepE S pick (encC k φ) : ℝ) ≤ G * expClauses α k φ.length
  /-- one machine computes, on every input x, the named function at (x, 2^{prepE x} units) within
  q·(|x| + 2^{prepE x} + 1)^q steps, and it counts within the printed bound -/
  machine : ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some ((prepA S pick (x, pad (prepE S pick x))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ prepE S pick x + 1) ^ q))) ∧
    CountsFor α M C

/-- As `prepA`, for the code with N in unary. -/
def prepAUnary {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (p : List Bool × U) : List Bool := AM S pick (VariableBound.Rename.renc p.1, p.2)

/-- As `prepE`, for the code with N in unary. -/
def prepEUnary {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (x : List Bool) : ℕ := eM S pick (VariableBound.Rename.renc x)

/-- As `TopOccur`, for the code `SatM.enc k φ`, which has N in unary, and the preparation
`VariableBound.Rename.renc`. -/
structure TopOccurUnary {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (α : ℝ) : Prop where
  poly_A : PolyT (prepAUnary S pick)
  poly_e : PolyT (prepEUnary S pick)
  correct : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ prepEUnary S pick (SatM.enc k φ) ≤ pad.length →
    prepAUnary S pick (SatM.enc k φ, pad) = SatK.binary (numOcc φ) (numSatOcc φ)
  rate : ∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (prepEUnary S pick (SatM.enc k φ) : ℝ) ≤ G * expClauses α k φ.length
  machine : ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some ((prepAUnary S pick (x, pad (prepEUnary S pick x))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ prepEUnary S pick x + 1) ^ q))) ∧
    CountsUnaryFor α M C

/-- The step: from the bound in m for the named top level on formulas in which every variable occurs
to the bound for the same top level after the preparation, on every k-CNF with k ≥ 1 and m ≥ 2
(correctness: m ≥ 1). For every algorithm for cliques, every way to pick its
level and every exponent 0 ≤ α ≤ 1. -/
def TopOccurOfTopStmt : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (α : ℝ), 0 ≤ α → α ≤ 1 →
  GeneralPieces.Tied.TopM S pick (SatM.rPow α) → TopOccur S pick α ∧ TopOccurUnary S pick α

/-- Theorem A (c), first sentence, for the named programs: for all pieces with parameters (ρ, c) and
every x₀ ≥ 18 with 2^x₀ ≥ c + 5, the preparation, then the top level in m on the recursion of part (b)
on these pieces. -/
def CountsFromPiecesTied : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val →
  18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → TopOccur (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) x₀) (AppRunningTime.alpha' ρ) ∧
    TopOccurUnary (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) x₀) (AppRunningTime.alpha' ρ)

/-- The bound in m of the Main Theorem for the named programs: for some programs (P, val) for the
pieces of Appendix B, with a constant c, and the least x₀ of Theorem A. -/
def BoundInClausesTied : Prop := ∃ (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), GeneralPieces.Tied.IsPiecesB c P A val ∧
  TopOccur (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) (GeneralPieces.x₀Of c)) (1 / 2) ∧
  TopOccurUnary (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) (GeneralPieces.x₀Of c)) (1 / 2)

/-- From the tied forms, which name the programs, to the forms that only say «there is a machine». -/
def UntieStmt : Prop := (CountsFromPiecesTied → CountsFromPieces ∧ CountsUnaryFromPieces) ∧ (BoundInClausesTied → BoundInClauses)

/-! ### For every machine -/

/-- Let 0 ≤ α ≤ 1, let `pre` number the variables that occur, and let M, with the constant C, count
within C·2^{C·km/(log₂(m+2))^α} steps on the formulas in which every variable occurs (the body of
`SatM.CountInRate`). Then EVERY machine
N that wraps M, with `pre` before it and nothing after it, for whatever q, counts on every k-CNF
with k ≥ 1 and m ≥ 2 as in `CountsFor α`, with some constant. All that is known of N is
`Wrap.Wraps M pre id N q`. That such `pre`, N and q exist is said by
`PreparationStmt` and `Wrap.EveryMachineCanBeWrapped`. -/
def EveryWrapperCounts : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ pre : List Bool → List Bool, Prepares pre → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), SatM.CountsTM M (SatM.bound (SatM.rPow α) C) →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre id N q → ∃ C' : ℕ, CountsFor α N C'

/-- The same for the code with N in unary. -/
def EveryWrapperCountsUnary : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ pre : List Bool → List Bool, PreparesUnary pre → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), SatM.CountsTM M (SatM.bound (SatM.rPow α) C) →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre id N q → ∃ C' : ℕ, CountsUnaryFor α N C'

end OccurM
