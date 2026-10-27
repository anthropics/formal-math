/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecPseudocode_Algorithm
public import KSatStatement
public import PaperSentencesStatement
public import GraphProblemsStatement
public import CircuitLowerBoundStatement
public import CircuitLowerBoundInfinitelyOftenStatement
public import Eight.Level.Defs
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import StepMachines.Prog.Sat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import StepMachines.Math.SparsifyCount
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import WidthK.Top.Sat
public import WidthK.Decode
public import SparsifyWidthK.DefsProg
public import CountKSat.Interfaces
public import GraphProblems.Engine
public import GraphProblems.Sized
public import GraphProblems.ColorTM
public import CircuitLowerBound.Alg.Machine
public import PaddedDescent.BrutePad

/-! # Section 7: the input of a verifier and the specification of a procedure for #k-SAT (definitions only)

It defines `stripW`, which takes the witness off the input of a verifier; `Serves`, what a machine
must do to serve as the procedure for #k-SAT with a given exponent and constant; and `StEngine`,
Corollary 6 for machines cut into steps,
with the machine left open. This file has no theorem. It imports the statement files of the
corollaries and files of proof/consequences/WidthK/, proof/consequences/CountKSat/,
proof/consequences/GraphProblems/ and proof/consequences/CircuitLowerBound/. -/

@[expose] public section

namespace Eight

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Paper CountKSat CountKSat.CountTop GraphProblems

/-- Takes the witness off the input of a verifier: from 1^{|w|} 0 w x it returns x. -/
def stripW (y : List Bool) : List Bool := ((y.dropWhile id).tail).drop (y.takeWhile id).length

/-- What a machine E must do to serve as the procedure for #k-SAT with the exponent δ and the
constant c: on (N in unary, ψ), for ψ with clauses of at most k literals, variables below N and no
clause written twice, it returns the number of satisfying
assignments on N variables in N + 1 bits, within c·2^{δN} steps and on states of size at most
c·(N+2)^c. -/
def Serves (E : Stepped (List Unit × Fml) (List Bool)) (k : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (N : ℕ) (ψ : Fml),
  (∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < N) → ψ.Nodup →
  ∃ T : ℕ, E.Runs (List.replicate N (), ψ) T (c * (N + 2) ^ c) (SatK.binary N (cntN N ψ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * N)

/-- Corollary 6 for machines cut into steps, with the machine left open: for every k ≥ 1 and δ > 0
some machine with polynomial-time steps serves. -/
def StEngine : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ E : Stepped (List Unit × Fml) (List Bool), Nonempty (IsPolyT E) ∧ ∃ c : ℕ, Serves E k δ c

end Eight
