/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Cor.Defs
public import Eight.ViaGrouping.AlgDefs

/-! # Section 7: what Corollary 7, the circuit lower bound for E^NP and the sentence on NSETH ask of the procedures, and the verifier (definitions only)

The files proof/networks/Eight/ViaGrouping/CorGraph.lean, CorENP.lean and CorNSETH.lean prove
Corollary 7, the circuit lower bound for E^NP (Section 7) and «NSETH is false» for a procedure that
is a parameter. This file has the definitions that their
statements mention:
* `EngineCounts En`: what Corollary 6 for machines cut into steps says, of a family of machines En k
  ℓ τ for #k-SAT;
* `Decides M k δ c`: the same for k-SAT, of one machine;
* `verifier M`: the verifier for tautologies made from a machine M for k-SAT.
This file has no proofs. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Paper CountKSat GraphProblems

/-! ## Procedures for #k-SAT -/

/-- Corollary 6 for machines cut into steps, said of a family of machines En k ℓ τ (k the width, ℓ a
level, τ a threshold parameter of the sparsification): for every k ≥ 1 and δ > 0 there are ℓ and τ
such that En k ℓ τ has polynomial-time steps and serves as
the procedure for #k-SAT with the exponent δ. -/
def EngineCounts (En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (En k ℓ τ) ∧ ∃ c : ℕ, Serves (En k ℓ τ) k δ c

/-! ## Machines for k-SAT -/

/-- The machine M, cut into steps, decides k-SAT with the exponent δ and the constant c: on the code
of a k-CNF φ on n variables it ends within c·2^{δn} steps, on states of size at most c·(length of
the code + 1)^c, with the bit «φ is satisfiable». -/
def Decides (M : StepMachine (List Bool) Bool) (k : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
  ∃ (T : ℕ) (b : Bool), M.Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) b ∧ (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-! ## The verifier -/

/-- The verifier for the tautologies among the k-DNF formulas made from a machine M for k-SAT: take
the witness off and ignore it, run M on the rest, and answer with the opposite bit, as a word of one
bit. -/
def verifier (M : StepMachine (List Bool) Bool) : StepMachine (List Bool) (List Bool) := Stepped.mapOut (Stepped.mapIn stripW M) fun b => [!b]

end Eight.ViaGrouping
