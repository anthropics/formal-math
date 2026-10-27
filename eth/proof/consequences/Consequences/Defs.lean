/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
public import SplitSat.Defs
public import SizeCircuit.CircuitDefs
public import Complement.Defs
public import Sat3Graph.Defs
public import Eight.Cor.NSETHDefs
public import CircuitLowerBoundStatement
public import CircuitLowerBoundInfinitelyOftenStatement
public import CircuitLowerBound.Alg.Machine

/-! # A definition for Section 7: what it means that a procedure counts in graphs

`CountsGraph`, used by `Consequences.tm_of_counts` (proof/consequences/Consequences/Main.lean) and
by proof/consequences/FromPrinted/GraphDefs.lean, which puts Corollary 7 on the machine of the
printed proof of Corollary 6. This file has no theorem. -/

@[expose] public section

namespace Consequences

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount SplitSat SizeCircuit Complement

/-- A machine cut into steps returns the number f(G, s), s ≤ n, on the code of (G, s), within
c·2^{δn} steps, on states of size polynomial in n. -/
def CountsGraph (Ms : StepMachine (List Bool) ℕ) (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) (δ : ℝ) (c : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ T : ℕ, Ms.Runs (codeWith G s) T (c * (n + 2) ^ c) (f n G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

end Consequences
