/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecLevel_Recursion
public import StepMachines.Prog.Sat
import all StepMachines.Prog.Count
public import StepMachines.Math.SparsifyCount
public import StepMachines.Math.SatArith
public import StepMachineStatements
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import StepMachines.Math.SparsifyList
public import ToTuring.Poly.Count
public import ToTuring.Poly.Sat

/-! # Section 6 of the paper: formulas as the algorithm holds them, the network of a formula ("Clusters, occurrences, equality tests"), and the bound on its total U -/

@[expose] public section

namespace Paper

open Groundwork Groundwork.Prog Finset

/-! ### Formulas inside the algorithm -/

/-- A formula as the algorithm holds it in memory: a list of clauses, a clause being a list of
literals (number of the variable,
value that makes the literal true). -/
abbrev Formula : Type := Fml

/-- Nonempty clauses of at most 3 literals, on the variables x₀, …, xₙ₋₁ (the paper's "3-CNF on n
variables"). -/
def Formula.Is3CNF (n : ℕ) (ψ : Formula) : Prop := ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n

/-! ### The network of a formula -/

/-- m̄ = ⌈m/g⌉, the number of clauses of a cluster. -/
abbrev clusterSize (g : ℕ) (Φ : Formula) : ℕ := Count.mu g Φ

/-- **The network of Φ** on [g] ("Clusters, occurrences, equality tests"). Cluster a consists of the
clauses number a·m̄, …, a·m̄ + m̄ - 1.
A setting of node a has one bit for each of the 3m̄ positions (3 per clause) of its cluster; W_a is
1 exactly if every clause of the
cluster has a true occurrence, the tests inside the cluster hold, and the bits at positions without
a literal are 0; c_ab is
the number of tests between the clusters a and b, and f_ab(z, θ) = [z restricted to these tests =
θ].
Differences from the paper: every clause has exactly 3 positions, some of which may be empty, and
the occurrences of a variable are
listed in reading order. -/
abbrev networkOf (g : ℕ) (Φ : Formula) : Network (Fin g) (List Bool) (List Bool) := Count.wordNet g 3 Φ

/-- "U < 6m". (Here: U ≤ 6m.) -/
theorem network_total_le {g : ℕ} (hg : 0 < g) (Φ : Formula) : (networkOf g Φ).U ≤ 6 * Φ.length := by
  rw [Count.U_wordNet hg]
  exact SatNet.U_net_le

end Paper
