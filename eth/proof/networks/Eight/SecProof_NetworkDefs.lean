/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecProof_Proof

/-! # Section 6 of the paper, «Proof of Theorem 2»: definitions for the sentences on the network of Φ

The words of the paragraph «Clusters, occurrences, equality tests» in which the statements of
proof/networks/Eight/SecProof_Network.lean are written: the variables that occur in Φ, the
assignments of these variables and the number of those that satisfy
Φ, the occurrences, and the equality tests. This file has definitions only; nothing is proved or
assumed here. A formula is `Paper.Formula`: a list of clauses, a clause being a list of literals
(variable, value that makes the literal
true). -/

@[expose] public section

namespace Eight

open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper

/-! ## The variables that occur, and their assignments -/

/-- The set of the variables that occur in Φ. A literal is a pair (variable, value that makes the
literal true). -/
def occurring (Φ : Formula) : Finset ℕ := (Φ.flatten.map Prod.fst).toFinset

/-- An assignment of the variables that occur in Φ: one bit for each of them, and for no other
variable. -/
abbrev Assignment (Φ : Formula) : Type := {v : ℕ // v ∈ occurring Φ} → Bool

/-- The assignment a satisfies Φ: every clause has a literal (v, b) with a(v) = b. -/
def Satisfies (Φ : Formula) (a : Assignment Φ) : Prop := ∀ C ∈ Φ, ∃ l ∈ C, ∃ h : l.1 ∈ occurring Φ, a ⟨l.1, h⟩ = l.2

instance (Φ : Formula) : DecidablePred (Satisfies Φ) := fun a => by unfold Satisfies; infer_instance

/-- The number of assignments of the variables occurring in Φ that satisfy Φ. -/
def numSat (Φ : Formula) : ℕ := #{a : Assignment Φ | Satisfies Φ a}

/-- An assignment of the occurring variables, continued by 0 to all variables. -/
def continued {Φ : Formula} (a : Assignment Φ) (v : ℕ) : Bool := if h : v ∈ occurring Φ then a ⟨v, h⟩ else false

/-! ## Occurrences and equality tests -/

/-- The occurrences, for g clusters of μ clauses with k positions each: the positions (cluster,
clause of the cluster, place in the clause) that hold a literal. The paper: «An occurrence is a pair
o = (E, ω) of a clause E ∈ Φ and a
literal ω ∈ E, that is, one position of one clause.» -/
def occurrencesOf (Φ : Formula) (g μ k : ℕ) : Finset (Slot g μ k) := {p | lit Φ p ≠ none}

/-- The equality tests: the pairs (o, o') of consecutive occurrences of a variable, the occurrences
of each variable being listed in reading order (`Groundwork.SatNet.Link`). The paper: «any order
will do». A test is written here as the
ordered pair with the earlier occurrence first. -/
def testsOf (Φ : Formula) (g μ k : ℕ) : Finset (Slot g μ k × Slot g μ k) := {t | Link Φ t.1 t.2}

/-- The occurrences in Φ, when Φ is cut into g clusters of m̄ = ⌈m/g⌉ clauses with 3 positions each,
as in `Paper.networkOf g Φ`. -/
abbrev occurrences (g : ℕ) (Φ : Formula) : Finset (Slot g (clusterSize g Φ) 3) := occurrencesOf Φ g (clusterSize g Φ) 3

/-- The equality tests of Φ, for the same clusters. -/
abbrev tests (g : ℕ) (Φ : Formula) : Finset (Slot g (clusterSize g Φ) 3 × Slot g (clusterSize g Φ) 3) := testsOf Φ g (clusterSize g Φ) 3

end Eight
