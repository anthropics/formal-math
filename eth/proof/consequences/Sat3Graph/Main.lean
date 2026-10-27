/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import SizeCircuit.CircuitDefs
import Sat3Graph.Sets
import Sat3Graph.Dominating
import Sat3Graph.Coloring
import Sat3Graph.Cert
import Sat3Graph.Host
import SizeCircuit.Circuit
import SizeCircuit.Cert
import Complement.Readers
import SplitSat.Procedure
import GraphProblems.DomTree
import Mathlib.Tactic

/-! # Section 7, Corollary 7 (the decision problems): parts of the proof

Proofs of the statements `StSets` and `StCert` of proof/consequences/Sat3Graph/Defs.lean, and a
lemma that turns a hosted decider into a decider in time O(2^{δn}).
Hosting with polynomial overhead is in Host.lean. -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat

/-- **`StSets`.** Independent Set, Clique and Vertex Cover from 3-SAT, for every procedure D with an
exponent δ₃ ≥ 0 such that δ₃·(a+1) ≤ δ. -/
theorem stSets : StSets := stSets_of stReaders stIndepAlone

/-- **`StCert`.** The steps of the five deciders are polynomial time if those of D are and the
circuits are computed in polynomial time. -/
theorem stCert : StCert := stCert_of stReadersCert stIndepAlone

/-- A property that a hosted decider decides is decided in time O(2^{δn}). -/
theorem decidesInTime_of_hosted {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ : ℝ} (h : HostedFor Ms p δ) :
    DecidesInTime p δ := by
  obtain ⟨M, c, q, hf, -, hM⟩ := h
  exact ⟨M, c, hf, hM⟩

end Sat3Graph
