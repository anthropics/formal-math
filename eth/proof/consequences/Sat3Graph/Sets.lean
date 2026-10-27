/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import Sat3Graph.Ask
import GraphProblems.Sets
import GraphProblems.Read
import Mathlib.Tactic

/-! # Section 7, Corollary 7 for deciding: Independent Set, Clique, Vertex Cover

Proof of `StSets` of proof/consequences/Sat3Graph/Defs.lean, from `stAskSized` at width 2 (no new
variable: B = 0). The formula is that for independent sets in all three cases: of the graph, of the
complement graph (`Complement.readClique`), or of the graph with n − s in the place of s
(`Complement.readCover`).
What the two readers hand over (`Complement.StReaders`) and the shape of the formula for independent
sets (`Complement.StIndepAlone`) are hypotheses here; Main.lean puts their proofs in. That subsets
of independent sets and of cliques, and supersets of vertex covers, are again such sets is
`GraphProblems.stDecide`. -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat

/-- Let `askSized gates D` answer at width 2 as `StAskSized` says, with the constant c'. Let the
reader rd hand over, on the code of (G, s) with s ≤ n, some (n in unary, s', ψ) with s' ≤ n and ψ of
width 2 on x₀ … xₙ₋₁, such that ψ has a satisfying assignment with exactly s' true variables exactly
if p holds of (G, s). Then `askSized gates D` behind rd decides p with the same constant. -/
theorem decidesGraph_of_reader {gates : ℕ → ℕ → List CircuitLowerBound.GateD} {D : StepMachine (List Unit × Fml) Bool} {δ : ℝ} {c' : ℕ}
    (hA : ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped 2 n ψ → (2 - 3) * ψ.length ≤ 0 * (n + 1) →
      ∃ (T : ℕ) (b : Bool), (askSized gates D).Runs (List.replicate n (), s, ψ) T (c' * (n + 2) ^ c') b ∧ (b = true ↔ cntS n s ψ ≠ 0) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n))
    (rd : List Bool → List Unit × ℕ × Fml) (p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ (s' : ℕ) (ψ : Fml), s' ≤ n ∧ Shaped 2 n ψ ∧
      rd (codeWith G s) = (List.replicate n (), s', ψ) ∧ (cntS n s' ψ ≠ 0 ↔ p n G s)) :
    DecidesGraph (Stepped.mapIn rd (askSized gates D)) p δ c' := by
  intro n G s hs
  obtain ⟨s', ψ, hs', hsh, hrd, hp⟩ := h n G s hs
  obtain ⟨T, b, hr, hb, hT⟩ := hA n s' ψ hs' hsh (by simp)
  rw [← hrd] at hr
  exact ⟨T, b, Stepped.mapIn_runs hr, hb.trans hp, hT⟩

/-- **`StSets`**, from what the readers for cliques and vertex covers hand over and the shape of the
formula for independent sets: for every procedure D for 3-SAT with an exponent δ₃ ≥ 0 such that
δ₃·(a+1) ≤ δ, the machines `INDEP`, `CLIQUE`, `COVER` decide Independent Set, Clique and Vertex
Cover within c'·2^{δn} steps. -/
theorem stSets_of (hRd : Complement.StReaders) (hI : Complement.StIndepAlone) : StSets := by
  intro gates a hT δ δ₃ hδ h0 hle D c hD
  obtain ⟨c', hA⟩ := stAskSized gates a hT 2 0 δ δ₃ hδ h0 (by simpa using hle) D c hD
  refine ⟨c', ?_, ?_, ?_⟩
  · exact decidesGraph_of_reader hA (readF indepF) _ fun n G s hs =>
      ⟨s, indepF n (matrix G), hs, (hI.2 n _).1, by simp [readF, stRead2 n G s], by rw [stIndep n G s]; exact (stDecide n G s hs).1.symm⟩
  · exact decidesGraph_of_reader hA readClique _ fun n G s hs =>
      ⟨s, indepF n (matrix Gᶜ), hs, (hI.2 n _).1, (hRd n G s hs).1.1, by rw [(hRd n G s hs).1.2]; exact (stDecide n G s hs).2.1.symm⟩
  · exact decidesGraph_of_reader hA readCover _ fun n G s hs =>
      ⟨n - s, indepF n (matrix G), Nat.sub_le n s, (hI.2 n _).1, (hRd n G s hs).2.1, by rw [(hRd n G s hs).2.2]; exact (stDecide n G s hs).2.2.1.symm⟩

end Sat3Graph
