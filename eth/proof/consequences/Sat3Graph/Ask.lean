/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import Sat3Graph.Split
import SplitSat.Leaf
import SizeCircuit.Gamma
import SizeCircuit.Sized
import Mathlib.Tactic

/-! # Section 7, Corollary 7 for deciding: one question to the procedure for 3-SAT

Proof of `StAskSized` of proof/consequences/Sat3Graph/Defs.lean. On (n in unary, s, ψ) the machine
`askSized gates D` puts Γ beside ψ, splits every long clause and asks D.
* The 3-CNF has N = (variables of Γ) + (new variables) variables. Γ has at most (a+1)·(n+1)
  variables (`SizeCircuit.numVars_le`). The clauses of Γ have at most 3 literals and need no new
  variable; those of ψ need at most (w − 3)·|ψ| ≤ B·(n+1). So N ≤ (a+1+B)·(n+1): a 3-CNF on O(n)
  variables.
* The 3-CNF is satisfiable exactly if ψ ∧ Γ is (`splitN_spec`), that is if the number of satisfying
  assignments of ψ ∧ Γ is not 0, and this number is that of the satisfying assignments of ψ with
  exactly s true variables (`SizeCircuit.stGammaCount`, a statement on numbers; `askSized gates D`
  runs no machine but D). -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit SplitSat

/-- What `withGamma` hands over on (n in unary, s, ψ). -/
theorem withGamma_replicate (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (n s : ℕ) (ψ : Fml) :
    withGamma gates (List.replicate n (), s, ψ) = (List.replicate (numVars gates n s) (), (ψ ++ gamma gates n s).dedup) := by
  simp only [withGamma, List.length_replicate]

/-- **`StAskSized`.** Let gates test the size with at most a·(n+1) gates, and let D decide 3-SAT
with an exponent δ₃ ≥ 0 such that δ₃·(a + 1 + B) ≤ δ. On (n in unary, s, ψ), for s ≤ n and ψ of
width at most w on x₀ … xₙ₋₁ with (w − 3)·|ψ| ≤ B·(n+1), `askSized gates D` says, within c'·2^{δn}
steps and on states of size at most c'·(n+2)^{c'}, whether ψ has a satisfying assignment with
exactly s true variables. -/
theorem stAskSized : StAskSized := by
  intro gates a hT w B δ δ₃ _ h0 hle D c hD
  obtain ⟨c', hc'⟩ := exists_bounds (a + 1 + B) c h0 (by push_cast; exact hle)
  refine ⟨c', fun n s ψ _ hψ hB => ?_⟩
  obtain ⟨N0, hN0⟩ : ∃ N0, N0 = numVars gates n s := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ ++ gamma gates n s).dedup := ⟨_, rfl⟩
  have hnN : n ≤ N0 := hN0 ▸ le_numVars gates n s
  have hvars : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N0 := by
    intro C hC l hl
    rw [hφ] at hC
    rcases List.mem_append.1 (List.mem_dedup.1 hC) with h | h
    · exact lt_of_lt_of_le ((hψ C h).2 l hl) hnN
    · exact hN0 ▸ (shaped_gamma hT n s C h).2 l hl
  have hfresh : numFresh φ ≤ B * (n + 1) := by
    have e1 := numFresh_dedup_le (ψ ++ gamma gates n s)
    have e2 := Eight.Width.numFresh_le w ψ fun C hC => (hψ C hC).1
    have e3 : numFresh (gamma gates n s) = 0 := numFresh_eq_zero fun C hC => (shaped_gamma hT n s C hC).1
    rw [numFresh_append, e3] at e1
    rw [hφ]
    omega
  have hN : N0 + numFresh φ ≤ (a + 1 + B) * (n + 1) := by
    have e := numVars_le hT n s
    rw [← hN0] at e
    rw [Nat.add_mul]
    omega
  obtain ⟨h3, hnd, hsat⟩ := splitN_spec hvars
  obtain ⟨T, b, hr, hb, hTle⟩ := hD (N0 + numFresh φ) (splitN N0 φ) h3 hnd
  have hin : widthP (withGamma gates (List.replicate n (), s, ψ)) = (List.replicate (N0 + numFresh φ) (), splitN N0 φ) := by
    rw [withGamma_replicate, ← hN0, ← hφ, widthP_replicate]
  obtain ⟨k1, k2⟩ := hc' n _ T hN hTle
  rw [← hin] at hr
  refine ⟨T, b, (Stepped.mapIn_runs (f := fun p => widthP (withGamma gates p)) (a := (List.replicate n (), s, ψ)) hr).mono le_rfl k1, ?_, k2⟩
  rw [hb, hsat, sat_iff_cntN hvars, hφ, cntN_of_dedup, hN0, stGammaCount gates a hT n s ψ fun C hC => (hψ C hC).2]

end Sat3Graph
