/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Consequences.Defs
import Consequences.Sets
import Consequences.Dom
import SplitCount.Main
import Eight.ViaGrouping.CorGraph
import Eight.ViaGrouping.CorENP
import GraphProblems.Host
import GraphProblems.SetTM
import SplitCount.Sizes
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Color
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # From a machine cut into steps that computes a number from a graph to a Turing machine of Mathlib, and a lemma on binary words

* `tm_of_counts`: a machine cut into polynomial-time steps that returns a number computed from a
  graph within c·2^{(δ/2)n} steps is simulated by a Turing machine of Mathlib that writes `post` of
  the number, for a polynomial-time `post`, within ⌊C·2^{δn}⌋ steps: the host theorem of
  proof/consequences/GraphProblems/, `GraphProblems.tm_of_stepped`.
* `ofWord_binary_lt`: a number below 2^(N+1), written in N + 1 bits and read back, is itself. -/

public section

namespace Consequences

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount Turing

/-- From a machine cut into polynomial-time steps that returns f(G, s) within c·2^{(δ/2)n} steps to
a Turing machine with finite alphabets that, started on the code of (G, s), s ≤ n, halts with
`post (f n G s)` within ⌊C·2^{δn}⌋ steps, for every polynomial-time `post` from numbers to words. -/
theorem tm_of_counts {Ms : StepMachine (List Bool) ℕ} (hp : PolyTimeSteps Ms) {f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ) {c : ℕ} (h : CountsGraph Ms f (δ / 2) c)
    (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
      Outputs M (codeWith G s) (post (f n G s)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨hI⟩ := hp
  have := IsPolyT.mapOut (M := Ms) hpost
  obtain ⟨M, C, hfin, hM⟩ := tm_of_stepped (Stepped.mapOut Ms post) (ι := Inst) (fun x => codeWith x.2.1 x.2.2.1) (fun x => post (f x.1 x.2.1 x.2.2.1)) (fun x => x.1) hδ c 1 2
    (fun x => by
      obtain ⟨n, G, s, hs⟩ := x
      simp only [length_codeWith stMatrixLength]
      nlinarith)
    (fun x => by
      obtain ⟨n, G, s, hs⟩ := x
      obtain ⟨T, hr, hT⟩ := h n G s hs
      exact ⟨T, Stepped.mapOut_runs hr, hT⟩)
  exact ⟨M, C, hfin, fun n G s hs => hM ⟨n, G, s, hs⟩⟩

/-- A number below 2^(N+1), written in N + 1 bits and read back, is itself. -/
theorem ofWord_binary_lt {N v : ℕ} (h : v < 2 ^ (N + 1)) : ofWord (SatK.binary N v) = v := by
  rw [SatK.binary, ← SplitCount.toWord_eq, ofWord_toWord h]

end Consequences
