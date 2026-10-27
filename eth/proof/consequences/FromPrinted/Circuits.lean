/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.GraphDefs
import FromPrinted.Count
import FromPrinted.Sets
import FromPrinted.Dom
import Consequences.Main
import Eight.ViaGrouping.CorGraph
import Eight.ViaGrouping.CorENP
import GraphProblems.Host
import GraphProblems.SetTM
import SplitCount.Sizes
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Color
import Mathlib.Tactic

/-! # Corollary 7 on the machines of its printed proof, and the circuit lower bound for E^NP (Section 7) on the procedure of Corollary 6, on the machines of proof/threesat/Printed/

`Consequences.tm_of_counts` and `Consequences.ofWord_binary_lt`
(proof/consequences/Consequences/Main.lean), which name no machine, are used as they stand.
* `tm_of_colorings`: the machine of `StColoringsCounted` is simulated by a Turing machine of
  Mathlib: the host theorem of proof/consequences/GraphProblems/, `GraphProblems.tm_of_stepped`.
* `graphsFrom`, `graphsByCounting`: Corollary 7, both sentences, from `StSetsCounted`,
  `StDominatingCounted`, `StColoringsCounted` as hypotheses, then on their proofs; «In particular,
  they decide …» by `GraphProblems.stDecide` and `GraphProblems.stDecideColor`.
* `circuitsFrom`, `circuits`: the circuit lower bound for E^NP (the paragraph «Circuit lower bounds»
  in Section 7) in its three Lean forms, from Corollary 6 for machines cut into steps
  (`Eight.ViaGrouping.EngineCounts`) for the family `FromPrinted.SplitCount.ENGINEsplit`, as a
  hypothesis, then on its proof; `stAlgoRuns` names the machine inside. -/

public section

open Consequences

namespace FromPrinted.Consequences

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing

/-- A Turing machine with finite alphabets that, started on the code of a graph G on n vertices,
halts with `post` of the number of proper colorings of G with k ≥ 3 colors within ⌊C·2^{δn}⌋ steps,
from the statement `StColoringsCounted` as a hypothesis: it simulates the machine of that statement
at δ/2. -/
theorem tm_of_colorings (hCol : StColoringsCounted) (k : ℕ) (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      Outputs M (code G) (post (numColorings G k)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ, τ, c, ⟨hI⟩, h⟩ := hCol k hk (δ / 2) (by positivity)
  have hp : PolyT fun x : List Bool => post (ofWord x) := PolyT.comp hpost (by fun_prop)
  have := IsPolyT.mapOut (M := Stepped.mapIn (readC k) (ENGINEsplit (max k 2) ℓ τ)) hp
  obtain ⟨M, C, hfin, hM⟩ := tm_of_stepped (Stepped.mapOut (Stepped.mapIn (readC k) (ENGINEsplit (max k 2) ℓ τ)) fun x => post (ofWord x))
    (ι := (n : ℕ) × SimpleGraph (Fin n)) (fun x => code x.2) (fun x => post (numColorings x.2 k)) (fun x => x.1) hδ c 1 2
    (fun x => by
      obtain ⟨n, G⟩ := x
      simp only [length_code stMatrixLength]
      nlinarith)
    (fun x => by
      obtain ⟨n, G⟩ := x
      obtain ⟨T, hr, hT⟩ := h n G
      have hrun := Stepped.mapOut_runs (f := fun x => post (ofWord x)) hr
      have hle : numColorings G k < 2 ^ (n * k + 1) := by
        rw [← stColor stAdj k n G]
        exact lt_of_le_of_lt (SplitCount.cntN_le _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
      simp only [ofWord_binary_lt hle] at hrun
      exact ⟨T, hrun, hT⟩)
  exact ⟨M, C, hfin, fun n G => hM ⟨n, G⟩⟩

/-- **Corollary 7**, both sentences, in the wording of GraphProblemsStatement.lean
(`GraphsByCounting`): the five numbers are computed, and the five problems decided, in time
O(2^{δn}) on Turing machines. Here it is drawn from the three statements that name the machines, as
hypotheses: the Turing machines simulate the machines named in `StSetsCounted`,
`StDominatingCounted` and `StColoringsCounted`. -/
theorem graphsFrom (hSets : StSetsCounted) (hDom : StDominatingCounted) (hCol : StColoringsCounted) : GraphsByCounting := by
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨ℓ, τ, c, ⟨p1, h1⟩, ⟨p2, h2⟩, ⟨p3, h3⟩⟩ := hSets (δ / 2) (by positivity)
    obtain ⟨w, ℓ', τ', c', -, p4, h4⟩ := hDom (δ / 2) (by positivity)
    exact ⟨tm_of_counts p1 hδ h1 Nat.bits bits_polyT, tm_of_counts p2 hδ h2 Nat.bits bits_polyT, tm_of_counts p3 hδ h3 Nat.bits bits_polyT,
      tm_of_counts p4 hδ h4 Nat.bits bits_polyT, fun k hk => tm_of_colorings hCol k hk hδ Nat.bits bits_polyT⟩
  · -- «In particular, they decide …»
    obtain ⟨ℓ, τ, c, ⟨p1, h1⟩, ⟨p2, h2⟩, ⟨p3, h3⟩⟩ := hSets (δ / 2) (by positivity)
    obtain ⟨w, ℓ', τ', c', -, p4, h4⟩ := hDom (δ / 2) (by positivity)
    refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p1 hδ h1 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).1.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p2 hδ h2 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).2.1.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p3 hδ h3 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).2.2.1.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p4 hδ h4 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).2.2.2.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_colorings hCol k hk hδ nzW nzW_polyT
      exact ⟨M, C, hf, fun n G => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecideColor k n G).symm, h n G⟩⟩

/-- **Corollary 7**, both sentences: `graphsFrom` on the proofs `stSetsCounted`,
`stDominatingCounted`, `stColoringsCounted`. -/
theorem graphsByCounting : GraphsByCounting := graphsFrom stSetsCounted stDominatingCounted stColoringsCounted

/-- **The algorithm inside the circuit lower bound for E^NP (Section 7), with the procedure of
Corollary 6 named**: `Eight.ViaGrouping.ALGO_runs_of` at the family `ENGINEsplit`. For every δ > 0
there are ℓ, τ, c such that `ENGINEsplit 3 ℓ τ` has polynomial-time steps and
`CircuitLowerBound.Alg.algo (ENGINEsplit 3 ℓ τ) F fb` ends on every input x with the bit that says
whether the formula made from x is unsatisfiable within c·2^{δN} steps, N the number of variables of
that formula, for every F with `CircuitLowerBound.Alg.FormOK` and every fb. -/
theorem stAlgoRuns : StAlgoRuns := fun _ hδ => ALGO_runs_of stEngineCounts hδ

/-- **The circuit lower bound for E^NP** (the paragraph «Circuit lower bounds» in Section 7) in its
three Lean forms (`ENP.CorCircuits`, `ENP.CorCircuits'`, `ENP.CorCircuitsInf`), from Corollary 6 for
machines cut into steps (`Eight.ViaGrouping.EngineCounts`) for the family
`FromPrinted.SplitCount.ENGINEsplit`, as a hypothesis. -/
theorem circuitsFrom (h : EngineCounts ENGINEsplit) : Circuits :=
  ⟨corCircuits_of (stEngine_of h), corCircuits'_of (stEngine_of h), corCircuitsInf_of (stEngine_of h)⟩

/-- **The circuit lower bound for E^NP** (Section 7) in its three Lean forms: `circuitsFrom` on the
proof `FromPrinted.SplitCount.stEngineCounts`. -/
theorem circuits : Circuits := circuitsFrom stEngineCounts

end FromPrinted.Consequences
