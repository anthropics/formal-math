/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.GraphDefs
import FromPrinted.Count
import Consequences.Sets
import SizeCircuit.Main
import Complement.Readers
import Eight.ViaGrouping.CorGraph
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Cert
import GraphProblems.SetTM
import Mathlib.Tactic

/-! # Proof of Corollary 7 on the machines of proof/threesat/Printed/: sets of size s and colorings, with the machines named

«Add the clause {¬x_u, ¬x_v} for each edge uv; Corollary 6 then counts the independent sets of size
s. The cliques of size s are the independent sets of size s of the complement graph, and the vertex
covers of size s are the complements of the independent sets of size n − s.»
The counts come from `FromPrinted.SplitCount.stEngineCounts`; the bounds on states and steps use
`size_square` and `steps_double` of proof/consequences/Consequences/Sets.lean.
* `SIZED_counts`: for every width w and δ > 0 some `SIZED w ℓ τ` has polynomial-time steps and
  counts the satisfying assignments with exactly s true variables: `SizeCircuit.stSizedFromEngines`
  for the family `FromPrinted.SplitCount.ENGINEsplit` and the circuits `SizeCircuit.sizeGates`
  (`SizeCircuit.stSizeGates`).
* `stSetsCounted`: that machine at width 2 after the three readers; for cliques and vertex covers by
  `Complement.stCounts`.
* `stColoringsCounted`: `Eight.ViaGrouping.COLOR_counts_of` for the family `ENGINEsplit`. -/

public section

open Consequences

namespace FromPrinted.Consequences

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement

/-- For every width w and δ > 0 there are ℓ, τ such that `SIZED w ℓ τ` has polynomial-time steps and
returns, on (n in unary, s, ψ) for s ≤ n and ψ of width at most w on x₀ … xₙ₋₁, the number of
satisfying assignments of ψ with exactly s true variables, within c·2^{δn} steps, on states of size
at most c·(n + number of clauses + 2)^c. -/
theorem SIZED_counts (w : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, PolyTimeSteps (SIZED w ℓ τ) ∧ ∃ c : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, (SIZED w ℓ τ).Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨a, hT, hC⟩ := stSizeGates
  exact stSizedFromEngines ENGINEsplit stEngineCounts sizeGates a hT hC w δ hδ

/-- **Independent sets, cliques, vertex covers of size s, with the machines named.** For every δ > 0
there are ℓ, τ, c such that `SIZED 2 ℓ τ`, put after the reader of the formula for independent sets,
after `readClique` and after `readCover`, has polynomial-time steps and returns the three numbers
within c·2^{δn} steps, on states of size at most c·(n+2)^c. -/
theorem stSetsCounted : StSetsCounted := by
  intro δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c, h⟩ := SIZED_counts 2 hδ
  have hpos : ∀ n : ℕ, (0 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := fun n => by positivity
  refine ⟨ℓ, τ, 2 * c, ⟨⟨IsPolyT.mapIn (M := SIZED 2 ℓ τ) (readF_polyT stCertRead stIndepAlone.1)⟩, fun n G s hs => ?_⟩,
    ⟨⟨IsPolyT.mapIn (M := SIZED 2 ℓ τ) stReadersCert.1⟩, fun n G s hs => ?_⟩, ⟨⟨IsPolyT.mapIn (M := SIZED 2 ℓ τ) stReadersCert.2⟩, fun n G s hs => ?_⟩⟩
  · obtain ⟨T, hr, hT⟩ := h n s (indepF n (matrix G)) hs (stIndepAlone.2 n _).1
    have hread : readF indepF (codeWith G s) = (List.replicate n (), s, indepF n (matrix G)) := by simp [readF, stRead2 n G s]
    rw [← hread, stIndep n G s] at hr
    exact ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (size_square (stIndepAlone.2 n _).2), hT.trans (steps_double c (hpos n))⟩
  · obtain ⟨T, hr, hT⟩ := (stCounts (SIZED 2 ℓ τ) δ c h n G s hs).1
    exact ⟨T, hr.mono le_rfl (size_square le_rfl), hT.trans (steps_double c (hpos n))⟩
  · obtain ⟨T, hr, hT⟩ := (stCounts (SIZED 2 ℓ τ) δ c h n G s hs).2
    exact ⟨T, hr.mono le_rfl (size_square le_rfl), hT.trans (steps_double c (hpos n))⟩

/-- **Proper colorings with k colors, with the machine named.** For every k ≥ 3 and δ > 0 there are
ℓ, τ, c such that the reader `readC k` followed by `ENGINEsplit (max k 2) ℓ τ` has polynomial-time
steps and returns, on the code of a graph G on n vertices, the number of proper colorings of G with
k colors in n·k + 1 bits, within c·2^{δn} steps, on states of size at most c·(n+2)^c. -/
theorem stColoringsCounted : StColoringsCounted := by
  intro k hk δ hδ
  obtain ⟨ℓ, τ, hp, c, h⟩ := COLOR_counts_of stEngineCounts k (by omega) hδ
  exact ⟨ℓ, τ, c, hp, h⟩

end FromPrinted.Consequences
