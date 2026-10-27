/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Cor.Graph
public import Eight.ViaGrouping.CorDefs2
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Color
import GraphProblems.Blocks
import GraphProblems.DomTree
import GraphProblems.Cert
import GraphProblems.SetTM
import GraphProblems.Interfaces
import GraphProblems.Host
import CountKSat.Walk
import Mathlib.Tactic

/-! # Section 7, Corollary 7: proper colorings, from a procedure for #k-SAT that is a parameter

As in the paper, Corollary 7 applies Corollary 6 to formulas made from the graph.
proof/networks/Eight/Cor/Graph.lean proves the places at which the procedure for #k-SAT enters for a
procedure E that is a parameter (among them `Eight.color_counts`).
This file draws two steps towards Corollary 7 from a family of such procedures:
* `EngineCounts En` (proof/networks/Eight/ViaGrouping/CorDefs2.lean) says of a family of machines En
  k ℓ τ what Corollary 6 for machines cut into steps says: for every k ≥ 1 and δ > 0 some En k ℓ τ
  has polynomial-time steps and serves as the procedure for #k-SAT with the exponent δ;
* `COLOR_counts_of`: the machine of Corollary 7 that counts proper colorings, with the procedure
  named, En k ℓ τ;
* `stEngine_of`: from `EngineCounts En`, the statement `Eight.StEngine`, in which the procedure is
  left open.
The proofs in this file name no algorithm for cliques or for networks. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing

variable {En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)}

/-- `EngineCounts En` gives Corollary 6 for machines cut into steps with the machine left open
(`Eight.StEngine`). -/
theorem stEngine_of (h : EngineCounts En) : StEngine := fun k hk δ hδ =>
  let ⟨ℓ, τ, hp, hc⟩ := h k hk δ hδ
  ⟨En k ℓ τ, hp, hc⟩

/-! ### Colorings -/

/-- **Counting the proper colorings, with the procedure named.** For every k ≥ 1 and δ > 0 there are
a level ℓ and a threshold parameter τ such that the reader `readC k` followed by `En (max k 2) ℓ τ`
has polynomial-time steps and returns, on the code of a graph G on
n vertices, the number of proper colorings of G with k colors in n·k + 1 bits, within c·2^{δn}
steps. -/
theorem COLOR_counts_of (h : EngineCounts En) (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, PolyTimeSteps (Stepped.mapIn (readC k) (En (max k 2) ℓ τ)) ∧
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ T : ℕ, (Stepped.mapIn (readC k) (En (max k 2) ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) (SatK.binary (n * k) (numColorings G k)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨ℓ, τ, ⟨hE⟩, c, hc⟩ := h (max k 2) (le_max_of_le_right (by norm_num)) (δ / k) (by positivity)
  refine ⟨ℓ, τ, ⟨IsPolyT.mapIn (M := En (max k 2) ℓ τ) (readC_polyT stCertRead stCertForm k)⟩, c * k ^ c + c, fun n G => ?_⟩
  have h := color_counts stRead1 stShapeColor k hk hc n G
  rwa [stColor stAdj k n G] at h

end Eight.ViaGrouping
