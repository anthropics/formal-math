/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.StepSparsifyDefs
public import PaperSentencesStatement
import SparsificationLemma.Nodes
import SparsificationLemma.One
import SparsificationLemma.Side
import SparsificationLemma.Len
import SparsificationLemma.Gen
import ThreeSatRateStatement
import ClauseBoundStatement
import CountKSatStatement
import all PaddedDescent.F.MarkDeg

/-! # Appendix C («Counting satisfying assignments as a function of n», proof sketch): the number of clauses of an output

The theorem here is the sentence of the proof sketch of Appendix C on the number of clauses of an
output of the sparsification; its docstring quotes the sentence.
The sketch is written for clauses of 3 literals and Calabro's thresholds. The theorem here holds for
every width k and all thresholds with the four conditions `ThrC`; 2·(θ 0 + … + θ (k−1)) plays the
role of M(ε) of the text.
A node is a pair x = (ψ, 𝒩); `out x` is the list 𝒩 followed by ψ, with every clause written once.
**Not here.** The sentence «Φ has Z·2^(n−v) satisfying assignments» is about the count of one sparse
formula, and the sentences on the running time are the subject of
proof/sparsification/SparsificationLemma/Mach.
The clause «there are at most 2^(εn) outputs» is `StepSparsify.outputs_le`
(proof/sparsification/SparsificationLemma/StepSparsify.lean) with k = 3.
-/

public section

namespace SparsificationLemma.Sketch

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK


section branch
variable {θ : ℕ → ℕ} {k : ℕ} {x : CNode} {H : PCl} {Q : PFml}

end branch

/-! ### The tree -/

/-- «and each has at most (M(ε)+2)n clauses, as there are only 2n clauses with one literal.» For
thresholds with `ThrC`, 1 ≤ k, 1 ≤ τ, paths cut after at least (β 0 + … + β (k−1))·n steps, and 2·(θ
0 + … + θ (k−1)) as M(ε):
the formula at a leaf has at most M(ε)·n clauses, the side list, every clause written once, at most
2n, and the output at most (M(ε)+2)·n. -/
theorem clauses_le {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml} (hk : 1 ≤ k) (hτ : 1 ≤ τ) (hT : ThrC k τ θ β) (hD : (∑ i ∈ range k, β i) * n ≤ D) (hψ : IsKCNF k n ψ) :
    ∀ x ∈ tree θ k D ψ, x.1.length ≤ (2 * ∑ j ∈ range k, θ j) * n ∧ (sideU x.2).length ≤ 2 * n ∧ (out x).length ≤ (2 * (∑ j ∈ range k, θ j) + 2) * n := by
  intro x hx
  obtain ⟨f1, -, f3, -, f5, -⟩ := node_facts hT hψ D x (mem_nodesOf_of_mem_leaves _ _ _ x hx)
  have hst : stepK θ k x.1 = none := by simpa [stepC, stepK] using (stGen stSide k τ n D θ β hk hτ hT hD ψ hψ).1 x hx
  have h1 : x.1.length ≤ (2 * ∑ j ∈ range k, θ j) * n :=
    stLenOfOcc k n _ x.1 f3 fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hT.pos f1 (fun C hC => ⟨(f3 C hC).1, (f3 C hC).2.1⟩) hst v
  have h2 : (sideU x.2).length ≤ 2 * n := length_sideU_le fun C hC l hl => by
    obtain ⟨l', rfl, hl'⟩ := f5 C hC
    rwa [List.mem_singleton.1 hl]
  refine ⟨h1, h2, ?_⟩
  have h3 : (out x).length ≤ (sideU x.2).length + x.1.length := by
    rw [← List.length_append]
    exact (List.dedup_sublist _).length_le
  rw [Nat.add_mul]
  omega

end SparsificationLemma.Sketch
