/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatOnTree.Defs
public import Eight.SecProof_Proof
import SparsificationLemma.TreeWalk.Walk
import Eight.SecPseudocode_Levels
import WidthK.Top.Poly
import WidthK.Poly.Decode
import SparsifyWidthK.Poly.Sparsify
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # The sparsification of Appendix C for the proof of Theorem 2

The proof of Theorem 2 in its decision form (Section 6) takes one thing from Lemma 4 in its form for
deciding: with ε = δ/3, it suffices to decide whether a 3-CNF Φ with m ≤ Mn clauses is satisfiable,
in time O(2^{δ'm}), δ' = δ/(3M). In this development it is
the property `Eight.SufficesSparse δ M S` of a constant M and of a construction S of machines,
defined in proof/networks/Eight/SecProof_Proof.lean.
This file proves the property from `SparsificationLemma.TreeWalk.lemSparsification_walk`
(`sufficesSparse_viaC`): the tree is that of the procedure of Appendix C at width 3 with the
thresholds θ 0 = 1, θ i = 4·τ^(2i−1), the tree whose leaves are the formulas ψ of the nodes (ψ, 𝒩)
of `SparsificationLemma.tree`.
M = 2·(θ 0 + θ 1 + θ 2) bounds the number of clauses of a leaf per variable. S = `satC τ`
(proof/threesat/ThreeSatOnTree/Defs.lean). Its correctness and its number of steps are `sat_correct`
of proof/consequences/WidthK/Top/Sat.lean, which asks of the tree only the property `Sparsifies`.
`one_le_leafCU` says that M ≥ 1.
Different from the paper: the walk tests ψ at a leaf and not the output ψ ∪ 𝒩; a formula is
satisfiable exactly if ψ is satisfiable at some leaf. The list of Lemma 4 is never written, and the
time clause of Lemma 4 is not used. -/

public section

namespace ThreeSatOnTree

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight SparsificationLemma.TreeWalk

/-- The constant M = 2·(θ 0 + θ 1 + θ 2) is at least 1. -/
theorem one_le_leafCU (τ : ℕ) : (1 : ℝ) ≤ (leafCU τ 3 : ℝ) := by
  have h : leafCU τ 3 = 2 * ∑ j ∈ Finset.range 3, thetaU τ j := rfl
  have h0 : thetaU τ 0 = 1 := rfl
  have : 1 ≤ leafCU τ 3 := by
    rw [h, Finset.sum_range_succ', h0]
    omega
  exact_mod_cast this

/-- **«By Lemma 4 with ε = δ/3», in Theorem 2 in its decision form: it suffices to decide whether a
3-CNF Φ with m ≤ Mn clauses is satisfiable, in time O(2^{δ'm})**, with Lemma 4 in the form
`SparsificationLemma.TreeWalk.lemSparsification_walk`: M = 2·(θ 0 + θ 1 + θ 2) for its parameter τ,
and S = `satC τ`. -/
theorem sufficesSparse_viaC {δ : ℝ} (hδ : 0 < δ) : ∃ τ : ℕ, 24 ≤ τ ∧ SufficesSparse δ (leafCU τ 3 : ℝ) (satC τ) := by
  obtain ⟨τ, hτ, hsp, -⟩ := lemSparsification_walk (ε := δ / 3) (by positivity)
  have hM := one_le_leafCU τ
  refine ⟨τ, hτ, fun Mc hMc => ?_, fun Mc A hMc => ?_⟩
  · obtain ⟨h⟩ := hMc
    exact ⟨isPolyT_satMK (DecodeK.decK_polyT 3) (certStep (thetaU τ) 3) (by fun_prop)⟩
  · have hδB : δ / (3 * (leafCU τ 3 : ℝ)) * (leafCU τ 3 : ℝ) ≤ δ / 3 := le_of_eq (by field_simp)
    exact sat_correct (le_of_lt (by norm_num : 1 < 3)) hδ (by positivity) (fun n φ h => DecodeK.decK_enc (by norm_num) h) hsp hδB Mc A hMc

end ThreeSatOnTree
