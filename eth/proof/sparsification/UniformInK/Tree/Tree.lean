/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Tree.Defs
public import CountKSatRate.Tree
import all PaddedDescent.F.MarkDeg
import Mathlib.Tactic.Ring

/-! # The sparsification lemma for counting with the geometric thresholds

This file proves `StTreeU` of proof/sparsification/UniformInK/Tree/Defs.lean from `StIfaceU` of
proof/sparsification/UniformInK/Spars/Defs.lean. Its proof follows that of `CountKSatRate.stTreeK`
(proof/consequences/CountKSatRate/Tree.lean). The lemma
`CountKSatRate.Tree.tree_of` there holds for all thresholds and bounds that satisfy `Iface` and
`Refines`, and is used here with the thresholds `thetaU τ`, the depth bound `bsumU τ k · n`, a
budget of k·n units
of which a heavy step spends τ, and at most `leafCU τ k · n` clauses in a leaf. As there, τ ≥ k²
bounds the side list by 2n clauses, and `length_occ_le_of_none` of
proof/rates/PaddedDescent/F/MarkDeg.lean bounds the
number of clauses of a leaf in which a variable occurs. -/

public section

namespace UniformInK

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate WidthK.Prog

namespace Tree

/-- Every threshold is at least 1, if τ ≥ 1. -/
theorem one_le_thetaU {τ : ℕ} (hτ : 1 ≤ τ) : ∀ i, 1 ≤ thetaU τ i
  | 0 => le_refl 1
  | i + 1 => Nat.mul_pos (by norm_num) (Nat.pow_pos hτ)

end Tree

/-- From `StIfaceU`: the sparsification lemma for counting at width k with the thresholds `thetaU τ`
and a side list of at most 2n clauses, the interface statement `StTreeU`. -/
theorem stTreeU (hIf : StIfaceU) : StTreeU := by
  intro k τ n hk hτk hτ8 ψ hψ
  have hτ : 1 ≤ τ := (Nat.one_le_pow 2 k hk).trans hτk
  have hθ : ∀ i, 1 ≤ thetaU τ i := Tree.one_le_thetaU hτ
  have hI := hIf τ k n hk hτ8
  have hOk : WidthK.ProgMain.Ok k n (toFin ψ) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [WidthK.ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
  have hT : k * n < (k * n / τ + 1) * τ := by
    calc k * n < τ * (k * n / τ + 1) := Nat.lt_mul_div_succ (k * n) (by omega : 0 < τ)
      _ = (k * n / τ + 1) * τ := Nat.mul_comm _ _
  have hB : n * τ + k * (k * n) ≤ 2 * n * τ := by
    have := Nat.mul_le_mul_left n hτk
    calc n * τ + k * (k * n) = n * τ + n * k ^ 2 := by ring
      _ ≤ n * τ + n * τ := by omega
      _ = 2 * n * τ := by ring
  obtain ⟨c1, c2, c3, c4⟩ := CountKSatRate.Tree.tree_of stStepCount stRootCount stSumLeaves hθ hI (WidthK.Refine.stRefines _ k hθ) hT hB ψ hOk
    fun C hC => (hψ C hC).2
  have er : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
  rw [er]
  refine ⟨c1, fun x hx => ?_, c3, c4⟩
  obtain ⟨d1, d2, d3, p', t', hx'⟩ := c2 x hx
  have hne : ∀ C ∈ x.1, C ≠ [] := by
    intro C hC
    obtain ⟨C', hC', hsub, hne⟩ := hx'.1.2.2.1 _ (WidthK.ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨-, b, -⟩ := hx'.1.2.1 C' hC'
    exact (List.toFinset_nonempty_iff C).1 (hne b)
  have hst : stepK (thetaU τ) k x.1 = none := by simpa [stepC, stepK] using d1
  exact ⟨d1, d2.trans (le_of_eq (by ring)), fun C hC => ⟨hne C hC, d3 C hC⟩,
    fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hθ hx'.1.1 (fun C hC => ⟨hne C hC, (d3 C hC).1⟩) hst v,
    fun C hC => ⟨hx'.2.2.2.2 C hC, (hx'.2.2.1 C hC).2⟩⟩

end UniformInK
