/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
public import CountKSatRate.Tree
import SparsificationLemma.Iface
import SparsificationLemma.Shrink
import all CountKSatRate.Leaf
import all PaddedDescent.F.MarkDeg
import Mathlib.Tactic.Ring

/-! # The sparsification for all thresholds with `ThrC`

This file proves `StGen` and `StTreeG` of proof/sparsification/SparsificationLemma/Defs.lean.
`Gen.withSideClauses` is about the tree of proof/consequences/CountKSat/Defs.lean, whose side list
starts with the n clauses xᵢ ∨ ¬xᵢ. It applies `CountKSatRate.Tree.tree_of`
(proof/consequences/CountKSatRate/Tree.lean), which holds for all
thresholds and bounds that satisfy `Iface` and `Refines`, with `stIfaceC`: the depth is at most D,
and a budget of (k−1)·n is spent τ at a time, at the second child of a step. As in
proof/sparsification/UniformInK/Tree/Tree.lean, `length_occ_le_of_none` of
proof/rates/PaddedDescent/F/MarkDeg.lean bounds the number of clauses of a leaf in which a variable
occurs. For the last part of `StGen`, that no node has more clauses than ψ, the invariant of the
tree is carried along together with «at most as many clauses as ψ»,
which both children inherit by `Shrink.length_step_le`.
`stGen` moves these facts to the tree that starts with the empty side list, by `StSide`.
`stTreeG` takes everything from `Gen.withSideClauses` except the identity of the counts. That
identity comes from `StExactlyOne` and `StCountOfExactlyOne`: the count of ψ is the sum of the
counts of the outputs; by
`StOutputsSame` the outputs are the formulas `out x` of the tree whose side list starts with the
clauses xᵢ ∨ ¬xᵢ, and `out x`, `leafM x` and `leafF x` have the same satisfying assignments. -/

public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)

namespace Gen

variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}

/-- The set of clauses of a k-CNF on n variables satisfies the condition `Ok` on the formula at the
root. -/
theorem ok_of (hψ : IsKCNF k n ψ) : ProgMain.Ok k n (toFin ψ) := by
  intro X hX
  obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
  obtain ⟨a, b, c⟩ := hψ C hC
  refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
  rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
  exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩

/-- The formula at the root has at most as many clauses as ψ. -/
theorem length_rootP_le (ψ : PFml) : (rootP ψ).length ≤ ψ.length :=
  (List.length_filter_le _ _).trans ((List.dedup_sublist _).length_le.trans (by simp))

/-- The invariant of the tree of proof/consequences/CountKSatRate/Tree.lean with the node predicate
of `StIfaceC`, together with «the formula of the node has at most as many clauses as ψ». -/
def InvL (θ : ℕ → ℕ) (k τ n : ℕ) (ψ : PFml) (x : CNode) (p t : ℕ) : Prop :=
  CountKSatRate.Tree.GT (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU θ k τ F₀ F p t) ψ n k τ x p t ∧ x.1.length ≤ ψ.length

/-- The tree whose side list starts with the clauses xᵢ ∨ ¬xᵢ, for thresholds with `ThrC`, τ ≥ 1 and
D ≥ (β 0 + … + β (k-1))·n. B is any bound for the side list: n·τ + k·(k−1)·n ≤ B·τ.
The number of leaves; what holds at a leaf; the stack of the depth-first walk. -/
theorem withSideClauses (hτ : 1 ≤ τ) (hT : ThrC k τ θ β) (hD : (∑ i ∈ range k, β i) * n ≤ D) (hψ : IsKCNF k n ψ) {B : ℕ}
    (hB : n * τ + k * ((k - 1) * n) ≤ B * τ) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n),
      stepC θ k x = none ∧ (leafF x).length ≤ (2 * ∑ j ∈ range k, θ j) * n + B ∧
        (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j) ∧
        (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧ x.1.length ≤ ψ.length) ∧
    ∀ i, ((round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1,
        x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ B ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by
  have hθ : ∀ i, 1 ≤ θ i := hT.pos
  have hI := stIfaceC k τ n D θ β hT hD
  have hR := Refine.stRefines θ k hθ
  have hOk := ok_of hψ
  have hψ' : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := fun C hC => (hψ C hC).2
  have hT' : (k - 1) * n < ((k - 1) * n / τ + 1) * τ := by
    calc (k - 1) * n < τ * ((k - 1) * n / τ + 1) := Nat.lt_mul_div_succ _ (by omega : 0 < τ)
      _ = ((k - 1) * n / τ + 1) * τ := Nat.mul_comm _ _
  obtain ⟨c1, c2, -, c4⟩ := CountKSatRate.Tree.tree_of stStepCount stRootCount stSumLeaves hθ hI hR hT' hB ψ hOk hψ'
  have hs : ∀ (s : CNode) (p t : ℕ) (l h : CNode), InvL θ k τ n ψ s p t → stepC θ k s = some (l, h) →
      InvL θ k τ n ψ l (p + 1) t ∧ InvL θ k τ n ψ h (p + 1) (t + τ) := by
    intro s p t l h hG hst
    obtain ⟨g1, g2⟩ := CountKSatRate.Tree.GT_step hθ hI hR ψ hψ' s p t l h hG.1 hst
    obtain ⟨-, N, a, hh, hInv, -⟩ := hG.1.1.2.2
    obtain ⟨l1, l2⟩ := Shrink.length_step_le hθ hG.1.1.1 hInv.red hst
    exact ⟨⟨g1, l1.trans hG.2⟩, ⟨g2, l2.trans hG.2⟩⟩
  have hr : InvL θ k τ n ψ (rootP ψ, taut n) 0 0 :=
    ⟨⟨⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩, CountKSatRate.Tree.sideT_taut n k τ⟩, length_rootP_le ψ⟩
  refine ⟨c1, fun x hx => ?_, c4⟩
  obtain ⟨d1, d2, d3, -⟩ := c2 x hx
  obtain ⟨p', t', hx', hlen⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
  have hne : ∀ C ∈ x.1, C ≠ [] := by
    intro C hC
    obtain ⟨C', hC', hsub, hne⟩ := hx'.1.2.2.1 _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨-, b, -⟩ := hx'.1.2.1 C' hC'
    exact (List.toFinset_nonempty_iff C).1 (hne b)
  have hst : stepK θ k x.1 = none := by simpa [stepC, stepK] using d1
  exact ⟨d1, d2, fun C hC => ⟨hne C hC, d3 C hC⟩,
    fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hθ hx'.1.1 (fun C hC => ⟨hne C hC, (d3 C hC).1⟩) hst v,
    fun C hC => ⟨hx'.2.2.2.2 C hC, (hx'.2.2.1 C hC).2⟩, hlen⟩

/-- `leafM x` and `leafF x` have the same number of satisfying assignments, if every clause of the
side list is some xᵢ ∨ ¬xᵢ or has one literal. -/
theorem cntN_leafM {x : CNode} (hs : ∀ C ∈ x.2, C ∈ taut n ∨ ∃ l, C = [l]) : cntN n (leafM x) = cntN n (leafF x) := by
  rw [cntN, cntN]
  exact congrArg Finset.card (Finset.filter_congr fun σ _ => CountKSatRate.Leaf.sat_leafM_iff hs _)

/-- `out x` has the clauses of `leafM x`, so it has the same number of satisfying assignments. -/
theorem cntN_out (x : CNode) : cntN n (out x) = cntN n (leafM x) := by
  simp only [cntN, out, List.mem_dedup]

/-- A variable occurs in at most as many clauses of `out x` as of `leafM x`. -/
theorem occN_out_le (x : CNode) (v : ℕ) : occN (out x) v ≤ occN (leafM x) v :=
  ((List.dedup_sublist (leafM x)).filter _).length_le

end Gen

/-- The general theorem, from `StSide`: the facts of `Gen.withSideClauses`, moved to the tree that
starts with the empty side list. -/
theorem stGen (hSide : StSide) : StGen := by
  intro k τ n D θ β hk hτ hT hD ψ hψ
  have hB : n * τ + k * ((k - 1) * n) ≤ (n + k * ((k - 1) * n)) * τ := by
    rw [Nat.add_mul]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hτ) _
  obtain ⟨c1, c2, -⟩ := Gen.withSideClauses hτ hT hD hψ hB
  have e : leaves (stepC θ k) D (rootP ψ, taut n) = (tree θ k D ψ).map fun x => (x.1, x.2 ++ taut n) := hSide θ k D (rootP ψ) (taut n)
  rw [e] at c1 c2
  have c2' := fun x (hx : x ∈ tree θ k D ψ) => c2 _ (List.mem_map_of_mem hx)
  refine ⟨fun x hx => ?_, ?_, ?_, fun x hx => (c2' x hx).2.2.2.2.2⟩
  · have := (c2' x hx).1
    simpa [stepC] using this
  · simpa [outputs] using c1
  · intro Φ hΦ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hΦ
    obtain ⟨-, -, d3, d4, d5, -⟩ := c2' x hx
    refine ⟨fun C hC => ?_, fun v => ?_⟩
    · rcases List.mem_append.1 (List.mem_dedup.1 hC) with hC | hC
      · obtain ⟨h2, h3⟩ := CountKSatRate.Leaf.mem_sideU.1 hC
        exact ⟨fun h0 => by simp [h0] at h3, by omega, (d5 C (List.mem_append_left _ h2)).2⟩
      · exact d3 C hC
    · refine (Gen.occN_out_le x v).trans ?_
      rw [occN, leafM, occ, List.filter_append, List.length_append]
      have h1 := CountKSatRate.Leaf.length_occ_sideU_le x.2 v
      have h2 : (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j := d4 v
      rw [occ] at h1 h2
      omega

/-- What the walk of the tree needs, for all thresholds with `ThrC` and k² ≤ τ, from `StExactlyOne`,
`StCountOfExactlyOne` and `StOutputsSame`: the identity of the counts is derived from «each
satisfying assignment of the input satisfies exactly one output». -/
theorem stTreeG (hEx : StExactlyOne) (hCnt : StCountOfExactlyOne) (hOld : StOutputsSame) : StTreeG := by
  intro k τ n D θ β hk hτk hT hD ψ hψ
  have hτ : 1 ≤ τ := (Nat.one_le_pow 2 k hk).trans hτk
  have hB : n * τ + k * ((k - 1) * n) ≤ 2 * n * τ := by
    have h1 := Nat.mul_le_mul_left n hτk
    have h2 : k * ((k - 1) * n) ≤ n * k ^ 2 := by
      calc k * ((k - 1) * n) ≤ k * (k * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        _ = n * k ^ 2 := by ring
    calc n * τ + k * ((k - 1) * n) ≤ n * τ + n * τ := by omega
      _ = 2 * n * τ := by ring
  obtain ⟨c1, c2, c4⟩ := Gen.withSideClauses hτ hT hD hψ hB
  have h3 := hCnt n ψ _ fun b => hEx θ k D ψ b
  rw [← hOld θ k D n ψ, List.map_map] at h3
  have er : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
  rw [er] at h3 ⊢
  refine ⟨c1, fun x hx => ?_, ?_, c4⟩
  · obtain ⟨d1, d2, d3, d4, d5, -⟩ := c2 x hx
    exact ⟨d1, d2.trans (le_of_eq (by ring)), d3, d4, d5⟩
  · rw [h3]
    exact congrArg List.sum (List.map_congr_left fun x hx => (Gen.cntN_out x).trans (Gen.cntN_leafM fun C hC => ((c2 x hx).2.2.2.2.1 C hC).1))

end SparsificationLemma
