/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces
public import CountKSat.ProgC
public import CountKSat.StepCount
public import CountKSat.Walk
import all PaddedDescent.F.MarkDeg
import Mathlib.Tactic.Ring

/-! # The sparsification lemma for counting at width k, with a short side list

This file proves `StTreeK`, one of the interface statements of
proof/consequences/CountKSatRate/Interfaces.lean. It says of the tree of `stepC (theta τ) k` what
`StProgC` of
proof/consequences/CountKSat/Interfaces.lean says, with a sharper bound on the side list: at most 2n
clauses if τ ≥ k². Only the step to a heavy child (the child that gets the petals,
proof/consequences/CountKSat/Defs.lean) lengthens the
side list, by at most k clauses, and it adds q units to the counter t of the invariant `GC` of
proof/consequences/CountKSat/ProgC.lean. So (length of the side list)·q ≤ n·q + k·t holds at every
node. Here q = τ and t ≤ kn.
The file follows proof/consequences/CountKSat/ProgC.lean, with this bound in place of the bound by
the number of steps, and uses its lemmas on hearts and on the clauses xᵢ ∨ ¬xᵢ.
`StTreeK` also says what `PaddedDescent.F.StCountM` asks of a formula. The formula part x.1 of a
leaf, without its side list, has no empty clause and every variable occurs in at most leafC τ k of
its
clauses; this is `length_occ_le_of_none` of proof/rates/PaddedDescent/F/MarkDeg.lean, and the proof
follows `leaf_spec` there. Every clause of a side list is some xᵢ ∨ ¬xᵢ or has one literal. -/

@[expose] public section

namespace CountKSatRate

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)

namespace Tree

variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

/-- What holds of the side list X when the heavy steps so far have used t units, q each: |X|·q ≤ n·q +
k·t, every clause has at most 2 literals on variables
below n, all clauses xᵢ ∨ ¬xᵢ are there, and every other clause has exactly one literal. -/
def SideT (n k q : ℕ) (X : PFml) (t : ℕ) : Prop :=
  X.length * q ≤ n * q + k * t ∧ (∀ C ∈ X, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ C ∈ taut n, C ∈ X) ∧ ∀ C ∈ X, C ∈ taut n ∨ ∃ l, C = [l]

/-- The invariant of the counting tree: the invariant of
proof/sparsification/SparsifyWidthK/ProgMain.lean for the formula, and `SideT` for the side list. -/
def GT (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) (ψ : PFml) (n k q : ℕ) (x : CNode) (p t : ℕ) : Prop :=
  WidthK.ProgMain.G Node ψ x.1 p t ∧ SideT n k q x.2 t

/-- Both children of a node satisfy the invariant after one more step; at the heavy child the second
counter grows by q. -/
theorem GT_step (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} (ψ : PFml)
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (x : CNode) (p t : ℕ) (l h : CNode) (hG : GT Node ψ n k q x p t)
    (hst : stepC θ k x = some (l, h)) : GT Node ψ n k q l (p + 1) t ∧ GT Node ψ n k q h (p + 1) (t + q) := by
  obtain ⟨H, P, hp, rfl, rfl⟩ := ProgC.stepC_some hst
  obtain ⟨hHk, hHn⟩ := ProgC.pick_spec hθ hI hR hψ hG.1 hp
  obtain ⟨g1, g2⟩ := WidthK.ProgMain.G_step hI hR ψ x.1 p t (addP [H] x.1) (addP P x.1) hG.1 (by simp [stepK, hp])
  obtain ⟨s1, s2, s3, s4⟩ := hG.2
  refine ⟨⟨g1, s1, s2, s3, s4⟩, ⟨g2, ?_, ?_, ?_, ?_⟩⟩
  · show (negU H ++ x.2).length * q ≤ n * q + k * (t + q)
    rw [List.length_append, negU, List.length_map, Nat.add_mul, Nat.mul_add]
    have := Nat.mul_le_mul_right q hHk
    omega
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hC
      refine ⟨by simp, fun b hb => ?_⟩
      obtain rfl : b = (a.1, !a.2) := by simpa using hb
      exact hHn a ha
    · exact s2 C hC
  · exact fun C hC => List.mem_append_right _ (s3 C hC)
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hC
      exact Or.inr ⟨_, rfl⟩
    · exact s4 C hC

/-- The side list of the root satisfies `SideT` with no unit used. -/
theorem sideT_taut (n k q : ℕ) : SideT n k q (taut n) 0 :=
  ⟨by rw [ProgC.length_taut]; omega, (ProgC.sideOK_taut n k).2.1, fun _ hC => hC, fun _ hC => Or.inl hC⟩

/-- The sparsification lemma for counting with the side list bounded by B, for any thresholds and
bounds that satisfy `Iface` and `Refines`. Every leaf satisfies the invariant. -/
theorem tree_of (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) (hθ : ∀ i, 1 ≤ θ i) {n : ℕ} (hI : Iface θ k D T q leafB Ok Node)
    (hR : Refines θ k) {hv B : ℕ} (hT : T < (hv + 1) * q) (hB : n * q + k * T ≤ B * q) (ψ : PFml) (hOk : Ok (toFin ψ))
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n), stepC θ k x = none ∧ (leafF x).length ≤ leafB + B ∧
      (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∃ p t, GT Node ψ n k q x p t) ∧
    cntN n ψ = ((leaves (stepC θ k) D (rootP ψ, taut n)).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1, x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ B ∧
        (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at hT
    · exact h
  have hb : ∀ s p t, GT Node ψ n k q s p t → p ≤ D ∧ t ≤ T := fun s p t h => hI.bound _ _ _ _ h.1.2
  have hs := GT_step hθ hI hR ψ hψ
  have hr : GT Node ψ n k q (rootP ψ, taut n) 0 0 :=
    ⟨⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩, sideT_taut n k q⟩
  have hnone := step_eq_none_of_mem_leaves hb hs D (rootP ψ, taut n) 0 0 hr (by omega)
  have hk0 : ∀ C ∈ toFin ψ, C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    exact (List.toFinset_card_le C).trans (hψ C hC).1
  have hcl : ∀ x p t, GT Node ψ n k q x p t → ∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n :=
    fun x p t hx C hC => ProgC.clause_of_G hI hψ hx.1 C hC
  have hside : ∀ x p t, GT Node ψ n k q x p t → x.2.length ≤ B := by
    intro x p t hx
    refine Nat.le_of_mul_le_mul_right ((hx.2.1.trans ?_).trans hB) hq
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hb x p t hx).2) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_leaves_le hb hs _ _ _ _ 0 0 hr (by omega) (by omega)
  · intro x hx
    obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
    refine ⟨hnone x hx, ?_, hcl x p' t' hx', p', t', hx'⟩
    · have h1 : x.1.length ≤ leafB := by
        rw [WidthK.ProgMain.nf_length_eq hx'.1.1]
        refine hI.leaf _ _ _ _ hx'.1.2 (hR.none x.1 hx'.1.1 ?_)
        have := hnone x hx
        simpa [stepC] using this
      have h2 := hside x p' t' hx'
      rw [leafF, List.length_append]
      omega
  · have e : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
    rw [← hRC n ψ, e]
    exact hSL _ _ _ _ hs (fun x => cntN n (leafF x)) (fun s _ _ l h _ hst => hSC θ k n s l h hst) D (rootP ψ, taut n) 0 0 hr
  · intro i
    obtain ⟨h1, h2⟩ := stack_bound hb hs (rootP ψ, taut n) 0 0 hr i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hx'⟩ := h2 x hx
    refine ⟨?_, hside x p' t' hx', hcl x p' t' hx', hx'.2.2.1⟩
    rw [WidthK.ProgMain.nf_length_eq hx'.1.1]
    refine (WidthK.ProgMain.card_le_of_clause hk0 (hI.clause _ _ _ _ hx'.1.2)).trans (Nat.mul_le_mul_right _ ?_)
    rw [toFin]
    exact (List.toFinset_card_le _).trans (by simp)

end Tree

/-- The sparsification lemma for counting at width k with a side list of at most 2n clauses: the
interface statement `StTreeK`. -/
theorem stTreeK : StTreeK := by
  intro k τ n hk hτk ψ hψ
  have hτ : 1 ≤ τ := (Nat.one_le_pow 2 k hk).trans hτk
  have hθ : ∀ i, 1 ≤ theta τ i := (WidthK.stThr τ hτ).pos
  have hI := WidthK.ProgMain.iface WidthK.stNodeRoot WidthK.stNodeStep WidthK.stNodeBound WidthK.stLeafCard WidthK.stLightEq
    WidthK.stHeavyEq WidthK.stSatIff WidthK.stThr WidthK.stBetaSum hτ k n
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
  obtain ⟨c1, c2, c3, c4⟩ := Tree.tree_of stStepCount stRootCount stSumLeaves hθ hI (WidthK.Refine.stRefines _ k hθ) hT hB ψ hOk
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
  have hst : stepK (theta τ) k x.1 = none := by simpa [stepC, stepK] using d1
  exact ⟨d1, d2.trans (le_of_eq (by ring)), fun C hC => ⟨hne C hC, d3 C hC⟩,
    fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hθ hx'.1.1 (fun C hC => ⟨hne C hC, (d3 C hC).1⟩) hst v,
    fun C hC => ⟨hx'.2.2.2.2 C hC, (hx'.2.2.1 C hC).2⟩⟩

end CountKSatRate
