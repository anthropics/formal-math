/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
import SparsifyWidthK.ProgMain
import all SparsifyWidthK.Refine
import Mathlib.Tactic.Tauto

/-! # Counting along the tree: the count at a node is the sum of the counts at its two children

This file proves two of the interface statements of `proof/consequences/CountKSat/Interfaces.lean`
(the names `St…`): `StStepCount` and `StRootCount`.
A node is a pair (s, X) of the formula s that the branching rule looks at and a side list X; what is
counted at it is `leafF`, the formula X ++ s.

* `cntN_split`: let every petal Q ∈ P come from a clause C of s whose literals all lie in the heart
  H or in Q. Then the assignments that satisfy X ++ s are
  those that satisfy the light child (they make H true) and those that satisfy the heavy child
  together with «every literal of H is false», and no
  assignment does both. This is the idea of Dell, Husfeldt, Marx, Taslaman and Wahlén (arXiv 1206.1775,
  Appendix A).
* `cntN_step`: the same for one step of the program `stepC`. It needs no hypothesis on the node.
* `cntN_root`: the root has the count of the formula it was made from.

The proofs work on lists. The key fact is `holds_addP`: `addP A s` holds exactly if A and s hold. -/

namespace CountKSat

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog

namespace StepCount

/-- The truth values v make a literal of every clause of x true. -/
def Holds (v : PLit → Prop) (x : PFml) : Prop := ∀ C ∈ x, ∃ l ∈ C, v l

/-- A formula in two parts holds exactly if both parts hold. -/
theorem holds_append (v : PLit → Prop) (x y : PFml) : Holds v (x ++ y) ↔ Holds v x ∧ Holds v y := by
  simp only [Holds, List.mem_append]
  exact ⟨fun h => ⟨fun C hC => h C (Or.inl hC), fun C hC => h C (Or.inr hC)⟩, fun h C hC => hC.elim (h.1 C) (h.2 C)⟩

/-- `addP A s` holds exactly if A and s hold: a clause that `addP` drops contains a clause of A. -/
theorem holds_addP (v : PLit → Prop) (A s : PFml) : Holds v (addP A s) ↔ Holds v A ∧ Holds v s := by
  rw [addP, holds_append]
  refine and_congr_right fun hA => ⟨fun h C hC => ?_, fun h C hC => h C (List.mem_filter.1 hC).1⟩
  by_cases hd : (A.any fun D => subP D C) = true
  · obtain ⟨D, hD, hDC⟩ := List.any_eq_true.1 hd
    obtain ⟨l, hl, hv⟩ := hA D hD
    have hsub : ∀ a ∈ D, a ∈ C := by simpa [subP] using hDC
    exact ⟨l, hsub l hl, hv⟩
  · exact h C (List.mem_filter.2 ⟨hC, by simpa using hd⟩)

/-- A formula with the one clause H holds exactly if a literal of H is true. -/
theorem holds_singleton (v : PLit → Prop) (H : PCl) : Holds v [H] ↔ ∃ l ∈ H, v l := by simp [Holds]

/-- The unit clauses `negU H` hold under an assignment b exactly if b makes no literal of H true. -/
theorem holds_negU (b : ℕ → Bool) (H : PCl) : Holds (fun l => b l.1 = l.2) (negU H) ↔ ¬ ∃ l ∈ H, b l.1 = l.2 := by
  simp only [Holds, negU, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.mem_singleton, exists_eq_left,
    not_exists, not_and]
  refine forall₂_congr fun l _ => ?_
  cases b l.1 <;> cases l.2 <;> simp

/-- If no literal of the heart H is true and s holds, then the petals hold. -/
theorem holds_petals {v : PLit → Prop} {s P : PFml} {H : PCl} (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q)
    (hH : ¬ ∃ l ∈ H, v l) (hs : Holds v s) : Holds v P := by
  intro Q hQ
  obtain ⟨C, hC, hCQ⟩ := hP Q hQ
  obtain ⟨l, hl, hv⟩ := hs C hC
  rcases hCQ l hl with h | h
  · exact absurd ⟨l, h, hv⟩ hH
  · exact ⟨l, h, hv⟩

/-- If L means «P and Q» and R means «P and not Q», then the number of a with P a is the sum of the
numbers for L and for R. -/
theorem card_split {ι : Type} [Fintype ι] (P Q L R : ι → Prop) [DecidablePred P] [DecidablePred L] [DecidablePred R]
    (hL : ∀ a, L a ↔ P a ∧ Q a) (hR : ∀ a, R a ↔ P a ∧ ¬ Q a) :
    (univ.filter P).card = (univ.filter L).card + (univ.filter R).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_union, hL, hR]
    tauto
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_filter, mem_univ, true_and, hL, hR] at ha hb
    exact hb.2 ha.2

/-- Every petal Q that `pickK` returns comes from a clause of s whose literals lie in the heart or
in Q. -/
theorem pickK_petals {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {H : PCl} {P : PFml} (h : pickK θ k s = some (H, P)) :
    ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q := by
  have hmem : (H, P) ∈ (pairsK k).filterMap (tryP θ k s) := List.mem_of_head? h
  obtain ⟨jh, -, htry⟩ := List.mem_filterMap.1 hmem
  obtain ⟨H', -, he⟩ := Option.map_eq_some_iff.1 htry
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  intro Q hQ
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hQ
  refine ⟨C, (List.mem_filter.1 hC).1, fun l hl => ?_⟩
  by_cases hlH : l ∈ H'
  · exact Or.inl hlH
  · exact Or.inr (List.mem_filter.2 ⟨hl, by simpa using hlH⟩)

end StepCount

open StepCount

/-- The count of X ++ s is the count of the light child (H added) plus the count of the heavy child
(P added) with «H is false» on the side list. -/
public theorem cntN_split (n : ℕ) (X s : PFml) (H : PCl) (P : PFml) (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q) :
    cntN n (X ++ s) = cntN n (X ++ addP [H] s) + cntN n ((negU H ++ X) ++ addP P s) := by
  refine card_split _ (fun a : Fin n → Bool => ∃ l ∈ H, ext a l.1 = l.2) _ _ (fun a => ?_) (fun a => ?_)
  · change Holds _ _ ↔ Holds _ _ ∧ _
    rw [holds_append, holds_append, holds_addP, holds_singleton]
    tauto
  · change Holds _ _ ↔ Holds _ _ ∧ _
    rw [holds_append, holds_append, holds_append, holds_addP, holds_negU]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h4⟩; exact ⟨⟨h2, h4⟩, h1⟩
    · rintro ⟨⟨h2, h4⟩, h1⟩; exact ⟨⟨h1, h2⟩, holds_petals hP h1 h4, h4⟩

/-- The count at a node is the sum of the counts at its two children. -/
public theorem cntN_step {θ : ℕ → ℕ} {k : ℕ} (n : ℕ) {x l h : CNode} (hst : stepC θ k x = some (l, h)) :
    cntN n (leafF x) = cntN n (leafF l) + cntN n (leafF h) := by
  obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact cntN_split n x.2 x.1 H P (pickK_petals hp)

/-- The count at the root of the tree of ψ is the count of ψ. -/
public theorem cntN_root (n : ℕ) (ψ : Fml) : cntN n (leafF (rootC (List.replicate n (), ψ))) = cntN n ψ := by
  unfold cntN
  congr 1
  refine Finset.filter_congr fun a _ => ?_
  change Holds _ _ ↔ Holds _ _
  rw [leafF, rootC, holds_append]
  have h1 : Holds (fun l : PLit => ext a l.1 = l.2) (taut (List.replicate n ()).length) := by
    intro C hC
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
    cases hb : ext a i
    · exact ⟨(i, false), by simp, hb⟩
    · exact ⟨(i, true), by simp, hb⟩
  have h2 : Holds (fun l : PLit => ext a l.1 = l.2) (rootP ψ) ↔ Holds (fun l : PLit => ext a l.1 = l.2) ψ := by
    unfold Holds
    rw [← ProgMain.sat_toFin, ← ProgMain.sat_toFin, Refine.toFin_rootP, sat_red]
  exact ⟨fun h => h2.1 h.2, fun h => ⟨h1, h2.2 h⟩⟩

/-! ### The interface statements of `proof/consequences/CountKSat/Interfaces.lean` proved by this file -/

/-- `cntN_step`, in the form of the interface. -/
public theorem stStepCount : StStepCount := fun _ _ n _ _ _ hst => cntN_step n hst

/-- `cntN_root`, in the form of the interface. -/
public theorem stRootCount : StRootCount := cntN_root

end CountKSat
