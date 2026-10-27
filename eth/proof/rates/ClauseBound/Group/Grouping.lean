/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Group.Sample

/-! # Groupings as permutations of one fixed grouping: lemmas for case (ii) of Lemma 8

Lemmas for a proof of case (ii) of Lemma 8 by counting instead of probability. The paper takes a
uniformly random grouping with groups of g/K nodes, n nodes here. Here the groupings are χ₀∘e, where
χ₀ is one fixed grouping with
groups of n nodes and e runs over all permutations of the nodes; every such grouping arises from the
same number of permutations, but this is not needed. What is needed: the group number γ of
χ₀∘e is each set of n nodes for the same number of e (`fiber_le`), and among the e for which it is a
given set A, the group number γ' is each set of n nodes outside A for the same number of
e. Both follow from the fact that a permutation of the nodes carries one such configuration to the
other (`exists_perm_sets`). So the fraction of the e with a property of the group is the
fraction of the sets of n nodes with that property (`card_filter_le_of_fibers`), which Hoeffding's
inequality for sampling without replacement bounds. -/

public section

namespace ClauseBound.Group

open Finset

namespace Grouping

/-! ### Permutations that carry one configuration of sets to another -/

/-- Two colourings with classes of the same sizes differ by a permutation. -/
theorem exists_perm_of_fiber {V C : Type} [Fintype V] [DecidableEq C] (α β : V → C) (h : ∀ y, #{x | α x = y} = #{x | β x = y}) :
    ∃ p : Equiv.Perm V, ∀ x, β (p x) = α x := by
  have hy : ∀ y, Nonempty ({x // α x = y} ≃ {x // β x = y}) := fun y =>
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h y)⟩
  refine ⟨(Equiv.sigmaFiberEquiv α).symm.trans ((Equiv.sigmaCongrRight fun y => (hy y).some).trans (Equiv.sigmaFiberEquiv β)), fun x => ?_⟩
  exact ((hy (α x)).some ⟨x, rfl⟩).2

/-- The sizes of the four classes of the colouring by membership in two disjoint sets. -/
theorem card_colour {V : Type} [Fintype V] [DecidableEq V] (A B : Finset V) (h : Disjoint A B) (y : Bool × Bool) :
    #{x | (decide (x ∈ A), decide (x ∈ B)) = y} =
      if y.1 = true then (if y.2 = true then 0 else #A) else (if y.2 = true then #B else Fintype.card V - (#A + #B)) := by
  obtain ⟨y1, y2⟩ := y
  cases y1 <;> cases y2 <;> simp only [Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq_true, if_false, if_true]
  · rw [← card_union_of_disjoint h, ← card_compl]
    congr 1
    ext x; simp
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hx => hx.2, fun hx => ⟨fun hA => disjoint_left.1 h hA hx, hx⟩⟩
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, disjoint_left.1 h hx⟩⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun x _ hx => disjoint_left.1 h hx.1 hx.2

/-- A permutation that keeps the set A and carries A'' to A', two sets of the same size that are
disjoint from A. -/
theorem exists_perm_sets {V : Type} [Fintype V] [DecidableEq V] (A A' A'' : Finset V) (h' : Disjoint A A') (h'' : Disjoint A A'') (hc : #A' = #A'') :
    ∃ p : Equiv.Perm V, (∀ x, p x ∈ A ↔ x ∈ A) ∧ ∀ x, p x ∈ A' ↔ x ∈ A'' := by
  obtain ⟨p, hp⟩ := exists_perm_of_fiber (fun x => (decide (x ∈ A), decide (x ∈ A''))) (fun x => (decide (x ∈ A), decide (x ∈ A')))
    fun y => by rw [card_colour A A'' h'', card_colour A A' h', hc]
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · have := congrArg Prod.fst (hp x)
    simpa using this
  · have := congrArg Prod.snd (hp x)
    simpa using this

/-! ### Counting through a map with fibres of one size -/

/-- If all fibres of F over Xs have the same size, the fraction of Ω' on which F has a property is
the fraction of Xs with that property. -/
theorem card_filter_le_of_fibers {Ω X : Type} [DecidableEq X] (Ω' : Finset Ω) (F : Ω → X) (Xs : Finset X) (hF : ∀ e ∈ Ω', F e ∈ Xs)
    (hconst : ∀ x ∈ Xs, ∀ x' ∈ Xs, #{e ∈ Ω' | F e = x} ≤ #{e ∈ Ω' | F e = x'}) (Q : X → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : (#{x ∈ Xs | Q x} : ℝ) ≤ ε * #Xs) : (#{e ∈ Ω' | Q (F e)} : ℝ) ≤ ε * #Ω' := by
  rcases Xs.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have : Ω' = ∅ := eq_empty_iff_forall_notMem.2 fun e he => by simpa using hF e he
    subst this
    simp
  · have hf : ∀ x ∈ Xs, #{e ∈ Ω' | F e = x} = #{e ∈ Ω' | F e = x₀} := fun x hx => le_antisymm (hconst x hx x₀ hx₀) (hconst x₀ hx₀ x hx)
    have h1 : #Ω' = #Xs * #{e ∈ Ω' | F e = x₀} := by
      rw [card_eq_sum_card_fiberwise (f := F) (t := Xs) (fun e he => hF e he), sum_congr rfl hf, sum_const, smul_eq_mul]
    have h2 : #{e ∈ Ω' | Q (F e)} = #{x ∈ Xs | Q x} * #{e ∈ Ω' | F e = x₀} := by
      rw [card_eq_sum_card_fiberwise (f := F) (t := {x ∈ Xs | Q x})
        (fun e he => mem_coe.2 (mem_filter.2 ⟨hF e (mem_filter.1 (mem_coe.1 he)).1, (mem_filter.1 (mem_coe.1 he)).2⟩)), ← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun x hx => ?_
      rw [← hf x (mem_filter.1 hx).1, filter_filter]
      congr 1
      refine filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨h ▸ (mem_filter.1 hx).2, h⟩⟩
    rw [h1, h2]
    push_cast
    calc (#{x ∈ Xs | Q x} : ℝ) * #{e ∈ Ω' | F e = x₀} ≤ ε * #Xs * #{e ∈ Ω' | F e = x₀} := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg _)
      _ = ε * (#Xs * #{e ∈ Ω' | F e = x₀}) := by ring

/-! ### The groupings -/

variable {K n : ℕ}

/-- One grouping with groups of n nodes. -/
def chi0 (a : Fin (K * n)) : Fin K := (finProdFinEquiv.symm a).1

/-- The group number γ of the grouping χ₀∘e. -/
def cls (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : Finset (Fin (K * n)) := {a | chi0 (e a) = γ}

theorem mem_cls {e : Equiv.Perm (Fin (K * n))} {γ : Fin K} {a : Fin (K * n)} : a ∈ cls e γ ↔ chi0 (e a) = γ := by simp [cls]

/-- Every group has n nodes. -/
theorem card_cls (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : #(cls e γ) = n := by
  have h : cls e γ = (({γ} : Finset (Fin K)) ×ˢ (univ : Finset (Fin n))).map (finProdFinEquiv.trans e.symm).toEmbedding := by
    ext a
    simp only [mem_cls, chi0, mem_map, mem_product, mem_singleton, mem_univ, and_true, Equiv.coe_toEmbedding, Equiv.trans_apply]
    constructor
    · intro h
      exact ⟨finProdFinEquiv.symm (e a), h, by rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
  rw [h, card_map, card_product, card_singleton, card_univ, Fintype.card_fin, Nat.one_mul]

/-- Different groups are disjoint. -/
theorem disjoint_cls (e : Equiv.Perm (Fin (K * n))) {γ γ' : Fin K} (h : γ ≠ γ') : Disjoint (cls e γ) (cls e γ') :=
  disjoint_left.2 fun _ h1 h2 => h ((mem_cls.1 h1).symm.trans (mem_cls.1 h2))

/-- The groups of χ₀∘e∘p are the preimages under p of the groups of χ₀∘e. -/
theorem mem_cls_mul {e p : Equiv.Perm (Fin (K * n))} {γ : Fin K} {a : Fin (K * n)} : a ∈ cls (e * p) γ ↔ p a ∈ cls e γ := by
  rw [mem_cls, mem_cls, Equiv.Perm.mul_apply]

/-- If p carries A'' to A' and multiplication by p keeps Ω', then the group number γ' is A'' at
least as often on Ω' as it is A'. -/
theorem fiber_le (Ω' : Finset (Equiv.Perm (Fin (K * n)))) (p : Equiv.Perm (Fin (K * n))) (hΩ : ∀ e ∈ Ω', e * p ∈ Ω') (γ' : Fin K)
    (A' A'' : Finset (Fin (K * n))) (hp : ∀ x, p x ∈ A' ↔ x ∈ A'') : #{e ∈ Ω' | cls e γ' = A'} ≤ #{e ∈ Ω' | cls e γ' = A''} := by
  refine card_le_card_of_injOn (fun e => e * p) (fun e he => ?_) fun e _ e' _ h => mul_right_cancel h
  obtain ⟨h1, h2⟩ := mem_filter.1 (mem_coe.1 he)
  refine mem_coe.2 (mem_filter.2 ⟨hΩ e h1, ?_⟩)
  ext a
  rw [mem_cls_mul, h2, hp]

end Grouping

open Grouping

end ClauseBound.Group
