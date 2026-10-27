/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Function

/-! The calculus of factorisations. An interaction between two nodes is «factorised» when it is
written as a sum over
labels θ of (a factor that reads one side and θ) times (a factor that reads the other side and θ);
the number of labels is
what the pair costs. Three rules: (a) a product of factorised functions is factorised over the
tuples of labels,
(b) labels may be renamed into a larger type, (c) every function factors through its second
    argument.
Also the number of pairs a < b, and the crossing X = [x=v][y=u] of Section 4 of the paper, a
function of the four
corners of a rectangle, for indices in any type α. -/

namespace Groundwork

open Finset

variable {ι X' τ A α : Type*}

/-! ### The calculus -/

/-- Membership in the set of tuples. -/
public theorem mem_tuples [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (t : ι → X') : t ∈ tuples P T d ↔ ∀ i, (P i → t i ∈ T i) ∧ (¬P i → t i = d) := by
  unfold tuples
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]

/-- The number of tuples. -/
public theorem card_tuples [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X') :
    #(tuples P T d) = ∏ i with P i, #(T i) := by
  unfold tuples
  rw [Fintype.card_piFinset, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- Distributivity: a sum over tuples of a product is the product of the sums. -/
public theorem sum_tuples_prod [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (H : ι → X' → ℤ) : ∑ t ∈ tuples P T d, ∏ i with P i, H i (t i) = ∏ i with P i, ∑ x ∈ T i, H i x := by
  unfold tuples
  have h := Finset.prod_univ_sum (fun i => if P i then T i else {d}) (fun i x => if P i then H i x else (1 : ℤ))
  simp only [Finset.prod_filter]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi <;> simp

/-- (a), for a family: a product of factorised functions is factorised over the tuples of labels, by
the products of the
factors. -/
public theorem prod_factorised [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (f f' : ι → X' → ℤ) :
    ∏ i with P i, ∑ x ∈ T i, f i x * f' i x =
      ∑ t ∈ tuples P T d, (∏ i with P i, f i (t i)) * ∏ i with P i, f' i (t i) := by
  rw [← sum_tuples_prod P T d]
  simp only [Finset.prod_mul_distrib]

/-- (b): labels may be renamed into a larger type, both factors vanishing off the set D of names. -/
public theorem sum_renamed [Fintype A] [DecidableEq A] (D : Finset A) (dec : A → τ) (Θ : Finset τ)
    (h : Set.BijOn dec D Θ) (f f' : τ → ℤ) :
    ∑ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) = ∑ θ ∈ Θ, f θ * f' θ := by
  have h1 : ∀ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) =
      if x ∈ D then f (dec x) * f' (dec x) else 0 := by
    intro x; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_nbij dec (fun x hx => h.mapsTo hx) h.injOn h.surjOn (fun _ _ => rfl)

/-- (c): every function factors through its second argument. -/
public theorem sum_mul_eq [Fintype τ] [DecidableEq τ] (F : τ → ℤ) (z' : τ) :
    ∑ θ, F θ * (if z' = θ then 1 else 0) = F z' := by
  simp

/-! ### The number of pairs -/

/-- The ordered pairs are the pairs a < b, the pairs a > b and the diagonal. -/
private theorem two_mul_card_pairs' [Fintype α] [LinearOrder α] :
    2 * #(pairs α) + Fintype.card α = Fintype.card α * Fintype.card α := by
  have h1 : #(univ.filter fun p : α × α => p.2 < p.1) = #(pairs α) :=
    Finset.card_nbij' Prod.swap Prod.swap (by intro p; simp [pairs]) (by intro p; simp [pairs]) (by intro p; simp)
      (by intro p; simp)
  have h2 : #(univ.filter fun p : α × α => p.1 = p.2) = Fintype.card α :=
    Finset.card_nbij' Prod.fst (fun a => (a, a)) (by intro p; simp) (by intro p; simp)
      (by rintro ⟨a, b⟩ h; simp at h; simp [h]) (by intro p; simp)
  have h3 : #(univ : Finset (α × α)) = #(pairs α) + #(univ.filter fun p : α × α => p.1 = p.2) +
      #(univ.filter fun p : α × α => p.2 < p.1) := by
    rw [pairs, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1; ext p; simp; exact lt_trichotomy p.1 p.2
    · rw [Finset.disjoint_left]; intro p; simp; grind
    · rw [Finset.disjoint_left]; intro p; simp; grind
  rw [Finset.card_univ, Fintype.card_prod, h1, h2] at h3
  lia

/-- The number of pairs a < b. -/
public theorem card_pairs [Fintype α] [LinearOrder α] : #(pairs α) = (Fintype.card α).choose 2 := by
  have h := two_mul_card_pairs' (α := α)
  rw [Nat.choose_two_right]
  have h2 : Fintype.card α * (Fintype.card α - 1) = 2 * #(pairs α) := by
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | h0
    · simp [h0] at h ⊢; lia
    · obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hn] at h ⊢
      simp only [Nat.add_sub_cancel]
      grind
  rw [h2]; simp

/-! ### The crossing -/

namespace Cross

/-- X = [x=v][y=u]: opposite corners agree (the two diagonals of a rectangle with x, y on top and u,
v below). -/
@[expose] public def X [DecidableEq α] (x y u v : α) : ℤ := if x = v ∧ y = u then 1 else 0

end Cross

end Groundwork
