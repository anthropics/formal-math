/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Grid.Defs
public import Groundwork.Net.Net
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! One level of the recursion (Section 5, proof of Proposition 3): the clique on the grid. Every
edge that joins two rows and two columns is a diagonal of
exactly one rectangle, so Z is the half-edge sum ZG with the crossing at every rectangle. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

/-! ### Indicators -/

/-- Indicators of equivalent propositions are equal. -/
theorem boole_congr {P Q : Prop} {_ : Decidable P} {_ : Decidable Q} (h : P ↔ Q) :
    (if P then (1 : ℤ) else 0) = if Q then 1 else 0 := by
  simp [h]

/-- The indicator of a conjunction of three propositions is the product of their indicators. -/
theorem boole_and3 {S A B C : Prop} {_ : Decidable S} {_ : Decidable A} {_ : Decidable B} {_ : Decidable C}
    (h : S ↔ (A ∧ B) ∧ C) :
    (if S then (1 : ℤ) else 0) = (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [h, hA, hB, hC]

/-- A product of indicators is the indicator of «all of them hold». -/
theorem prod_ind {ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] {P : Prop} [Decidable P]
    (h : P ↔ ∀ i ∈ s, p i) : ∏ i ∈ s, (if p i then (1 : ℤ) else 0) = if P then 1 else 0 := by
  rw [Finset.prod_boole]
  exact boole_congr h.symm

/-! ### The edges of the grid -/

omit [Fintype α] [DecidableEq α] in
/-- The two copies of every edge agree if and only if they agree on the edges inside rows, on the
edges inside columns and on
the two diagonals of every rectangle. -/
theorem symm_iff (ℓ : Half ρ γ α) : (∀ w w', ℓ w w' = ℓ w' w) ↔
    ((∀ a, ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1)) ∧
     (∀ i, ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i))) ∧
     ∀ ω ∈ Ω ρ γ, ℓ (ω.1.1, ω.2.1) (ω.1.2, ω.2.2) = ℓ (ω.1.2, ω.2.2) (ω.1.1, ω.2.1) ∧
       ℓ (ω.1.1, ω.2.2) (ω.1.2, ω.2.1) = ℓ (ω.1.2, ω.2.1) (ω.1.1, ω.2.2) := by
  constructor
  · intro h
    exact ⟨⟨fun a q _ => h _ _, fun i p _ => h _ _⟩, fun ω _ => ⟨h _ _, h _ _⟩⟩
  · rintro ⟨⟨hr, hc⟩, hd⟩ ⟨a, i⟩ ⟨b, i'⟩
    have hr' : ∀ a i i', i < i' → ℓ (a, i) (a, i') = ℓ (a, i') (a, i) := fun a i i' h =>
      hr a (i, i') (by simp [pairs, h])
    have hc' : ∀ i a b, a < b → ℓ (a, i) (b, i) = ℓ (b, i) (a, i) := fun i a b h =>
      hc i (a, b) (by simp [pairs, h])
    have hd1 : ∀ a b i i', a < b → i < i' → ℓ (a, i) (b, i') = ℓ (b, i') (a, i) := fun a b i i' h h' =>
      (hd ((a, b), (i, i')) (by simp [Ω, h, h'])).1
    have hd2 : ∀ a b i i', a < b → i < i' → ℓ (a, i') (b, i) = ℓ (b, i) (a, i') := fun a b i i' h h' =>
      (hd ((a, b), (i, i')) (by simp [Ω, h, h'])).2
    rcases lt_trichotomy a b with h | h | h <;> rcases lt_trichotomy i i' with h' | h' | h'
    · exact hd1 _ _ _ _ h h'
    · subst h'; exact hc' _ _ _ h
    · exact hd2 _ _ _ _ h h'
    · subst h; exact hr' _ _ _ h'
    · subst h; subst h'; rfl
    · subst h; exact (hr' _ _ _ h').symm
    · exact (hd2 _ _ _ _ h h').symm
    · subst h'; exact (hc' _ _ _ h).symm
    · exact (hd1 _ _ _ _ h h').symm

omit [Fintype α] in
/-- The product of all equalities ℓ w w' = ℓ w' w is the product of those inside rows, those inside
columns, and of the
crossing over the rectangles. -/
theorem symm_eq_prod (ℓ : Half ρ γ α) : (if ∀ w w', ℓ w w' = ℓ w' w then (1 : ℤ) else 0) =
    (∏ a, ∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
    (∏ i, ∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
    ∏ ω ∈ Ω ρ γ, app Cross.X ℓ ω := by
  have h1 : ∀ a, (∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then (1 : ℤ) else 0) =
      if ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0 := fun a => prod_ind _ _ Iff.rfl
  have h2 : ∀ i, (∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then (1 : ℤ) else 0) =
      if ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0 := fun i => prod_ind _ _ Iff.rfl
  simp only [h1, h2, app, Cross.X]
  rw [prod_ind univ _ (P := ∀ a, ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1)) (by simp),
    prod_ind univ _ (P := ∀ i, ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i)) (by simp),
    prod_ind (Ω ρ γ) _ Iff.rfl]
  exact boole_and3 (symm_iff ℓ)

omit [Fintype α] [DecidableEq α] in
/-- The rectangles, sorted by pairs of rows. -/
theorem Ω_eq_product : Ω ρ γ = pairs ρ ×ˢ (univ.filter fun k : γ × γ => k.1 < k.2) := by
  ext ω; simp [Ω, pairs]

omit [Fintype α] [DecidableEq α] in
/-- A product over the rectangles, sorted by pairs of rows. (`to_additive` makes the same lemma for
sums, `sum_Ω_rows`.) -/
@[to_additive] theorem prod_Ω_rows {M : Type} [CommMonoid M] (F : Rect ρ γ → M) :
    ∏ ω ∈ Ω ρ γ, F ω = ∏ p ∈ pairs ρ, ∏ k : γ × γ with k.1 < k.2, F (p, k) := by
  rw [Ω_eq_product, Finset.prod_product]

/-! ### Z in half-edge form -/

omit [DecidableEq α] in
/-- The half-edge labellings of Inst.Z_eq_halfEdges are those with the default label at every node
itself. -/
theorem mem_halfEdges [Fintype J] [DecidableEq J] (d : α) (ℓ : J → J → α) :
    ℓ ∈ (Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset α)) d) ↔
      ∀ w, ℓ w w = d := by
  simp only [Fintype.mem_piFinset, tuples]
  constructor
  · intro h w
    simpa using h w w
  · intro h w w'
    by_cases hw : w' = w
    · subst hw; simp [h]
    · simp [hw]

/-- Z in half-edge form. -/
theorem Z_eq_symm [Fintype J] [LinearOrder J] (R : Inst J α) (d : α) :
    R.Z d = ∑ ℓ : J → J → α, (∏ w, if ℓ w w = d then R w (ℓ w) else 0) *
      (if ∀ w w', ℓ w w' = ℓ w' w then 1 else 0) := by
  rw [Inst.Z_eq_halfEdges, ← Finset.sum_subset (Finset.subset_univ
    (Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset α)) d))]
  · refine sum_congr rfl fun ℓ hℓ => ?_
    have hd := (mem_halfEdges d ℓ).1 hℓ
    congr 1
    · simp [hd]
    · refine prod_ind _ _ ⟨fun h p _ => h _ _, fun h w w' => ?_⟩
      rcases lt_trichotomy w w' with hw | hw | hw
      · exact h (w, w') (by simp [pairs, hw])
      · rw [hw]
      · exact (h (w', w) (by simp [pairs, hw])).symm
  · intro ℓ _ hℓ
    rw [mem_halfEdges] at hℓ
    push Not at hℓ
    obtain ⟨w, hw⟩ := hℓ
    rw [Finset.prod_eq_zero (mem_univ w) (by simp [hw]), zero_mul]

/-- The half-edge form on the grid. -/
theorem Z_eq_ZG_X [Fintype J] [LinearOrder J] (R : Inst J α) (d : α) (e : J ≃ ρ × γ) :
    R.Z d = ZG (onGrid R d e) (fun _ => Cross.X) := by
  rw [Z_eq_symm]
  unfold ZG
  refine Fintype.sum_equiv (e.arrowCongr (e.arrowCongr (Equiv.refl _))) _ _ fun ℓ => ?_
  rw [← symm_eq_prod]
  congr 1
  · refine Fintype.prod_equiv e _ _ fun w => ?_
    simp [onGrid, Equiv.arrowCongr, Function.comp_def]
  · refine boole_congr ⟨fun h w w' => ?_, fun h w w' => ?_⟩
    · simp [Equiv.arrowCongr, h]
    · simpa [Equiv.arrowCongr] using h (e w) (e w')

omit [Fintype α] [DecidableEq α] in
/-- The number of rectangles is C(g,2)². -/
theorem card_Ω {g : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) : #(Ω ρ γ) = g.choose 2 ^ 2 := by
  rw [Ω_eq_product, Finset.card_product]
  change #(pairs ρ) * #(pairs γ) = _
  rw [card_pairs, card_pairs, hρ, hγ, sq]

end Groundwork.Grid
