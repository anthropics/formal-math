/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.WidePerm

/-!
# Sums over functions on finite domains
-/

namespace Nc

open Finset MvPolynomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : Type*} [Fintype D] [DecidableEq D] {E : D → Type*} [∀ d, Fintype (E d)] [∀ d, DecidableEq (E d)]
variable {θ : Type*} [Fintype θ] [DecidableEq θ]

/-- The bits of a function: one for every point and value. -/
def hot (g : ∀ d, E d) (p : Σ d, E d) : Bool := decide (g p.1 = p.2)

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (E d)] in
theorem hot_injective : Function.Injective (hot (E := E)) := by
  intro g g' e
  funext d
  have := congrFun e ⟨d, g d⟩
  simp only [hot, decide_true] at this
  exact (of_decide_eq_true this.symm).symm

/-- The sum over all functions of the product over the clauses; a literal about a function is `g d = e` or its
negation. -/
def fdSum (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) (w : θ → F) (x : ι → Bool) : F :=
  ∑ g : ∀ d, E d, ∏ i, if ∀ l ∈ lits i, Sum.elim x (hot g) l.1 = l.2 then w i else 1

/-- The clauses that make bits the bits of a function. -/
noncomputable def fdLits (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) :
    θ ⊕ D ⊕ ((Σ d, E d) × (Σ d, E d)) → List ((ι ⊕ Σ d, E d) × Bool)
  | Sum.inl i => lits i
  | Sum.inr (Sum.inl d) => (univ : Finset (E d)).toList.map fun e => (Sum.inr ⟨d, e⟩, false)
  | Sum.inr (Sum.inr (p, q)) => [(Sum.inr p, true), (Sum.inr q, true)]

/-- Their weights. -/
def fdWt (w : θ → F) : θ ⊕ D ⊕ ((Σ d, E d) × (Σ d, E d)) → F
  | Sum.inl i => w i
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (p, q)) => if p.1 = q.1 ∧ p ≠ q then 0 else 1

omit [Fintype ι] [DecidableEq ι] [DecidableEq θ] in
theorem fdSum_eq (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) (w : θ → F) (x : ι → Bool) :
    fdSum lits w x = wideSum (fdLits lits) (fdWt w) x := by
  unfold fdSum wideSum
  refine Finset.sum_of_injOn hot hot_injective.injOn (fun _ _ => mem_univ _) ?_ ?_
  · intro a _ ha
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    by_cases hex : ∀ d, ∃ e, a ⟨d, e⟩ = true
    · choose g hg using hex
      have hne : a ≠ hot g := fun h => ha ⟨g, mem_univ _, h.symm⟩
      obtain ⟨⟨d, e⟩, he⟩ := Function.ne_iff.1 hne
      have hde : g d ≠ e := by
        rintro rfl
        exact he (by simp [hot, hg])
      have hat : a ⟨d, e⟩ = true := by
        simpa [hot, hde] using he
      have : (∏ q : (Σ d, E d) × (Σ d, E d),
          if ∀ l ∈ fdLits lits (Sum.inr (Sum.inr q)), Sum.elim x a l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inr q)) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ (⟨d, e⟩, ⟨d, g d⟩)) ?_
        have hpq : (⟨d, e⟩ : Σ d, E d) ≠ ⟨d, g d⟩ := by
          intro h
          exact hde (eq_of_heq (Sigma.mk.inj h).2).symm
        simp [fdLits, fdWt, hat, hg, hpq]
      rw [this, mul_zero, mul_zero]
    · push Not at hex
      obtain ⟨d, hd⟩ := hex
      have : (∏ d : D, if ∀ l ∈ fdLits lits (Sum.inr (Sum.inl d)), Sum.elim x a l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inl d)) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ d) ?_
        rw [if_pos]
        · rfl
        · intro l hl
          simp only [fdLits, List.mem_map, Finset.mem_toList, mem_univ, true_and] at hl
          obtain ⟨e, rfl⟩ := hl
          simpa using hd e
      rw [this, zero_mul, mul_zero]
  · intro g _
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    have h1 : (∏ d : D, if ∀ l ∈ fdLits lits (Sum.inr (Sum.inl d)), Sum.elim x (hot g) l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inl d)) else 1) = 1 := by
      refine Finset.prod_eq_one fun d _ => if_neg fun h => ?_
      have := h (Sum.inr ⟨d, g d⟩, false) (by simp [fdLits])
      simp [hot] at this
    have h2 : (∏ q : (Σ d, E d) × (Σ d, E d),
          if ∀ l ∈ fdLits lits (Sum.inr (Sum.inr q)), Sum.elim x (hot g) l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inr q)) else 1) = 1 := by
      refine Finset.prod_eq_one ?_
      rintro ⟨⟨d, e⟩, ⟨d', e'⟩⟩ _
      split_ifs with h
      · simp only [fdLits, List.forall_mem_cons, Sum.elim_inr, hot, decide_eq_true_eq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        simp only [fdWt]
        refine if_neg ?_
        rintro ⟨hd, hne⟩
        subst hd
        exact hne rfl
      · rfl
    rw [h1, h2, mul_one, mul_one]
    rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq θ] in
/-- Clauses whose product does not depend on the function. -/
theorem fdSum_elim {θ' : Type*} [Fintype θ'] (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) (w : θ → F)
    (lits' : θ' → List ((ι ⊕ Σ d, E d) × Bool)) (w' : θ' → F) (x : ι → Bool) (c : F)
    (h : ∀ g : ∀ d, E d, (∏ i, if ∀ l ∈ lits' i, Sum.elim x (hot g) l.1 = l.2 then w' i else 1) = c) :
    fdSum (Sum.elim lits lits') (Sum.elim w w') x = fdSum lits w x * c := by
  unfold fdSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.prod_sum_type, ← h g]
  rfl

section Proj

variable {F ι D θ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] {E : D → Type}
  [∀ d, Fintype (E d)] [∀ d, DecidableEq (E d)] [Fintype θ] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {κ : ℕ}

end Proj

end Nc
