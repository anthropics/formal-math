/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunOne

/-!
# Automata with one input: the polynomial of degree at most `N`

Clauses on the input bits allow at most one letter at each place and ask for a letter at each place unless the end
mark came before. The monomial extension then has degree at most `N`, and below the code of a word only this
code is allowed.
-/

namespace Nc

open Finset MvPolynomial

set_option linter.unusedSectionVars false

section Valid

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}

/-- At most one letter at each place; at each place a letter, or the end mark before. -/
structure VOk (x : Fin N × Option Γ → Bool) : Prop where
  one : ∀ p y y', x (p, y) = true → x (p, y') = true → y = y'
  some : ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true

/-- The letter at a place of a word with its end mark. -/
theorem code1_le {u : List Γ} {p : Fin N} {y : Option Γ} (h : code1 N u (p, y) = true) :
    (u.map some ++ [none])[p.1]? = some y := by simpa [code1] using h

theorem code1_lt {u : List Γ} {p : Fin N} {y : Option Γ} (h : code1 N u (p, y) = true) : p.1 ≤ u.length := by
  have := (List.getElem?_eq_some_iff.1 (code1_le h)).1
  simp at this
  omega

theorem code1_none {u : List Γ} {p : Fin N} (h : code1 N u (p, none) = true) : p.1 = u.length := by
  have h1 := code1_le h
  have h2 := code1_lt h
  rcases h2.lt_or_eq with h3 | h3
  · rw [List.getElem?_append_left (by simpa using h3)] at h1
    simp at h1
  · exact h3

theorem code1_exists (u : List Γ) {p : Fin N} (h : p.1 ≤ u.length) : ∃ y, code1 N u (p, y) = true := by
  have hlt : p.1 < (u.map some ++ [none]).length := by simp; omega
  refine ⟨(u.map some ++ [none])[p.1], ?_⟩
  simp [code1, List.getElem?_eq_getElem hlt]

theorem code1_unique {u : List Γ} {p : Fin N} {y y' : Option Γ} (h : code1 N u (p, y) = true)
    (h' : code1 N u (p, y') = true) : y = y' := by
  have h1 := code1_le h
  rw [code1_le h'] at h1
  exact (Option.some.inj h1).symm

theorem vOk_code1 (u : List Γ) (hu : u.length + 1 ≤ N) : VOk (code1 N u) := by
  refine ⟨fun p y y' h h' => code1_unique h h', fun p => ?_⟩
  by_cases hp : p.1 ≤ u.length
  · exact Or.inl (code1_exists u hp)
  · refine Or.inr ⟨⟨u.length, by omega⟩, ?_, ?_⟩
    · rw [Fin.lt_def]
      simp only
      omega
    · simp [code1]

/-- Below the code of a word only this code is allowed. -/
theorem eq_code1 {x : Fin N × Option Γ → Bool} (hx : VOk x) {u : List Γ}
    (hle : ∀ b, x b = true → code1 N u b = true) : x = code1 N u := by
  funext b
  obtain ⟨p, y⟩ := b
  rcases hc : code1 N u (p, y) with _ | _
  · by_contra h
    rw [Bool.not_eq_false] at h
    rw [hle _ h] at hc
    cases hc
  · rcases hx.some p with ⟨y', hy'⟩ | ⟨p', hp', h'⟩
    · rw [code1_unique hc (hle _ hy')]
      exact hy'
    · have h1 := code1_none (hle _ h')
      have h2 := code1_lt hc
      rw [Fin.lt_def] at hp'
      omega

theorem card_ones_le {x : Fin N × Option Γ → Bool} (hx : VOk x) : #{b | x b = true} ≤ N := by
  have : #{b | x b = true} ≤ #(univ : Finset (Fin N)) := by
    refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_
    rintro ⟨p, y⟩ h ⟨p', y'⟩ h' e
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h' e
    subst e
    rw [hx.one p y y' h h']
  simpa using this

theorem card_ones_code1 (u : List Γ) (hu : u.length + 1 ≤ N) : #{b | code1 N u b = true} = u.length + 1 := by
  have : #(univ : Finset (Fin (u.length + 1))) = #{b | code1 N u b = true} := by
    refine Finset.card_bij (fun k _ => (⟨k.1, by omega⟩, (u.map some ++ [none])[k.1]'(by
      have := k.2; simp; omega))) ?_ ?_ ?_
    · intro k _
      have hlt : k.1 < (u.map some ++ [none]).length := by
        have := k.2
        simp
        omega
      simp [code1, List.getElem?_eq_getElem hlt]
    · intro k _ k' _ e
      have := congrArg (fun b => b.1.1) e
      exact Fin.ext this
    · rintro ⟨p, y⟩ h
      simp only [mem_filter, mem_univ, true_and] at h
      have h2 := code1_lt h
      have h1 := code1_le h
      refine ⟨⟨p.1, by omega⟩, mem_univ _, ?_⟩
      have hlt : p.1 < (u.map some ++ [none]).length := by simp; omega
      rw [List.getElem?_eq_getElem hlt] at h1
      simp [Option.some.inj h1]
  simpa using this.symm

end Valid

section Rules

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {n t M N : ℕ}

/-- The rules on the input bits. -/
abbrev RC (Γ : Type) (N : ℕ) : Type := (Fin N × Option Γ × Option Γ) ⊕ Fin N

/-- Their literals. -/
noncomputable def cLits : RC Γ N → List (RV Γ S Q n t M N × Bool)
  | .inl (p, y, y') => [(.inl (p, y), true), (.inl (p, y'), true)]
  | .inr p => ((univ : Finset (Option Γ)).toList.map fun y => (.inl (p, y), false)) ++
      ((univ : Finset (Fin N)).filter (· < p)).toList.map fun p' => (.inl (p', none), false)

/-- Their weights. -/
def cRWt : RC Γ N → F
  | .inl (_, y, y') => if y = y' then 1 else 0
  | .inr _ => 0

open scoped Classical in
theorem prod_valid (x : Fin N × Option Γ → Bool) (g : ∀ d, RE Γ S Q n t M d) :
    (∏ r : RC Γ N, if ∀ l ∈ cLits r, Sum.elim x (hot g) l.1 = l.2 then (cRWt r : F) else 1) =
      if VOk x then 1 else 0 := by
  rw [Fintype.prod_sum_type]
  split_ifs with hx
  · rw [Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · intro p _
      refine if_neg fun h => ?_
      rcases hx.some p with ⟨y, hy⟩ | ⟨p', hp', h'⟩
      · have := h (.inl (p, y), false) (by simp [cLits])
        simp [hy] at this
      · have := h (.inl (p', none), false) (by simp [cLits, hp'])
        simp [h'] at this
    · rintro ⟨p, y, y'⟩ _
      split_ifs with h
      · simp only [cLits, List.forall_mem_cons, Sum.elim_inl] at h
        exact if_pos (hx.one p y y' h.1 h.2.1)
      · rfl
  · have hx' : ¬ ((∀ p y y', x (p, y) = true → x (p, y') = true → y = y') ∧
        ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true) := fun h => hx ⟨h.1, h.2⟩
    by_cases h1 : ∀ p y y', x (p, y) = true → x (p, y') = true → y = y'
    · have h2 : ¬ ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true := fun h => hx' ⟨h1, h⟩
      push Not at h2
      obtain ⟨p, h3, h4⟩ := h2
      have : (∏ p : Fin N, if ∀ l ∈ cLits (S := S) (Q := Q) (n := n) (t := t) (M := M) (.inr p : RC Γ N),
          Sum.elim x (hot g) l.1 = l.2 then (cRWt (.inr p : RC Γ N) : F) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ p) ?_
        rw [if_pos]
        · rfl
        · intro l hl
          simp only [cLits, List.mem_append, List.mem_map, mem_toList, mem_univ, true_and, mem_filter] at hl
          rcases hl with ⟨y, rfl⟩ | ⟨p', hp', rfl⟩
          · simpa using h3 y
          · simpa using h4 p' hp'
      rw [this, mul_zero]
    · push Not at h1
      obtain ⟨p, y, y', h3, h4, hne⟩ := h1
      have : (∏ q : Fin N × Option Γ × Option Γ,
          if ∀ l ∈ cLits (S := S) (Q := Q) (n := n) (t := t) (M := M) (.inl q : RC Γ N),
          Sum.elim x (hot g) l.1 = l.2 then (cRWt (.inl q : RC Γ N) : F) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ (p, y, y')) ?_
        rw [if_pos]
        · exact if_neg hne
        · intro l hl
          simp only [cLits, List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · simpa using h3
          · simpa using h4
      rw [this, zero_mul]

open scoped Classical in
/-- The sum over finite domains with the clauses on the input bits. -/
theorem fdSum_valid (lits : RS Γ S Q n t ⊕ RH Γ S n t M → List (RV Γ S Q n t M N × Bool))
    (w : RS Γ S Q n t ⊕ RH Γ S n t M → F) (x : Fin N × Option Γ → Bool) :
    fdSum (Sum.elim lits cLits) (Sum.elim w (cRWt : RC Γ N → F)) x = if VOk x then fdSum lits w x else 0 := by
  rw [fdSum_elim lits w cLits cRWt x (if VOk x then 1 else 0)]
  · split_ifs <;> simp
  · intro g
    rw [← prod_valid (F := F) x g]
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases hr : ∀ l ∈ cLits r, Sum.elim x (hot g) l.1 = l.2
    · rw [if_pos hr]
      exact (if_pos hr).symm
    · rw [if_neg hr]
      exact (if_neg hr).symm

end Rules

section Monomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monomial extension along the line through a 0/1 point. -/
theorem line_mnExt (f : (ι → Bool) → F) (u : ι → Bool) :
    line (fun j => if u j then (1 : F) else 0) (mlExtC 0 f) = ∑ b : ι → Bool,
      if ∀ j, b j = true → u j = true then Polynomial.C (f b) * Polynomial.X ^ #{j | b j = true} else 0 := by
  unfold mlExtC
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ j, line (fun j => if u j then (1 : F) else 0) (if b j then X j else 1 - C 0 * X j) =
      if b j then (if u j then Polynomial.X else 0) else 1 := by
    intro j
    split_ifs <;> simp_all [line]
  have hC : line (fun j => if u j then (1 : F) else 0) (C (f b)) = Polynomial.C (f b) := by
    simp [line]
  rw [map_mul, map_prod, hC, Finset.prod_congr rfl fun j _ => h1 j]
  split_ifs with h
  · congr 1
    have h2 : ∀ j, (if b j then (if u j then (Polynomial.X : Polynomial F) else 0) else 1) =
        if b j = true then Polynomial.X else 1 := by
      intro j
      by_cases hb : b j = true
      · simp [hb, h j hb]
      · simp [hb]
    rw [Finset.prod_congr rfl fun j _ => h2 j, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  · push Not at h
    obtain ⟨j, hb, hu⟩ := h
    rw [Finset.prod_eq_zero (mem_univ j), mul_zero]
    rw [if_pos hb, if_neg hu]

/-- The degree of the monomial extension. -/
theorem totalDegree_mnExt (f : (ι → Bool) → F) {d : ℕ} (hd : ∀ b, f b ≠ 0 → #{j | b j = true} ≤ d) :
    (mlExtC 0 f).totalDegree ≤ d := by
  unfold mlExtC
  refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
  by_cases hb : f b = 0
  · rw [hb, map_zero, zero_mul, totalDegree_zero]
    exact Nat.zero_le _
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (le_trans ?_ (hd b hb))
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact (totalDegree_X j).le
    · simp

end Monomial

section Main

variable {F : Type} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

end Main

end Nc
