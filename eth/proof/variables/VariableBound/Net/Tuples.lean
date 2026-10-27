/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import VariableBound.Net.Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD

/-! # Step 3: sets of marked objects and tuples (Π₀, …, Π_r)

Step 3: «So the term is given by ξ and the sets Π₀ and Π_j of the clauses E for which E,
respectively (E, j), is marked; … Π₀ ⊆ V(ξ) and Π_j ⊆ V_j(ξ)».

A set P of positions of objects is cut into the sets `sl D 0 0 P` = Π₀ (the clauses E that are
members of P) and `sl D 1 j P` = Π_j (the clauses E whose incidence (E, j) is a member of P); `back`
puts a tuple together
again. For a fixed ξ this is a bijection between the sets P of objects with violated clauses and the
tuples with Π₀ ⊆ V(ξ) and Π_j ⊆ V_j(ξ); it keeps the numbers |Π₀|, |Π_j|, and hence the limits and
the value of the term
(`sum_sets`). Summed over ξ this is `stTuples`. `stChks`: for well-formed data, the list of checks
as sets has the numbers r, |Λ_j| and load(E) of the list of checks as lists. -/

namespace VariableBound.Net.Tuples

open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)

variable {k n : ℕ} {D : Dat}

/-! ### The list of checks as sets -/

/-- A clause is in the set of a list of numbers iff its number is in the list. -/
theorem mem_setD {m : ℕ} {l : List ℕ} {e : Fin m} : e ∈ Fld.setD m l ↔ e.val ∈ l := by
  simp [Fld.setD]

/-- The set of a list without repetition of numbers below m has as many members as the list. -/
theorem card_setD {m : ℕ} {l : List ℕ} (hn : l.Nodup) (hl : ∀ e ∈ l, e < m) : #(Fld.setD m l) = l.length := by
  rw [← List.toFinset_card_of_nodup hn, ← Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext x
  simp only [mem_image, mem_setD, List.mem_toFinset]
  exact ⟨fun ⟨e, he, hx⟩ => hx ▸ he, fun hx => ⟨⟨x, hl x hx⟩, hx, rfl⟩⟩

/-- Check number j as a set is the set of check number j as a list. -/
theorem getD_chks (D : Dat) (j : ℕ) : (chks D).getD j ∅ = Fld.setD D.1.length (D.2.getD j []) := by
  have h0 : (∅ : Finset (Fin D.1.length)) = Fld.setD D.1.length [] := by simp [Fld.setD]
  rw [chks, chksD, h0, List.getD_map]

/-- The list of sets has r members. -/
theorem length_chks (D : Dat) : (chks D).length = D.2.length := by
  simp [chks, chksD]

/-- For well-formed data D (a formula Φ and a list of checks given as lists of clause numbers), the
list of sets has the numbers of the list of lists: r, |Λ_j| and load(E). -/
public theorem stChks : StChks := by
  intro k n D hW
  refine ⟨length_chks D, fun j => ?_, fun e => ?_⟩
  · rw [getD_chks]
    by_cases hj : j < D.2.length
    · exact card_setD (hW.2 _ (getD_mem hj)).1 (hW.2 _ (getD_mem hj)).2
    · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
      simp [Fld.setD]
  · rw [AppVariables.load, colD, chks, chksD, List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun l _ => ?_
    simp [mem_setD]

/-! ### Cutting a set of objects into a tuple, and back -/

open Classical in
/-- The clauses E such that the object (κ, E, j) is a member of P: Π₀ for (κ, j) = (0, 0), Π_j for κ = 1. -/
noncomputable def sl (D : Dat) (κ j : ℕ) (P : Finset ℕ) : Finset (Fin D.1.length) := univ.filter fun e => ∃ o ∈ P, obAt D o = (κ, e.val, j)

open Classical in
/-- The set of the objects E with E ∈ S₀ and (E, j) with E ∈ S j. -/
noncomputable def back (D : Dat) {r : ℕ} (S₀ : Finset (Fin D.1.length)) (S : Fin r → Finset (Fin D.1.length)) : Finset ℕ :=
  (range (objs D).length).filter fun o => (∃ e ∈ S₀, obAt D o = (0, e.val, 0)) ∨ ∃ j, ∃ e ∈ S j, obAt D o = (1, e.val, j.val)

/-- E is in the part (κ, j) of P iff the object (κ, E, j) is a member of P. -/
theorem mem_sl {κ j : ℕ} {P : Finset ℕ} {e : Fin D.1.length} : e ∈ sl D κ j P ↔ ∃ o ∈ P, obAt D o = (κ, e.val, j) := by
  simp [sl]

/-- The members of the set put together from (S₀, S) are the objects E with E ∈ S₀ and (E, j) with E
∈ S j. -/
theorem mem_back {r : ℕ} {S₀ : Finset (Fin D.1.length)} {S : Fin r → Finset (Fin D.1.length)} {o : ℕ} :
    o ∈ back D S₀ S ↔ o < (objs D).length ∧ ((∃ e ∈ S₀, obAt D o = (0, e.val, 0)) ∨ ∃ j, ∃ e ∈ S j, obAt D o = (1, e.val, j.val)) := by
  simp [back]

/-- An object of kind 0 is a triple (0, e, 0): the third entry of an object o (a place below the
number of objects) of kind 0 is 0. -/
theorem third_zero {o : ℕ} (h : o < (objs D).length) (h0 : (obAt D o).1 = 0) : (obAt D o).2.2 = 0 := by
  rcases mem_objs.1 (obAt_mem h) with h' | h'
  · exact h'.2.2
  · omega

/-- For well-formed data and a set P of positions of objects: there are as many clauses E with (κ,
E, j) in P as members of P of kind κ with third entry j. -/
theorem card_sl (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ j : ℕ) :
    #(sl D κ j P) = #(P.filter fun o => (obAt D o).1 = κ ∧ (obAt D o).2.2 = j) := by
  symm
  refine Finset.card_bij (fun o ho => ⟨(obAt D o).2.1, cl_lt hW (mem_range.1 (hP (mem_filter.1 ho).1))⟩) ?_ ?_ ?_
  · intro o ho
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 ho
    exact mem_sl.2 ⟨o, h1, Prod.ext h2 (Prod.ext rfl h3)⟩
  · intro o ho o' ho' he
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 ho
    obtain ⟨h1', h2', h3'⟩ := mem_filter.1 ho'
    exact obAt_inj hW (mem_range.1 (hP h1)) (mem_range.1 (hP h1')) (Prod.ext (h2.trans h2'.symm) (Prod.ext (Fin.mk.inj he) (h3.trans h3'.symm)))
  · intro e he
    obtain ⟨o, ho, hx⟩ := mem_sl.1 he
    exact ⟨o, mem_filter.2 ⟨ho, by rw [hx], by rw [hx]⟩, Fin.ext (by simp [hx])⟩

/-- |Π₀| is the number of members of P of kind 0, for well-formed data (WfD) and a set P of places
of objects. -/
theorem card_kP_zero (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) : #(kP D P 0) = #(sl D 0 0 P) := by
  rw [card_sl hW hP, kP]
  congr 1
  refine filter_congr fun o ho => ⟨fun h => ⟨h, third_zero (mem_range.1 (hP ho)) h⟩, fun h => h.1⟩

/-- |Π_j| is the number of members of P that are incidences of check j, for well-formed data (WfD)
and a set P of places of objects. -/
theorem card_chP (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (j : ℕ) : #(chP D P j) = #(sl D 1 j P) := by
  rw [card_sl hW hP, chP]

/-- |Π₁| + … + |Π_r| is the number of members of P of kind 1, for well-formed data (WfD) and a set P
of places of objects. -/
theorem card_kP_one (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) : #(kP D P 1) = ∑ j : Fin (chks D).length, #(sl D 1 j.val P) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => #(sl D 1 j P)), length_chks,
    Finset.card_eq_sum_card_fiberwise (f := fun o => (obAt D o).2.2) (t := range D.2.length)]
  · refine sum_congr rfl fun j _ => ?_
    rw [card_sl hW hP, kP, filter_filter]
  · intro o ho
    obtain ⟨h1, h2⟩ := mem_filter.1 ho
    exact mem_coe.2 (mem_range.2 (inc_mem (mem_range.1 (hP h1)) h2).1)

/-- Cutting and putting together again gives back a set P of positions of objects, for well-formed
data. -/
theorem back_sl (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) :
    back D (sl D 0 0 P) (fun j : Fin (chks D).length => sl D 1 j.val P) = P := by
  ext o
  rw [mem_back]
  constructor
  · rintro ⟨ho, ⟨e, he, hx⟩ | ⟨j, e, he, hx⟩⟩
    · obtain ⟨o', ho', hx'⟩ := mem_sl.1 he
      rwa [obAt_inj hW ho (mem_range.1 (hP ho')) (hx.trans hx'.symm)]
    · obtain ⟨o', ho', hx'⟩ := mem_sl.1 he
      rwa [obAt_inj hW ho (mem_range.1 (hP ho')) (hx.trans hx'.symm)]
  · intro hoP
    have ho := mem_range.1 (hP hoP)
    refine ⟨ho, ?_⟩
    rcases kind_cases ho with h0 | h1
    · have hx : obAt D o = (0, (obAt D o).2.1, 0) := Prod.ext h0 (Prod.ext rfl (third_zero ho h0))
      exact Or.inl ⟨⟨(obAt D o).2.1, cl_lt hW ho⟩, mem_sl.2 ⟨o, hoP, hx⟩, hx⟩
    · have hx : obAt D o = (1, (obAt D o).2.1, (obAt D o).2.2) := Prod.ext h1 rfl
      exact Or.inr ⟨⟨(obAt D o).2.2, by rw [length_chks]; exact (inc_mem ho h1).1⟩, ⟨(obAt D o).2.1, cl_lt hW ho⟩, mem_sl.2 ⟨o, hoP, hx⟩, hx⟩

/-- The part Π₀ of the set put together from (S₀, S) is S₀. -/
theorem sl_zero_back {r : ℕ} (S₀ : Finset (Fin D.1.length)) (S : Fin r → Finset (Fin D.1.length)) : sl D 0 0 (back D S₀ S) = S₀ := by
  ext e
  rw [mem_sl]
  constructor
  · rintro ⟨o, ho, hx⟩
    rcases (mem_back.1 ho).2 with ⟨e', he', hx'⟩ | ⟨j, e', _, hx'⟩
    · have h := hx.symm.trans hx'
      simp only [Prod.mk.injEq, true_and, and_true] at h
      rwa [Fin.ext h]
    · have h := hx.symm.trans hx'
      simp at h
  · intro he
    obtain ⟨o, ho, hx⟩ := exists_obAt (D := D) (x := (0, e.val, 0)) (mem_objs.2 (Or.inl ⟨rfl, e.isLt, rfl⟩))
    exact ⟨o, mem_back.2 ⟨ho, Or.inl ⟨e, he, hx⟩⟩, hx⟩

/-- The part Π_j of the set put together from (S₀, S) is S j, if S j ⊆ Λ_j. -/
theorem sl_one_back (S₀ : Finset (Fin D.1.length)) (S : Fin (chks D).length → Finset (Fin D.1.length)) (j : Fin (chks D).length)
    (hS : S j ⊆ (chks D).getD j.val ∅) : sl D 1 j.val (back D S₀ S) = S j := by
  ext e
  rw [mem_sl]
  constructor
  · rintro ⟨o, ho, hx⟩
    rcases (mem_back.1 ho).2 with ⟨e', _, hx'⟩ | ⟨j', e', he', hx'⟩
    · have h := hx.symm.trans hx'
      simp at h
    · have h := hx.symm.trans hx'
      simp only [Prod.mk.injEq, true_and] at h
      rwa [Fin.ext h.1, Fin.ext h.2]
  · intro he
    have h1 := hS he
    rw [getD_chks, mem_setD] at h1
    obtain ⟨o, ho, hx⟩ := exists_obAt (D := D) (x := (1, e.val, j.val)) (mem_objs.2 (Or.inr ⟨rfl, by rw [← length_chks]; exact j.isLt, h1⟩))
    exact ⟨o, mem_back.2 ⟨ho, Or.inr ⟨j, e, he, hx⟩⟩, hx⟩

/-- S is a tuple (Π₁, …, Π_r) of the display after Lemma 12 (the right sides for X and F) iff Π_j ⊆
Λ_j ∩ V(ξ) for all j and |Π₁| + … + |Π_r| ≤ M. -/
theorem mem_tup {X E : Type} [Fintype X] [Fintype E] [DecidableEq E] {V : X → Finset E} {L : List (Finset E)} {M : ℕ} {ξ : X} {S : Fin L.length → Finset E} :
    S ∈ AppVariables.tup V L M ξ ↔ (∀ j, S j ⊆ L.getD j.val ∅ ∩ V ξ) ∧ ∑ j, #(S j) ≤ M := by
  simp [AppVariables.tup, ParityChecks.tuples, Fintype.mem_piFinset]

/-- E ∈ V(ξ) iff ξ violates the clause number E. -/
theorem mem_Vof {σ : Fin n → Bool} {e : Fin D.1.length} : e ∈ Vof D.1 σ ↔ vio (Mark.ext σ) (D.1.getD e.val []) = true := by
  simp [Vof]

/-- An object is in `vset` iff the assignment violates its clause. -/
theorem mem_vset {σ : ℕ → Bool} {o : ℕ} : o ∈ vset σ D ↔ o < (objs D).length ∧ vio σ (D.1.getD (obAt D o).2.1 []) = true := by
  simp [vset, clOf]

/-- If ξ violates the clauses of all members of P, then ξ violates the clauses of every part of P. -/
theorem sl_subset_Vof {σ : Fin n → Bool} {P : Finset ℕ} (hP : P ⊆ vset (Mark.ext σ) D) (κ j : ℕ) : sl D κ j P ⊆ Vof D.1 σ := by
  intro e he
  obtain ⟨o, ho, hx⟩ := mem_sl.1 he
  have h := (mem_vset.1 (hP ho)).2
  rw [hx] at h
  exact mem_Vof.2 h

/-- Π_j ⊆ Λ_j, for a set P of places of objects. -/
theorem sl_one_subset {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (j : ℕ) : sl D 1 j P ⊆ (chks D).getD j ∅ := by
  intro e he
  obtain ⟨o, ho, hx⟩ := mem_sl.1 he
  have h := (inc_mem (mem_range.1 (hP ho)) (by rw [hx])).2
  rw [hx] at h
  rw [getD_chks, mem_setD]
  exact h

/-- If ξ violates all clauses of S₀ and of the S j, then ξ violates the clauses of all members of
the set put together. -/
theorem back_subset_vset {σ : Fin n → Bool} {r : ℕ} {S₀ : Finset (Fin D.1.length)} {S : Fin r → Finset (Fin D.1.length)}
    (h0 : S₀ ⊆ Vof D.1 σ) (h1 : ∀ j, S j ⊆ Vof D.1 σ) : back D S₀ S ⊆ vset (Mark.ext σ) D := by
  intro o ho
  obtain ⟨hlt, ⟨e, he, hx⟩ | ⟨j, e, he, hx⟩⟩ := mem_back.1 ho
  · exact mem_vset.2 ⟨hlt, by rw [hx]; exact mem_Vof.1 (h0 he)⟩
  · exact mem_vset.2 ⟨hlt, by rw [hx]; exact mem_Vof.1 (h1 j he)⟩

/-- The members of `vset` are positions of objects. -/
theorem vset_subset (σ : ℕ → Bool) (D : Dat) : vset σ D ⊆ range (objs D).length := filter_subset _ _

/-! ### The sum for one ξ -/

/-- The value of the term of P, by the numbers |Π₀| and |Π_j|, for well-formed data (WfD) and a set
P of places of objects. -/
theorem wt_eq (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (fl : Bool) :
    wt D fl P = (bif fl then (-1) ^ #(sl D 0 0 P) else 1) * ∏ j : Fin (chks D).length, ParityChecks.sig #(sl D 1 j.val P) := by
  rw [wt, Fin.prod_univ_eq_prod_range (fun j => ParityChecks.sig #(sl D 1 j P)), length_chks, card_kP_zero hW hP, mul_comm]
  congr 1
  exact prod_congr rfl fun j _ => by rw [card_chP hW hP]

open Classical in
/-- Step 3, «the term is given by ξ and the sets Π₀ and Π_j»: for well-formed data and one ξ, the
sum of the terms of the sets P of objects with violated clauses, within the limits, is the sum over
the tuples
(Π₀, …, Π_r) of the display after Lemma 12. -/
theorem sum_sets (hW : WfD k n D) (nb M : ℕ) (fl : Bool) (σ : Fin n → Bool) :
    (∑ P ∈ (vset (Mark.ext σ) D).powerset, if Lim nb M D fl P then wt D fl P else 0) =
      ∑ S₀ ∈ (Vof D.1 σ).powerset with (if fl = true then #S₀ ≤ nb else #S₀ = nb + 1),
        (bif fl then (-1) ^ #S₀ else 1) * ∑ S ∈ AppVariables.tup (Vof (n := n) D.1) (chks D) M σ, ∏ j, ParityChecks.sig #(S j) := by
  rw [← sum_filter]
  simp_rw [mul_sum]
  rw [← sum_product']
  refine sum_nbij' (fun P => (sl D 0 0 P, fun j : Fin (chks D).length => sl D 1 j.val P)) (fun x => back D x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hP
    have hv := mem_powerset.1 h1
    have hr := hv.trans (vset_subset _ D)
    rw [card_kP_zero hW hr] at h2
    rw [card_kP_one hW hr] at h3
    exact mem_product.2 ⟨mem_filter.2 ⟨mem_powerset.2 (sl_subset_Vof hv 0 0), h2⟩,
      mem_tup.2 ⟨fun j => subset_inter (sl_one_subset hr j.val) (sl_subset_Vof hv 1 j.val), h3⟩⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_product.1 hx
    obtain ⟨h3, h4⟩ := mem_filter.1 h1
    obtain ⟨h5, h6⟩ := mem_tup.1 h2
    have hv : back D x.1 x.2 ⊆ vset (Mark.ext σ) D := back_subset_vset (mem_powerset.1 h3) fun j => (h5 j).trans inter_subset_right
    have hr := hv.trans (vset_subset _ D)
    refine mem_filter.2 ⟨mem_powerset.2 hv, ?_, ?_⟩
    · rw [card_kP_zero hW hr, sl_zero_back]
      exact h4
    · rw [card_kP_one hW hr]
      refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) h6
      rw [sl_one_back _ _ j ((h5 j).trans inter_subset_left)]
  · intro P hP
    exact back_sl hW ((mem_powerset.1 (mem_filter.1 hP).1).trans (vset_subset _ D))
  · intro x hx
    obtain ⟨_, h2⟩ := mem_product.1 hx
    obtain ⟨h5, _⟩ := mem_tup.1 h2
    exact Prod.ext (sl_zero_back _ _) (funext fun j => sl_one_back _ _ j ((h5 j).trans inter_subset_left))
  · intro P hP
    exact wt_eq hW ((mem_powerset.1 (mem_filter.1 hP).1).trans (vset_subset _ D)) fl

/-- Step 3: for well-formed data D, the sum over ξ and the sets P of objects with violated clauses,
within the limits |Π₀| = n̄ + 1 (for F: ≤ n̄) and |Π₁| + … + |Π_r| ≤ M, is the right side of the
display after Lemma 12 (for X, resp. F). -/
public theorem stTuples : StTuples := by
  classical
  intro k n nb M D fl hW
  rw [rhsD, rhsXF]
  cases fl
  · simp only [cond_false]
    refine sum_congr rfl fun σ _ => ?_
    have h := sum_sets hW nb M false σ
    simp only [Bool.false_eq_true, if_false, cond_false, one_mul] at h
    convert h
  · simp only [cond_true]
    refine sum_congr rfl fun σ _ => ?_
    have h := sum_sets hW nb M true σ
    simp only [if_true, cond_true] at h
    convert h

end VariableBound.Net.Tuples
