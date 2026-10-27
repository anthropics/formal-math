/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-! # Marks and layers: the sum over the sets of violated clauses

Fix an assignment σ. A set P of clauses that σ violates, with at most w clauses in every layer, gets
the sign (−1)^(number of its clauses outside the first layer). The sum of
these signs is the product over the layers of the cut-off sums: Σ_{j ≤ w} C(v, j) for the first
layer and Σ_{j ≤ w} (−1)^j·C(v, j) for the others, where v is the number of
violated clauses of the layer (`stPiSum`). The reason: P is chosen layer by layer, and a layer has
C(v, j) sets of j violated clauses.
The first part is about any finite set V with a map `lay` into the layers 0, …, R − 1; the second
part applies it to the list of all clauses of
`proof/rates/PaddedDescent/F/MarkNet.lean`. -/

namespace PaddedDescent.F.Mark.Pi

open Finset Groundwork Groundwork.Prog

/-! ### Any finite set divided into layers -/

variable {ι : Type*} [DecidableEq ι]

/-- The sum of F (X ∩ A) · G (X ∩ B) over the subsets X of a disjoint union A ∪ B is the sum of F
over the subsets of A times the sum of G over the subsets of B. -/
theorem sum_powerset_union {A B : Finset ι} (hAB : Disjoint A B) (F G : Finset ι → ℤ) :
    ∑ X ∈ (A ∪ B).powerset, F (X ∩ A) * G (X ∩ B) = (∑ P ∈ A.powerset, F P) * ∑ Q ∈ B.powerset, G Q := by
  rw [sum_mul_sum, ← sum_product']
  symm
  refine sum_nbij' (fun p => p.1 ∪ p.2) (fun X => (X ∩ A, X ∩ B)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    exact mem_powerset.2 (union_subset_union (mem_powerset.1 h1) (mem_powerset.1 h2))
  · intro X _
    exact mem_product.2 ⟨mem_powerset.2 inter_subset_right, mem_powerset.2 inter_subset_right⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have h1 := mem_powerset.1 h1
    have h2 := mem_powerset.1 h2
    have e1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h1, (disjoint_iff_inter_eq_empty.1 (hAB.symm.mono_left h2)), union_empty]
    have e2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h2, (disjoint_iff_inter_eq_empty.1 (hAB.mono_left h1)), empty_union]
    exact Prod.ext e1 e2
  · intro X hX
    change X ∩ A ∪ X ∩ B = X
    rw [← inter_union_distrib_left, inter_eq_left.2 (mem_powerset.1 hX)]
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have h1 := mem_powerset.1 h1
    have h2 := mem_powerset.1 h2
    have e1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h1, (disjoint_iff_inter_eq_empty.1 (hAB.symm.mono_left h2)), union_empty]
    have e2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h2, (disjoint_iff_inter_eq_empty.1 (hAB.mono_left h1)), empty_union]
    rw [e1, e2]

/-- Let a subset X of V have the weight Π_{i < R} φ i (the part of X in layer i). The sum of the
weights is the product over the layers of the sum of φ i over the subsets
of layer i. -/
theorem sum_powerset_layers (lay : ι → ℕ) (φ : ℕ → Finset ι → ℤ) (R : ℕ) (V : Finset ι) (hV : ∀ e ∈ V, lay e < R) :
    ∑ X ∈ V.powerset, ∏ i ∈ range R, φ i (X.filter fun e => lay e = i) =
      ∏ i ∈ range R, ∑ P ∈ (V.filter fun e => lay e = i).powerset, φ i P := by
  induction R generalizing V with
  | zero =>
    have : V = ∅ := eq_empty_of_forall_notMem fun e he => absurd (hV e he) (Nat.not_lt_zero _)
    subst this
    simp
  | succ R ih =>
    have hsplit : V = (V.filter fun e => lay e < R) ∪ V.filter fun e => lay e = R := by
      ext e
      simp only [mem_union, mem_filter]
      constructor
      · intro he
        have := hV e he
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, h⟩
      · rintro (h | h) <;> exact h.1
    have hdis : Disjoint (V.filter fun e => lay e < R) (V.filter fun e => lay e = R) := by
      rw [disjoint_left]
      intro e h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
    have key := sum_powerset_union hdis (fun P => ∏ i ∈ range R, φ i (P.filter fun e => lay e = i)) (φ R)
    rw [← hsplit, ih _ fun e he => (mem_filter.1 he).2] at key
    rw [prod_range_succ, ← prod_congr rfl (g := fun i => ∑ P ∈ (V.filter fun e => lay e = i).powerset, φ i P) ?_] 
    · rw [← key]
      refine sum_congr rfl fun X hX => ?_
      have hX := mem_powerset.1 hX
      rw [prod_range_succ]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        congr 1
        ext e
        simp only [mem_filter, mem_inter]
        constructor
        · rintro ⟨he, rfl⟩; exact ⟨⟨he, hX he, mem_range.1 hi⟩, rfl⟩
        · rintro ⟨⟨he, -⟩, h⟩; exact ⟨he, h⟩
      · congr 1
        ext e
        simp only [mem_filter, mem_inter]
        constructor
        · rintro ⟨he, h⟩; exact ⟨he, hX he, h⟩
        · rintro ⟨he, -, h⟩; exact ⟨he, h⟩
    · intro i hi
      congr 2
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨he, -⟩, h⟩; exact ⟨he, h⟩
      · rintro ⟨he, rfl⟩; exact ⟨⟨he, mem_range.1 hi⟩, rfl⟩

omit [DecidableEq ι] in
/-- The sum of s^|P| over the subsets P of S with at most w elements is Σ_{j ≤ w} s^j·C(|S|, j). -/
theorem sum_powerset_cap (S : Finset ι) (w : ℕ) (s : ℤ) :
    ∑ P ∈ S.powerset, (if P.card ≤ w then s ^ P.card else 0) = ∑ j ∈ range (w + 1), s ^ j * (S.card.choose j : ℤ) := by
  rw [sum_powerset_apply_card (fun m => if m ≤ w then s ^ m else 0)]
  have hL : ∑ m ∈ range (S.card + 1), S.card.choose m • (if m ≤ w then s ^ m else 0) =
      ∑ m ∈ (range (S.card + 1)).filter (· ≤ w), s ^ m * (S.card.choose m : ℤ) := by
    rw [sum_filter]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp [mul_comm]
  have hR : ∑ j ∈ range (w + 1), s ^ j * (S.card.choose j : ℤ) =
      ∑ j ∈ (range (w + 1)).filter (· ≤ S.card), s ^ j * (S.card.choose j : ℤ) := by
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hL, hR]
  congr 1
  ext m
  simp only [mem_filter, mem_range]
  omega

omit [DecidableEq ι] in
/-- With the factor 1 for each element of layer 0 and −1 for each other element, the product over
the layers is (−1)^(number of elements outside layer 0). -/
theorem prod_sign (lay : ι → ℕ) (R : ℕ) (X : Finset ι) (hX : ∀ e ∈ X, lay e < R) :
    ∏ i ∈ range R, (if i = 0 then (1 : ℤ) else -1) ^ (X.filter fun e => lay e = i).card =
      (-1) ^ (X.filter fun e => 1 ≤ lay e).card := by
  have h1 : (X.filter fun e => 1 ≤ lay e).card = ∑ i ∈ range R, if i = 0 then 0 else (X.filter fun e => lay e = i).card := by
    rw [card_eq_sum_card_fiberwise (f := lay) (t := range R) fun e he => mem_range.2 (hX e (mem_filter.1 he).1)]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · subst h
      rw [card_eq_zero, filter_filter, filter_eq_empty_iff]
      intro e _ he
      omega
    · congr 1
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨he, -⟩, h2⟩; exact ⟨he, h2⟩
      · rintro ⟨he, h2⟩; exact ⟨⟨he, by omega⟩, h2⟩
  rw [h1, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The sum of (−1)^(number of elements outside layer 0) over the subsets X of V with at most w
elements in every layer is the product over the layers of the cut-off sums. -/
theorem sum_capped (lay : ι → ℕ) (R w : ℕ) (V : Finset ι) (hV : ∀ e ∈ V, lay e < R) :
    ∑ X ∈ V.powerset.filter (fun X => ∀ i < R, (X.filter fun e => lay e = i).card ≤ w),
        (-1 : ℤ) ^ (X.filter fun e => 1 ≤ lay e).card =
      ∏ i ∈ range R, ∑ j ∈ range (w + 1),
        (if i = 0 then (1 : ℤ) else -1) ^ j * ((V.filter fun e => lay e = i).card.choose j : ℤ) := by
  rw [← prod_congr rfl fun i _ => sum_powerset_cap (V.filter fun e => lay e = i) w (if i = 0 then (1 : ℤ) else -1),
    ← sum_powerset_layers lay (fun i P => if P.card ≤ w then (if i = 0 then (1 : ℤ) else -1) ^ P.card else 0) R V hV,
    sum_filter]
  refine sum_congr rfl fun X hX => ?_
  have hXV := mem_powerset.1 hX
  split_ifs with h
  · rw [← prod_sign lay R X fun e he => hV e (hXV he)]
    exact prod_congr rfl fun i hi => (if_pos (h i (mem_range.1 hi))).symm
  · simp only [not_forall] at h
    obtain ⟨i, hi, hw⟩ := h
    exact (prod_eq_zero (mem_range.2 hi) (if_neg hw)).symm

/-! ### The list of all clauses -/

/-- The number of places of a list whose entry has the property p is the count of p in the list. -/
theorem card_filter_range_getD {β : Type*} (p : β → Bool) (d : β) (l : List β) :
    ((range l.length).filter fun e => p (l.getD e d) = true).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [card_filter, List.length_cons, sum_range_succ', ← card_filter]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.countP_cons]

/-- A sum over the places below n in which only the place i counts, with c, is c if i < n and 0
otherwise. -/
theorem sum_range_ite (n i c : ℕ) : ((List.range n).map fun i' => if i' = i then c else 0).sum = if i < n then c else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    split_ifs <;> omega

/-- The product of f over a list is the product over its places. -/
theorem prod_map_eq_prod_range {β : Type*} (f : β → ℤ) (d : β) (l : List β) :
    (l.map f).prod = ∏ i ∈ range l.length, f (l.getD i d) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, prod_range_succ', List.map_cons, List.prod_cons, ih, mul_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- The layer of a clause of the list of all clauses is below the number of layers. -/
theorem layer_lt (Ls : List Fml) {e : ℕ} (he : e < (cls Ls).length) : (clAt Ls e).1 < Ls.length := by
  have hm : clAt Ls e ∈ cls Ls := by
    rw [clAt, List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hm
  obtain ⟨C, -, hC⟩ := List.mem_map.1 hq
  rw [← hC]
  exact List.mem_range.1 hi

/-- Among all clauses, those of layer i with the property p are as many as the clauses with p in the
list of layer i. -/
theorem countP_cls (p : Cl → Bool) (Ls : List Fml) (i : ℕ) :
    (cls Ls).countP (fun q => p q.2 && decide (q.1 = i)) = (Ls.getD i []).countP p := by
  rw [cls, List.countP_flatMap]
  have : (List.range Ls.length).map ((List.countP fun q : ℕ × Cl => p q.2 && decide (q.1 = i)) ∘ fun i' => (Ls.getD i' []).map fun C => (i', C)) =
      (List.range Ls.length).map fun i' => if i' = i then (Ls.getD i []).countP p else 0 := by
    refine List.map_congr_left fun i' _ => ?_
    simp only [Function.comp, List.countP_map]
    split_ifs with h
    · subst h
      refine List.countP_congr fun C _ => ?_
      simp
    · rw [List.countP_eq_zero]
      intro C _
      simp [h]
  rw [this, sum_range_ite]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (Nat.not_lt.1 h)]; rfl

/-! ### The interface statement -/

/-- The violated clauses of layer i are as many as `nvio` counts in the list of layer i. -/
public theorem card_layP_vset (σ : ℕ → Bool) (Ls : List Fml) (i : ℕ) : (layP Ls (vset σ Ls) i).card = nvio σ (Ls.getD i []) := by
  rw [nvio, ← countP_cls (vio σ) Ls i, ← card_filter_range_getD _ (0, []) (cls Ls), layP, vset, filter_filter]
  congr 1
  ext e
  simp [clAt]

/-- The sum, over the sets P of violated clauses with at most w clauses in every layer, of the sign
of P is the product of the cut-off sums of the layers: unsigned for the
first layer, signed for the others. -/
public theorem sum_vset (σ : ℕ → Bool) (w : ℕ) (Ls : List Fml) :
    ∑ P ∈ (vset σ Ls).powerset.filter (fun P => ∀ i < Ls.length, (layP Ls P i).card ≤ w), sgnP Ls P =
      Tpl w (nvio σ (Ls.headD [])) * (Ls.tail.map fun L => Tsg w (nvio σ L)).prod := by
  have h := sum_capped (fun e => (clAt Ls e).1) Ls.length w (vset σ Ls) fun e he => layer_lt Ls (mem_range.1 (mem_filter.1 he).1)
  have hc : ∀ i, ((vset σ Ls).filter fun e => (clAt Ls e).1 = i).card = nvio σ (Ls.getD i []) := card_layP_vset σ Ls
  simp only [hc] at h
  refine Eq.trans h ?_
  obtain _ | ⟨L, T⟩ := Ls
  · simp [Tpl, nvio, sum_range_succ']
  · rw [List.length_cons, prod_range_succ', mul_comm, List.tail_cons, prod_map_eq_prod_range _ [] T]
    simp [Tpl, Tsg]

/-- `sum_vset`, as the interface states it. -/
public theorem stPiSum : StPiSum := by
  intro w Ls σ
  rw [← sum_vset σ w Ls, sum_filter]

end PaddedDescent.F.Mark.Pi
