/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.NetDefs
public import ClauseBound.ParityChecks.Dummy

/-! # The three layers at one assignment

An assignment σ of n + r variables is a pair (ξ, y): ξ assigns the n variables of ψ and y the r
dummy variables of the checks. For each of the three layers of clauses, the number of clauses of the
layer that σ violates is the number of elements of a finite set: the clauses of ψ that ξ violates
(first layer); the incidences that (ξ, y) violates (second layer); the clauses of ψ from number t on
that ξ violates (third layer). -/

public section

open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark

namespace ClauseBound.ParityChecks.BridgeInc

/-! ### Counting in lists -/

/-- The number of members from position t on with a property, as the number of their positions. -/
theorem countP_drop {α : Type} (p : α → Bool) (d : α) : ∀ (L : List α) (t : ℕ),
    (L.drop t).countP p = #{e : Fin L.length | t ≤ e.val ∧ p (L.getD e.val d) = true}
  | [], t => by simp
  | a :: L, 0 => by
    have ih := countP_drop p d L 0
    rw [List.drop_zero] at ih ⊢
    rw [List.countP_cons, ih, card_filter, card_filter]
    change _ = ∑ e : Fin (L.length + 1), _
    rw [Fin.sum_univ_succ]
    simp [add_comm]
  | a :: L, t + 1 => by
    have ih := countP_drop p d L t
    rw [List.drop_succ_cons, ih, card_filter, card_filter]
    change _ = ∑ e : Fin (L.length + 1), _
    rw [Fin.sum_univ_succ]
    simp

/-- The number of members with a property of a list of numbers below m without repetition, as the
number of elements of a subset of Fin m. -/
theorem countP_idx {m : ℕ} {I : List ℕ} (hn : I.Nodup) (hlt : ∀ e ∈ I, e < m) (q : ℕ → Bool) :
    I.countP q = #{e : Fin m | e.val ∈ I ∧ q e.val = true} := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hn.filter _), ← card_image_of_injective _ Fin.val_injective]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, hlt x h1⟩, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨e, h, rfl⟩
    exact h

/-! ### The two parts of an assignment -/

/-- The assignment of the variables of ψ. -/
@[expose] def xi {n r : ℕ} (σ : Fin (n + r) → Bool) : Fin n → Bool := fun v => σ (Fin.castAdd r v)

/-- The assignment of the dummy variables. -/
@[expose] def yy {n r : ℕ} (σ : Fin (n + r) → Bool) : Fin r → Bool := fun j => σ (Fin.natAdd n j)

theorem ext_lt {n r : ℕ} (σ : Fin (n + r) → Bool) {v : ℕ} (h : v < n) : ext σ v = ext (xi σ) v := by
  rw [Mark.ext, Mark.ext, dif_pos h, dif_pos (by omega)]
  rfl

theorem ext_add {n r : ℕ} (σ : Fin (n + r) → Bool) (j : Fin r) : ext σ (n + j.val) = yy σ j := by
  rw [Mark.ext, dif_pos (by omega)]
  rfl

/-- A clause in the variables of ψ sees only ξ. -/
theorem vio_ext {n r : ℕ} (σ : Fin (n + r) → Bool) {C : Cl} (h : ∀ l ∈ C, l.1 < n) : vio (ext σ) C = vio (ext (xi σ)) C := by
  unfold vio
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun l hl => by rw [ext_lt σ (h l hl)]

/-- The same for the clause number e of ψ, whatever e. -/
theorem vio_getD {n r : ℕ} (σ : Fin (n + r) → Bool) {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (e : ℕ) :
    vio (ext σ) (ψ.getD e []) = vio (ext (xi σ)) (ψ.getD e []) := by
  refine vio_ext σ fun l hl => ?_
  by_cases he : e < ψ.length
  · rw [List.getD_eq_getElem _ _ he] at hl
    exact h _ (List.getElem_mem he) l hl
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    exact absurd hl (List.not_mem_nil)

/-- A clause with the dummy literal of check j added is violated if and only if the clause is
violated and the dummy variable is 1. -/
theorem vio_append (τ : ℕ → Bool) (C : Cl) (x : ℕ) : vio τ (C ++ [(x, false)]) = (vio τ C && τ x) := by
  simp [vio]

/-! ### The first and the third layer -/

/-- The clauses from number t on that σ violates. -/
theorem nvio_drop {n r : ℕ} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (t : ℕ) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (ψ.drop t) = #(Dof ψ t ∩ Vof ψ (xi σ)) := by
  rw [nvio, countP_drop _ [], Dof, Vof, ← filter_and]
  exact congrArg card (filter_congr fun e _ => by rw [vio_getD σ h])

/-- The clauses that σ violates. -/
theorem nvio_all {n r : ℕ} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (σ : Fin (n + r) → Bool) : nvio (ext σ) ψ = #(Vof ψ (xi σ)) := by
  have h0 := nvio_drop h 0 σ
  rw [List.drop_zero] at h0
  rw [h0]
  congr 1
  ext e
  simp [Dof]

/-! ### The second layer -/

/-- The number of clauses of check j that τ violates. -/
@[expose] def cnt (τ : ℕ → Bool) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : ℕ := (Lam.getD j []).countP fun e => vio τ (ψ.getD e [])

/-- The incidences that τ violates, check by check. -/
theorem nvio_incL_sum (τ : ℕ → Bool) (n : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) :
    nvio τ (incL n ψ Lam j) = ∑ j' ∈ range j, (if τ (n + j') = true then cnt τ ψ Lam j' else 0) + cnt τ ψ Lam j := by
  have h1 : ∀ j', ((Lam.getD j' []).map fun e => ψ.getD e [] ++ [(n + j', false)]).countP (vio τ) = if τ (n + j') = true then cnt τ ψ Lam j' else 0 := by
    intro j'
    rw [List.countP_map, cnt]
    by_cases hy : τ (n + j') = true
    · rw [if_pos hy]
      exact List.countP_congr fun e _ => by simp [vio_append, hy]
    · rw [if_neg hy, List.countP_eq_zero]
      intro e _
      simp [vio_append, hy]
  have h2 : ((Lam.getD j []).map fun e => ψ.getD e []).countP (vio τ) = cnt τ ψ Lam j := by
    rw [List.countP_map, cnt]
    rfl
  rw [nvio, incL, List.countP_append, h2, List.countP_flatMap]
  congr 1
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  exact sum_congr rfl fun j' _ => h1 j'

/-- Every check, and the empty list beyond the last check, is a list without repetition of numbers
of clauses. -/
theorem wf_getD {ψ : Fml} {r : ℕ} {Lam : List (List ℕ)} (h : WfC ψ r Lam) (j : ℕ) : (Lam.getD j []).Nodup ∧ ∀ e ∈ Lam.getD j [], e < ψ.length := by
  by_cases hj : j < Lam.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨List.nodup_nil, fun e he => absurd he (List.not_mem_nil)⟩

/-- The number of clauses of check j that σ violates, as the number of elements of a set. -/
theorem cnt_eq {n r : ℕ} (σ : Fin (n + r) → Bool) {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) {r' : ℕ} {Lam : List (List ℕ)} (hL : WfC ψ r' Lam) (j : ℕ) :
    cnt (ext σ) ψ Lam j = #(Lof ψ Lam j ∩ Vof ψ (xi σ)) := by
  obtain ⟨h1, h2⟩ := wf_getD hL j
  rw [cnt, countP_idx h1 h2, Lof, Vof, ← filter_and]
  exact congrArg card (filter_congr fun e _ => by rw [vio_getD σ h])

/-- The checks before j. -/
@[expose] def J1 (r j : ℕ) : Finset (Fin r) := univ.filter fun j' => j'.val < j

/-- The check j. -/
@[expose] def J2 (r j : ℕ) : Finset (Fin r) := univ.filter fun j' => j'.val = j

theorem disjoint_J (r j : ℕ) : Disjoint (J1 r j) (J2 r j) := by
  rw [disjoint_left]
  intro a h1 h2
  have h1 := (mem_filter.1 h1).2
  have h2 := (mem_filter.1 h2).2
  omega

/-- A sum over the checks, with the checks before j counted if their dummy variable is 1. -/
theorem sum_checks {n r : ℕ} (σ : Fin (n + r) → Bool) (c : ℕ → ℕ) {j : ℕ} (hj : j ≤ r) :
    ∑ j' ∈ range j, (if ext σ (n + j') = true then c j' else 0) = ∑ j' : Fin r, if j' ∈ J1 r j ∧ yy σ j' = true then c j'.val else 0 := by
  have h1 : ∀ j' : Fin r, (if j' ∈ J1 r j ∧ yy σ j' = true then c j'.val else 0) =
      (fun i : ℕ => if i < j ∧ ext σ (n + i) = true then c i else 0) j'.val := fun j' => by
    simp only [J1, mem_filter, mem_univ, true_and, ext_add]
  rw [sum_congr rfl fun j' _ => h1 j', Fin.sum_univ_eq_sum_range fun i : ℕ => if i < j ∧ ext σ (n + i) = true then c i else 0]
  rw [← sum_subset (range_subset_range.2 hj) fun i _ hi => if_neg fun h => hi (mem_range.2 h.1)]
  exact sum_congr rfl fun i hi => by simp [mem_range.1 hi]

/-- The incidences of the checks before j and of check j that σ violates. (For j = r there is no
check j.) -/
theorem nvio_incL {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hL : WfC ψ r Lam) (hj : j ≤ r) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (incL n ψ Lam j) = #(Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) (xi σ) (yy σ)) := by
  rw [nvio_incL_sum, Dummy.card_inc, sum_checks σ _ hj]
  have e2 : ∀ j' : Fin r, j' ∈ J2 r j ↔ j'.val = j := fun j' => by simp [J2]
  have h2 : cnt (ext σ) ψ Lam j = ∑ j' : Fin r, if j' ∈ J2 r j then cnt (ext σ) ψ Lam j'.val else 0 := by
    rcases Nat.lt_or_ge j r with hlt | hge
    · rw [sum_eq_single (⟨j, hlt⟩ : Fin r)]
      · rw [if_pos ((e2 _).2 rfl)]
      · intro b _ hb
        exact if_neg fun h' => hb (Fin.ext ((e2 b).1 h'))
      · intro h'
        exact absurd (mem_univ _) h'
    · rw [sum_eq_zero fun j' _ => if_neg fun h' => by have := (e2 j').1 h'; have := j'.2; omega]
      unfold cnt
      rw [List.getD_eq_default _ _ (by rw [hL.1]; exact hge)]
      rfl
  rw [h2, ← sum_add_distrib]
  refine sum_congr rfl fun j' _ => ?_
  rw [← cnt_eq σ h hL]
  have e1 : j' ∈ J1 r j ↔ j'.val < j := by simp [J1]
  simp only [e1, e2]
  rcases lt_trichotomy j'.val j with hlt | heq | hgt
  · simp [hlt, hlt.ne]
  · simp [heq]
  · simp [not_lt.2 hgt.le, hgt.ne']

/-- The checks before j, cut out of the list of all checks. -/
theorem cnt_take (τ : ℕ → Bool) (ψ : Fml) (Lam : List (List ℕ)) {j j' : ℕ} (h : j' < j) : cnt τ ψ (Lam.take j) j' = cnt τ ψ Lam j' := by
  unfold cnt
  congr 1
  simp [List.getD_eq_getElem?_getD, h]

theorem cnt_take_self (τ : ℕ → Bool) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : cnt τ ψ (Lam.take j) j = 0 := by
  unfold cnt
  rw [List.getD_eq_default _ _ (by simp)]
  rfl

/-- The incidences of the checks before j that σ violates. -/
theorem nvio_incL_take {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hL : WfC ψ r Lam) (hj : j ≤ r) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (incL n ψ (Lam.take j) j) = #(Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ (xi σ) (yy σ)) := by
  rw [nvio_incL_sum, Dummy.card_inc, cnt_take_self, add_zero,
    sum_congr rfl fun j' hj' => by rw [cnt_take _ _ _ (mem_range.1 hj')], sum_checks σ _ hj]
  refine sum_congr rfl fun j' _ => ?_
  rw [← cnt_eq σ h hL]
  simp

/-! ### Products over the checks -/

/-- A product over the checks before j. -/
theorem prod_J1 {r j : ℕ} (hj : j ≤ r) (g : ℕ → ℤ) : ∏ j' ∈ J1 r j, g j'.val = ∏ j' ∈ range j, g j' := by
  refine prod_bij (fun a _ => a.val) (fun a ha => mem_range.2 (mem_filter.1 ha).2) (fun a _ b _ hab => Fin.ext hab)
    (fun b hb => ⟨⟨b, (mem_range.1 hb).trans_le hj⟩, mem_filter.2 ⟨mem_univ _, mem_range.1 hb⟩, rfl⟩) fun _ _ => rfl

/-- A product over the one check j. -/
theorem prod_J2 {r j : ℕ} (hj : j < r) (g : ℕ → ℤ) : ∏ j' ∈ J2 r j, g j'.val = g j := by
  have h : J2 r j = {(⟨j, hj⟩ : Fin r)} := by
    ext a
    simp [J2, Fin.ext_iff]
  rw [h, prod_singleton]

end ClauseBound.ParityChecks.BridgeInc
