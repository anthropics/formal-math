/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # One decision does not change the potential on average

A state consists of the checks chosen so far and of the set D of the clauses that are not yet
decided for check j. One decision takes a clause e out of D and either puts it into check j or
leaves it out. For each of the four terms of the potential, p times the value after «in» plus 1 − p
times the value after «out» is the value before the decision. In the first term only the ξ
that violate e count; in the second the numerator changes by 1 − p or by −p; in the third only the
summand of check j, and in the fourth only the summand of e, changes: it is multiplied by
2/(1 + p) or by 1/(1 + p). -/

public section

open Finset ParityChecks

namespace ClauseBound.ParityChecks.Martingale

variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-! ### The check after «in», and small facts -/

omit [Fintype E] in
/-- After «in», check j has the clause e in addition. -/
theorem putIn_same (j : ℕ) (Λ : ℕ → Finset E) (e : E) : putIn j Λ e j = insert e (Λ j) := Function.update_self ..

omit [Fintype E] in
/-- After «in», the other checks are as before. -/
theorem putIn_ne {j j' : ℕ} (h : j' ≠ j) (Λ : ℕ → Finset E) (e : E) : putIn j Λ e j' = Λ j' := Function.update_of_ne h ..

/-- 1 + p ≠ 0. -/
theorem one_add_pr_ne (nb : ℕ) : 1 + pr nb ≠ 0 := by
  have h : 0 ≤ pr nb := by unfold pr; positivity
  linarith

omit [Fintype E] [DecidableEq E] in
/-- A clause that is not yet decided for check j is not in check j. -/
theorem notMem_of_mem {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) : e ∉ Λ j :=
  fun h => (disjoint_left.1 hS.disj h) he

omit [Fintype E] in
/-- D has one clause more than D without e. -/
theorem card_eq_succ {D : Finset E} {e : E} (he : e ∈ D) : #D = #(D.erase e) + 1 := by
  have h := card_erase_of_mem he
  have h0 : 0 < #D := card_pos.2 ⟨e, he⟩
  omega

/-- 2p + (1 − p) = 1 + p, with the common factor x/(1 + p)^{k+1}. -/
theorem average (p x : ℚ) (k : ℕ) (hp : 1 + p ≠ 0) : p * (2 * x / (1 + p) ^ (k + 1)) + (1 - p) * (x / (1 + p) ^ (k + 1)) = x / (1 + p) ^ k := by
  field_simp
  ring

/-! ### The four terms -/

omit [Fintype E] in
/-- One decision, first term. -/
theorem upar (V : X → Finset E) (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Upar V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Upar V nb r j Λ (D.erase e) = Upar V nb r j Λ D := by
  have hej := notMem_of_mem hS he
  unfold Upar
  rw [mul_left_comm (pr nb), mul_left_comm (1 - pr nb), ← mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun ξ _ => ?_
  have hprod : ∏ j' ∈ range j, (ev #(putIn j Λ e j' ∩ V ξ) : ℚ) = ∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ) :=
    prod_congr rfl fun j' hj' => by rw [putIn_ne (ne_of_lt (mem_range.1 hj'))]
  rw [hprod, putIn_same]
  by_cases hv : e ∈ V ξ
  · have h1 : #(insert e (Λ j) ∩ V ξ) = #(Λ j ∩ V ξ) + 1 := by
      rw [insert_inter_of_mem hv, card_insert_of_notMem fun h => hej (mem_inter.1 h).1]
    have h2 : #(D ∩ V ξ) = #(D.erase e ∩ V ξ) + 1 := by
      rw [erase_inter]
      exact card_eq_succ (mem_inter.2 ⟨he, hv⟩)
    rw [h1, h2]
    ring
  · have h1 : insert e (Λ j) ∩ V ξ = Λ j ∩ V ξ := insert_inter_of_notMem hv
    have h2 : D.erase e ∩ V ξ = D ∩ V ξ := by
      rw [erase_inter, erase_eq_of_notMem fun h => hv (mem_inter.1 h).2]
    rw [h1, h2]
    ring

omit [Fintype E] in
/-- After «in», the checks have one pair more. -/
theorem sum_card_putIn {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    ∑ j' ∈ range r, #(putIn j Λ e j') = ∑ j' ∈ range r, #(Λ j') + 1 := by
  have hj : j ∈ range r := mem_range.2 hS.j_lt
  rw [← add_sum_erase _ _ hj, ← add_sum_erase (range r) (fun j' => #(Λ j')) hj, putIn_same, card_insert_of_notMem (notMem_of_mem hS he),
    sum_congr rfl fun j' hj' => by rw [putIn_ne (ne_of_mem_erase hj')]]
  omega

omit [DecidableEq E] in
/-- For check j the clauses of D are not yet decided. -/
theorem undRow_self (j : ℕ) (D : Finset E) : undRow j D j = #D := by simp [undRow]

omit [DecidableEq E] in
/-- For the other checks D does not matter. -/
theorem undRow_ne {j j' : ℕ} (h : j' ≠ j) (D D' : Finset E) : undRow j D j' = undRow j D' j' := by simp [undRow, h]

/-- Before the decision, one pair more is not yet decided. -/
theorem sum_undRow {r j : ℕ} {D : Finset E} {e : E} (hj : j < r) (he : e ∈ D) :
    ∑ j' ∈ range r, undRow j D j' = ∑ j' ∈ range r, undRow j (D.erase e) j' + 1 := by
  have hj : j ∈ range r := mem_range.2 hj
  have h1 : ∑ j' ∈ range r, undRow j D j' = undRow j D j + ∑ j' ∈ (range r).erase j, undRow j D j' := (add_sum_erase _ _ hj).symm
  have h2 : ∑ j' ∈ range r, undRow j (D.erase e) j' = undRow j (D.erase e) j + ∑ j' ∈ (range r).erase j, undRow j (D.erase e) j' :=
    (add_sum_erase _ _ hj).symm
  have h3 : ∑ j' ∈ (range r).erase j, undRow j D j' = ∑ j' ∈ (range r).erase j, undRow j (D.erase e) j' :=
    sum_congr rfl fun j' hj' => undRow_ne (ne_of_mem_erase hj') D (D.erase e)
  rw [h1, h2, h3, undRow_self, undRow_self, card_eq_succ he]
  omega

/-- One decision, second term. -/
theorem uinc (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Uinc nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Uinc nb r j Λ (D.erase e) = Uinc nb r j Λ D := by
  unfold Uinc
  rw [sum_card_putIn hS he, sum_undRow hS.j_lt he]
  push_cast
  ring

/-- One decision, third term. -/
theorem urow (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Urow nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Urow nb r j Λ (D.erase e) = Urow nb r j Λ D := by
  unfold Urow
  rw [mul_left_comm (pr nb), mul_left_comm (1 - pr nb), ← mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j' _ => ?_
  by_cases hjj : j' = j
  · subst hjj
    have hD := card_eq_succ he
    have hle : #D ≤ Fintype.card E := card_le_univ D
    have hk : Fintype.card E - #(D.erase e) = Fintype.card E - #D + 1 := by omega
    rw [putIn_same, card_insert_of_notMem (notMem_of_mem hS he), undRow_self, undRow_self, hk, pow_succ' (2 : ℚ)]
    exact average _ _ _ (one_add_pr_ne nb)
  · rw [putIn_ne hjj, undRow_ne hjj (D.erase e) D]
    ring

omit [Fintype E] in
/-- After «in», the clause e is in one check more. -/
theorem card_col_putIn_self {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    #{j' ∈ range r | e ∈ putIn j Λ e j'} = #{j' ∈ range r | e ∈ Λ j'} + 1 := by
  have h : {j' ∈ range r | e ∈ putIn j Λ e j'} = insert j {j' ∈ range r | e ∈ Λ j'} := by
    ext j'
    by_cases hjj : j' = j
    · subst hjj
      simp [putIn_same, hS.j_lt]
    · simp [putIn_ne hjj, hjj]
  have hn : j ∉ {j' ∈ range r | e ∈ Λ j'} := fun h' => notMem_of_mem hS he (mem_filter.1 h').2
  rw [h, card_insert_of_notMem hn]

omit [Fintype E] in
/-- After «in», the other clauses are in the same checks. -/
theorem card_col_putIn_ne (r j : ℕ) (Λ : ℕ → Finset E) {e e' : E} (h : e' ≠ e) :
    #{j' ∈ range r | e' ∈ putIn j Λ e j'} = #{j' ∈ range r | e' ∈ Λ j'} := by
  congr 1
  refine filter_congr fun j' _ => ?_
  by_cases hjj : j' = j
  · subst hjj
    simp [putIn_same, h]
  · rw [putIn_ne hjj]

/-- One decision, fourth term. -/
theorem ucol (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Ucol nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ucol nb r j Λ (D.erase e) = Ucol nb r j Λ D := by
  unfold Ucol
  rw [mul_left_comm (pr nb), mul_left_comm (1 - pr nb), ← mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun e' _ => ?_
  by_cases hee : e' = e
  · subst hee
    have hj := hS.j_lt
    have h1 : undCol r j D e' = r - 1 - j + 1 := by simp [undCol, he]
    have h2 : undCol r j (D.erase e') e' = r - 1 - j := by simp [undCol]
    have hk : r - (r - 1 - j) = r - (r - 1 - j + 1) + 1 := by omega
    rw [card_col_putIn_self hS he, h1, h2, hk, pow_succ' (2 : ℚ)]
    exact average _ _ _ (one_add_pr_ne nb)
  · have h1 : undCol r j (D.erase e) e' = undCol r j D e' := by simp [undCol, hee]
    rw [card_col_putIn_ne r j Λ hee, h1]
    ring

/-! ### The potential -/

/-- One decision: p·Υ^in + (1 − p)·Υ^out = Υ. -/
theorem martingale : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (e : E),
    2 ≤ nb → IsState r j Λ D → e ∈ D →
    pr nb * Ups V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ups V nb r j Λ (D.erase e) = Ups V nb r j Λ D := by
  intro X E _ _ _ V nb r j Λ D e _ hS he
  unfold Ups
  rw [← upar V nb hS he, ← uinc nb hS he, ← urow nb hS he, ← ucol nb hS he]
  ring

end ClauseBound.ParityChecks.Martingale
