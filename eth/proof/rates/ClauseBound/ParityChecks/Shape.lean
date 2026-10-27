/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs

/-! # The three layers of a state

In a state of the choice of the checks the network of marks is fed with three layers of clauses on n +
r variables: the clauses of ψ, the incidences, and the clauses not yet decided. This file
proves what the evaluation needs of them (`stShape`): every clause has 1 to k + 1 literals on these
variables; no variable occurs in too many clauses; there are not too many clauses. A variable
of ψ occurs in at most Δ clauses of ψ, and in the incidences of these clauses, of which each clause
has as many as there are checks that contain it; a dummy variable occurs in the incidences of its
check. The numbers of checks that contain a clause, of clauses of a check and of all incidences are
bounded in every state that is tried (`Tent`); the bounds are turned into natural numbers with
(1 + 1/nb)^(2·nb) ≤ 8. -/

public section

namespace ClauseBound.ParityChecks.Shape

open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

/-! ### Powers of 1 + 1/nb -/

/-- `pr nb` = 1/nb ≥ 0 (this is not the p of Appendix D of the paper). -/
theorem pr_nonneg (nb : ℕ) : 0 ≤ pr nb := by
  unfold pr; positivity

/-- (1 + 1/nb)^(2·nb) ≤ e² ≤ 8. -/
theorem pow_two_mul_le (nb : ℕ) (h : 1 ≤ nb) : (1 + pr nb) ^ (2 * nb) ≤ 8 := by
  have hnb : (0 : ℝ) < nb := by exact_mod_cast h
  have h1 : (1 : ℝ) + 1 / nb ≤ Real.exp (1 / nb) := by
    have := Real.add_one_le_exp (1 / (nb : ℝ))
    linarith
  have h2 : ((1 : ℝ) + 1 / nb) ^ (2 * nb) ≤ Real.exp (1 / nb) ^ (2 * nb) := pow_le_pow_left₀ (by positivity) h1 _
  have h3 : Real.exp (1 / (nb : ℝ)) ^ (2 * nb) = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have h4 : Real.exp 1 ^ 2 ≤ 8 := by
    have h5 := Real.exp_one_lt_d9
    have h6 := Real.exp_pos 1
    nlinarith
  have h7 : (((1 + 1 / (nb : ℚ)) ^ (2 * nb) : ℚ) : ℝ) ≤ ((8 : ℚ) : ℝ) := by
    push_cast
    exact h2.trans (h3.le.trans h4)
  unfold pr
  exact_mod_cast h7

/-- (1 + 1/nb)^N ≤ 2^(⌊3N/(2·nb)⌋ + 1). -/
theorem pow_le_two_pow (nb N : ℕ) (h : 1 ≤ nb) : (1 + pr nb) ^ N ≤ 2 ^ (3 * N / (2 * nb) + 1) := by
  have hp := pr_nonneg nb
  have ht : 3 * N < 2 * nb * (3 * N / (2 * nb) + 1) := Nat.lt_mul_div_succ _ (by omega)
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : 2 * nb ≠ 0)).1 ?_
  calc ((1 + pr nb) ^ N) ^ (2 * nb) = ((1 + pr nb) ^ (2 * nb)) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ 8 ^ N := pow_le_pow_left₀ (by positivity) (pow_two_mul_le nb h) _
    _ = 2 ^ (3 * N) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ (2 * nb * (3 * N / (2 * nb) + 1)) := pow_le_pow_right₀ (by norm_num) ht.le
    _ = (2 ^ (3 * N / (2 * nb) + 1)) ^ (2 * nb) := by rw [← pow_mul, Nat.mul_comm]

/-- From 2^c < 16·a·(1 + 1/nb)^N: c ≤ ⌈log₂(16a)⌉ + ⌊3N/(2·nb)⌋. -/
theorem le_of_two_pow_lt {nb a c N : ℕ} (hnb : 1 ≤ nb) (h : (2 : ℚ) ^ c < 2 * (8 * a * (1 + pr nb) ^ N)) :
    c ≤ Nat.clog 2 (16 * a) + 3 * N / (2 * nb) := by
  have hp := pr_nonneg nb
  have h1 : ((16 * a : ℕ) : ℚ) ≤ 2 ^ Nat.clog 2 (16 * a) := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h2 := pow_le_two_pow nb N hnb
  have h3 : (2 : ℚ) ^ c < 2 ^ (Nat.clog 2 (16 * a) + (3 * N / (2 * nb) + 1)) :=
    calc (2 : ℚ) ^ c < 2 * (8 * a * (1 + pr nb) ^ N) := h
      _ = ((16 * a : ℕ) : ℚ) * (1 + pr nb) ^ N := by push_cast; ring
      _ ≤ 2 ^ Nat.clog 2 (16 * a) * 2 ^ (3 * N / (2 * nb) + 1) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have h4 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 h3
  omega

/-! ### Counting in lists -/

/-- Does the variable v occur in the clause C? -/
@[expose] def hasV (v : ℕ) (C : List (ℕ × Bool)) : Bool := C.any fun l => l.1 == v

/-- The clauses in which v occurs. -/
theorem occ_eq (x : Fml) (v : ℕ) : occ x v = x.filter (hasV v) := rfl

/-- A literal more. -/
theorem hasV_append_singleton (v : ℕ) (C : List (ℕ × Bool)) (l : ℕ × Bool) : hasV v (C ++ [l]) = (hasV v C || l.1 == v) := by
  simp [hasV, List.any_append]

/-- A variable that is not among those of C does not occur in C. -/
theorem hasV_eq_false {v n : ℕ} {C : List (ℕ × Bool)} (hC : ∀ l ∈ C, l.1 < n) (hv : n ≤ v) : hasV v C = false := by
  rw [hasV, List.any_eq_false]
  intro l hl
  have := hC l hl
  simp only [beq_iff_eq]
  omega

/-- The members with a property of a list without repetition of numbers below m, counted as a set. -/
theorem countP_eq_card {L : List ℕ} (hL : L.Nodup) {m : ℕ} (hm : ∀ x ∈ L, x < m) (P : ℕ → Bool) :
    L.countP P = #{x ∈ range m | x ∈ L ∧ P x = true} := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨hm x h.1, h⟩, fun h => h.2⟩

/-- The clauses with a property, counted by their numbers. -/
theorem length_filter_eq_card (ψ : Fml) (P : List (ℕ × Bool) → Bool) :
    (ψ.filter P).length = #{x ∈ range ψ.length | P (ψ.getD x []) = true} := by
  have hψ : ψ = (List.range ψ.length).map fun x => ψ.getD x [] := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [List.getElem?_eq_getElem h1]
  have h1 : (ψ.filter P).length = (List.range ψ.length).countP fun x => P (ψ.getD x []) := by
    conv_lhs => rw [hψ]
    rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl
  rw [h1, countP_eq_card List.nodup_range (fun x hx => List.mem_range.1 hx)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_range]
  tauto

/-- The members with a property of a list that is put together from pieces number 0, …, j − 1. -/
theorem length_filter_flatMap_range {γ : Type} (f : ℕ → List γ) (P : γ → Bool) (j : ℕ) :
    (((List.range j).flatMap f).filter P).length = ∑ j' ∈ range j, ((f j').filter P).length := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.flatMap_append, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    simp

/-- The same for the whole list. -/
theorem length_flatMap_range {γ : Type} (f : ℕ → List γ) (j : ℕ) :
    ((List.range j).flatMap f).length = ∑ j' ∈ range j, (f j').length := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
    simp

/-- A check as a set has as many members as the list. -/
theorem card_lam {m : ℕ} (Lam : List Chk) (j' : ℕ) (hL : (Lam.getD j' []).Nodup) (hm : ∀ x ∈ Lam.getD j' [], x < m) :
    #(lam m Lam j') = (Lam.getD j' []).length := by
  rw [← List.toFinset_card_of_nodup hL, ← Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext y
  simp only [lam, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  exact ⟨fun ⟨x, hx, e⟩ => e ▸ hx, fun hy => ⟨⟨y, hm y hy⟩, hy, rfl⟩⟩

/-- Every entry of the list of checks, also beyond its end, is a list without repetition of numbers
of clauses. -/
theorem getD_ok {m : ℕ} {Lam : List Chk} (h : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < m) (j' : ℕ) :
    (Lam.getD j' []).Nodup ∧ ∀ x ∈ Lam.getD j' [], x < m := by
  rcases Nat.lt_or_ge j' Lam.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ hj]
    exact ⟨List.nodup_nil, fun x hx => absurd hx List.not_mem_nil⟩

/-- A list without repetition of numbers below m has at most m members. -/
theorem length_le_of_nodup {L : List ℕ} (hL : L.Nodup) {m : ℕ} (hm : ∀ x ∈ L, x < m) : L.length ≤ m := by
  rw [← List.toFinset_card_of_nodup hL, ← Finset.card_range m]
  exact Finset.card_le_card fun x hx => Finset.mem_range.2 (hm x (List.mem_toFinset.1 hx))

/-! ### The three layers -/

section Layers

variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}

/-- The variables of the clause number x of ψ are below n. -/
theorem getD_lt (hψ : WfL k n [ψ]) (x : ℕ) : ∀ l ∈ ψ.getD x [], l.1 < n := by
  rcases Nat.lt_or_ge x ψ.length with hx | hx
  · rw [List.getD_eq_getElem _ _ hx]
    exact (hψ ψ List.mem_cons_self _ (List.getElem_mem hx)).2.2
  · rw [List.getD_eq_default _ _ hx]
    exact fun l hl => absurd hl List.not_mem_nil

/-- Every clause of the three layers has 1 to k + 1 literals on the n + r variables. -/
theorem wfL (hm : ψ.length = q.m) (hψ : WfL k n [ψ]) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (e : ℕ) :
    WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] := by
  have h0 : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := hψ ψ List.mem_cons_self
  have h1 : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k + 1 ∧ ∀ l ∈ C, l.1 < n + q.r := fun C hC =>
    ⟨(h0 C hC).1, (h0 C hC).2.1.trans (Nat.le_succ k), fun l hl => ((h0 C hC).2.2 l hl).trans_le (Nat.le_add_right n q.r)⟩
  have hmem : ∀ j' x, x ∈ Lam.getD j' [] → ψ.getD x [] ∈ ψ := fun j' x hx => by
    have hxm : x < ψ.length := hm ▸ (getD_ok hL j').2 x hx
    rw [List.getD_eq_getElem _ _ hxm]
    exact List.getElem_mem hxm
  intro L hLs C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hLs
  rcases hLs with rfl | rfl | rfl
  · exact h1 C hC
  · rw [incL, List.mem_append, List.mem_flatMap] at hC
    rcases hC with ⟨j', hj', hC⟩ | hC
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hC
      have hj'' := List.mem_range.1 hj'
      obtain ⟨-, b, c⟩ := h0 _ (hmem j' x hx)
      refine ⟨by simp, by rw [List.length_append, List.length_singleton]; omega, fun l hl => ?_⟩
      rcases List.mem_append.1 hl with hl | hl
      · exact (c l hl).trans_le (Nat.le_add_right n q.r)
      · rw [List.mem_singleton.1 hl]
        exact Nat.add_lt_add_left (hj''.trans_le hj) n
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hC
      exact h1 _ (hmem j x hx)
  · exact h1 C (List.mem_of_mem_drop hC)

/-- The incidences in which v occurs, check by check. -/
theorem length_occ_incL (n : ℕ) (ψ : Fml) (Lam : List Chk) (j v : ℕ) : (occ (incL n ψ Lam j) v).length =
    ∑ j' ∈ range j, (Lam.getD j' []).countP (fun x => hasV v (ψ.getD x [] ++ [(n + j', false)])) +
      (Lam.getD j []).countP fun x => hasV v (ψ.getD x []) := by
  rw [occ_eq, incL, List.filter_append, List.length_append, length_filter_flatMap_range]
  congr 1
  · refine Finset.sum_congr rfl fun j' _ => ?_
    rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl
  · rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl

/-- The number of the checks 0, …, j that contain the clause x. -/
theorem card_col_le (hnb : 1 ≤ q.nb) (hj : j ≤ q.r) (hT : Tent q (lam q.m Lam)) {x : ℕ} (hx : x < q.m) :
    #{j' ∈ range (j + 1) | x ∈ Lam.getD j' []} ≤ Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1 := by
  have h1 : #{j' ∈ range (j + 1) | x ∈ Lam.getD j' []} ≤ #{j' ∈ range (q.r + 1) | x ∈ Lam.getD j' []} :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)))
  have h2 : #{j' ∈ range (q.r + 1) | x ∈ Lam.getD j' []} ≤ #{j' ∈ range q.r | x ∈ Lam.getD j' []} + 1 := by
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs
    · exact Finset.card_insert_le _ _
    · exact Nat.le_succ _
  have h3 : #{j' ∈ range q.r | x ∈ Lam.getD j' []} = #{j' ∈ range q.r | (⟨x, hx⟩ : Fin q.m) ∈ lam q.m Lam j'} := by
    congr 1
    refine Finset.filter_congr fun j' _ => ?_
    simp [lam]
  have h4 := le_of_two_pow_lt hnb (hT.col ⟨x, hx⟩)
  omega

/-- A variable of ψ occurs in at most Δ·(⌈log₂(16m)⌉ + ⌊3r/(2·nb)⌋ + 1) incidences. -/
theorem occ_incL_le_of_lt (hm : ψ.length = q.m) (hnb : 1 ≤ q.nb) {v : ℕ} (hocc : (occ ψ v).length ≤ Δ) (hj : j ≤ q.r)
    (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (hT : Tent q (lam q.m Lam)) (hv : v < n) :
    (occ (incL n ψ Lam j) v).length ≤ Δ * (Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1) := by
  have e1 : ∀ j' x, hasV v (ψ.getD x [] ++ [(n + j', false)]) = hasV v (ψ.getD x []) := fun j' x => by
    have h : (n + j' == v) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    rw [hasV_append_singleton, h, Bool.or_false]
  have e2 : ∀ j', ((Lam.getD j' []).countP fun x => hasV v (ψ.getD x [])) =
      #{x ∈ range q.m | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} := fun j' =>
    countP_eq_card (getD_ok hL j').1 (getD_ok hL j').2 _
  rw [length_occ_incL]
  simp only [e1]
  rw [← Finset.sum_range_succ fun j' => (Lam.getD j' []).countP fun x => hasV v (ψ.getD x [])]
  simp only [e2]
  have key : ∑ j' ∈ range (j + 1), #{x ∈ range q.m | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} =
      ∑ x ∈ range q.m, #{j' ∈ range (j + 1) | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow fun j' x => x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true
  rw [key]
  have hx : ∀ x ∈ range q.m, #{j' ∈ range (j + 1) | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} ≤
      if hasV v (ψ.getD x []) = true then Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1 else 0 := by
    intro x hx
    split_ifs with hP
    · refine le_trans (Finset.card_le_card ?_) (card_col_le hnb hj hT (Finset.mem_range.1 hx))
      exact fun j' hj' => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj').1, (Finset.mem_filter.1 hj').2.1⟩
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun j' _ h => hP h.2
  refine (Finset.sum_le_sum hx).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, ← hm, ← length_filter_eq_card, ← occ_eq]
  exact Nat.mul_le_mul_right _ hocc

/-- A dummy variable occurs in at most ⌈log₂(16r)⌉ + ⌊3m/(2·nb)⌋ incidences. -/
theorem occ_incL_le_of_ge (hψ : WfL k n [ψ]) (hnb : 1 ≤ q.nb) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m)
    (hT : Tent q (lam q.m Lam)) {v : ℕ} (hv : n ≤ v) :
    (occ (incL n ψ Lam j) v).length ≤ Nat.clog 2 (16 * q.r) + 3 * q.m / (2 * q.nb) := by
  have e0 : ∀ x, hasV v (ψ.getD x []) = false := fun x => hasV_eq_false (getD_lt hψ x) hv
  have e1 : ∀ j', ((Lam.getD j' []).countP fun x => hasV v (ψ.getD x [] ++ [(n + j', false)])) =
      if j' = v - n then (Lam.getD j' []).length else 0 := fun j' => by
    simp only [hasV_append_singleton, e0, Bool.false_or]
    split_ifs with h
    · have h' : (n + j' == v) = true := by
        rw [beq_iff_eq]
        omega
      rw [h', List.countP_true]
    · have h' : (n + j' == v) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      rw [h', List.countP_false]
      rfl
  have e2 : ((Lam.getD j []).countP fun x => hasV v (ψ.getD x [])) = 0 := by
    simp only [e0]
    rw [List.countP_false]
    rfl
  rw [length_occ_incL, e2, add_zero]
  simp only [e1]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · have hr : v - n < q.r := (Finset.mem_range.1 h).trans_le hj
    rw [← card_lam Lam (v - n) (getD_ok hL _).1 (getD_ok hL _).2]
    exact le_of_two_pow_lt hnb (hT.row _ hr)
  · exact Nat.zero_le _

/-- The number of incidences. -/
theorem length_incL (n : ℕ) (ψ : Fml) (Lam : List Chk) (j : ℕ) : (incL n ψ Lam j).length = ∑ j' ∈ range (j + 1), (Lam.getD j' []).length := by
  rw [incL, List.length_append, length_flatMap_range, Finset.sum_range_succ]
  simp only [List.length_map]

/-- There are at most 16·Δ·LD Δ·r + m incidences, if m ≤ 2·Δ·LD Δ·nb. -/
theorem length_incL_le (hnb : 1 ≤ q.nb) (h4 : q.m ≤ 2 * Δ * LD Δ * q.nb) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m)
    (hT : Tent q (lam q.m Lam)) : (incL n ψ Lam j).length ≤ 16 * Δ * LD Δ * q.r + q.m := by
  have h1 : ∑ j' ∈ range (j + 1), (Lam.getD j' []).length ≤ ∑ j' ∈ range (q.r + 1), (Lam.getD j' []).length :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
  have h2 : (Lam.getD q.r []).length ≤ q.m := length_le_of_nodup (getD_ok hL _).1 (getD_ok hL _).2
  have h3 : ∑ j' ∈ range q.r, (Lam.getD j' []).length = ∑ j' ∈ range q.r, #(lam q.m Lam j') :=
    Finset.sum_congr rfl fun j' _ => (card_lam Lam j' (getD_ok hL _).1 (getD_ok hL _).2).symm
  have hq : (0 : ℚ) < q.nb := by exact_mod_cast hnb
  have h5 : ((∑ j' ∈ range q.r, #(lam q.m Lam j') : ℕ) : ℚ) * q.nb < 8 * q.m * q.r + q.nb := by
    have h := mul_lt_mul_of_pos_right hT.inc hq
    have e : (8 * pr q.nb * q.m * q.r + 1) * (q.nb : ℚ) = 8 * q.m * q.r + q.nb := by
      unfold pr
      field_simp
    rwa [e] at h
  have h6 : (∑ j' ∈ range q.r, #(lam q.m Lam j')) * q.nb < 8 * q.m * q.r + q.nb := by exact_mod_cast h5
  have h7 : 8 * q.m * q.r ≤ 16 * Δ * LD Δ * q.r * q.nb := by
    calc 8 * q.m * q.r ≤ 8 * (2 * Δ * LD Δ * q.nb) * q.r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h4)
      _ = 16 * Δ * LD Δ * q.r * q.nb := by ring
  have h8 : (∑ j' ∈ range q.r, #(lam q.m Lam j')) * q.nb < (16 * Δ * LD Δ * q.r + 1) * q.nb := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h9 := Nat.lt_of_mul_lt_mul_right h8
  have h10 : ∑ j' ∈ range (q.r + 1), (Lam.getD j' []).length = ∑ j' ∈ range q.r, (Lam.getD j' []).length + (Lam.getD q.r []).length :=
    Finset.sum_range_succ _ _
  rw [length_incL]
  omega

/-- Δ ≤ Δ·LD Δ. -/
theorem le_mul_LD (Δ : ℕ) : Δ ≤ Δ * LD Δ := by
  rcases Nat.eq_zero_or_pos Δ with rfl | h
  · simp
  · exact Nat.le_mul_of_pos_right _ (Nat.clog_pos (by norm_num) (by omega))

/-- The shape of the three layers, with the bounds as they come out of the state. -/
theorem shape_core (hm : ψ.length = q.m) (hnb : 1 ≤ q.nb) (h3 : q.m ≤ Δ * n) (h4 : q.m ≤ 2 * Δ * LD Δ * q.nb) (hψ : WfL k n [ψ])
    (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (hT : Tent q (lam q.m Lam)) (e : ℕ) :
    WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] ∧
      (∀ v, (occ [ψ, incL n ψ Lam j, ψ.drop e].flatten v).length ≤
        max (Δ * (2 + (Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1))) (Nat.clog 2 (16 * q.r) + 3 * q.m / (2 * q.nb))) ∧
      [ψ, incL n ψ Lam j, ψ.drop e].flatten.length ≤ blkOL Δ * (n + q.r + 1) := by
  have hfl : [ψ, incL n ψ Lam j, ψ.drop e].flatten = ψ ++ (incL n ψ Lam j ++ ψ.drop e) := by simp
  refine ⟨wfL hm hψ hj hL e, fun v => ?_, ?_⟩
  · rw [hfl, occ_eq, List.filter_append, List.filter_append, List.length_append, List.length_append, ← occ_eq, ← occ_eq, ← occ_eq]
    have hd : (occ (ψ.drop e) v).length ≤ (occ ψ v).length := ((List.drop_sublist e ψ).filter _).length_le
    rcases Nat.lt_or_ge v n with hv | hv
    · refine le_trans ?_ (le_max_left _ _)
      have h1 := occ_incL_le_of_lt hm hnb (hocc v) hj hL hT hv
      have h2 := hocc v
      rw [Nat.mul_add]
      omega
    · refine le_trans ?_ (le_max_right _ _)
      have h1 := occ_incL_le_of_ge hψ hnb hj hL hT hv
      have h2 : (occ ψ v).length = 0 := by
        rw [occ_eq, length_filter_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _
        rw [hasV_eq_false (getD_lt hψ x) hv]
        exact Bool.false_ne_true
      omega
  · rw [hfl, List.length_append, List.length_append, List.length_drop, hm]
    have h1 := length_incL_le (n := n) (ψ := ψ) hnb h4 hj hL hT
    have h2 : Δ * n ≤ Δ * LD Δ * n := Nat.mul_le_mul_right n (le_mul_LD Δ)
    have h5 : blkOL Δ * (n + q.r + 1) =
        2 * (Δ * n) + 16 * (Δ * LD Δ * n) + 16 * Δ * LD Δ * q.r + (2 * Δ * (q.r + 1) + 16 * Δ * LD Δ + (n + q.r + 1)) := by
      unfold blkOL
      ring
    rw [h5]
    omega

end Layers

/-- The layers of a state that is tried have the shape that the evaluation asks. -/
theorem stShape : StShape := by
  intro k n Δ q ψ Lam j e hm hnb h3 hr hn hψ hocc hj hL hT
  have hnb1 : 1 ≤ q.nb := by omega
  have h4 : q.m ≤ 2 * Δ * LD Δ * q.nb := by
    calc q.m ≤ Δ * n := h3
      _ ≤ Δ * (2 * (q.nb * LD Δ)) := Nat.mul_le_mul_left _ hn.le
      _ = 2 * Δ * LD Δ * q.nb := by ring
  obtain ⟨a, b, c⟩ := shape_core hm hnb1 h3 h4 hψ hocc hj hL hT e
  refine ⟨a, fun v => (b v).trans ?_, c⟩
  have c1 : Nat.clog 2 (16 * q.m) ≤ Nat.clog 2 (16 * Δ * n) := Nat.clog_mono_right 2 (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h3)
  have c2 : Nat.clog 2 (16 * q.r) ≤ Nat.clog 2 (96 * n) := Nat.clog_mono_right 2 (by omega)
  have c3 : 3 * q.r / (2 * q.nb) ≤ 18 * LD Δ := by
    refine Nat.div_le_of_le_mul ?_
    calc 3 * q.r ≤ 18 * n := by omega
      _ ≤ 18 * (2 * (q.nb * LD Δ)) := Nat.mul_le_mul_left _ hn.le
      _ = 2 * q.nb * (18 * LD Δ) := by ring
  have c4 : 3 * q.m / (2 * q.nb) ≤ 3 * Δ * LD Δ := by
    refine Nat.div_le_of_le_mul ?_
    calc 3 * q.m ≤ 3 * (2 * Δ * LD Δ * q.nb) := Nat.mul_le_mul_left _ h4
      _ = 2 * q.nb * (3 * Δ * LD Δ) := by ring
  unfold occOL colMax rowMax
  exact max_le_max (Nat.mul_le_mul_left _ (by omega)) (by omega)

end ClauseBound.ParityChecks.Shape
