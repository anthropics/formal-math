/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Defs

/-!
# Loads in a tower: one stage

The norm of the loads falls by the factor `ρ` in every stage, up to a small error.
-/

namespace Nc.Tow

open Finset

variable {h b D J r : ℕ} (T : Tower h b D J r)

namespace Tower

/-- The units of type `i` at a chamber. -/
def be {j : ℕ} (i : Fin h) (n : T.Ed j → ℕ) (c : T.X j) : ℕ :=
  ∑ e, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e else 0

/-- The number of end segments on the pair `q` of the vertex `ω`. -/
def nEnd {j : ℕ} (i : Fin h) (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) : ℕ :=
  ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c else 0

/-- The square of the norm of a load on pairs. -/
noncomputable def NN2 (n : Sym2 T.Fl → ℕ) : ℝ :=
  ((b : ℝ) * (b - 1) / 2) * ∑ q : Sym2 T.Fl, if q.IsDiag then 0 else (n q : ℝ) ^ 2

/-- The norm of the loads at stage `j`. -/
noncomputable def kap {j : ℕ} (n : T.Ed j → ℕ) : ℝ :=
  √((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e, (n e : ℝ) ^ 2)

variable {T}

theorem kap_nonneg {j : ℕ} (n : T.Ed j → ℕ) : 0 ≤ T.kap n := Real.sqrt_nonneg _

theorem kap_sq {j : ℕ} (n : T.Ed j → ℕ) :
    T.kap n ^ 2 = (r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e, (n e : ℝ) ^ 2 :=
  Real.sq_sqrt (mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => sq_nonneg _))

theorem card_V {j : ℕ} (hj : j ≤ J) (i : Fin h) : Fintype.card (T.V j i) * b = Fintype.card (T.X j) := by
  rw [Fintype.card_of_bijective (T.vx_co hj i), Fintype.card_prod, T.card_fl]

/-- Cauchy–Schwarz for a sum over few elements. -/
theorem sq_sum_le {κ : Type*} (s : Finset κ) (f : κ → ℝ) {k : ℕ} (hk : s.card ≤ k) :
    (∑ x ∈ s, f x) ^ 2 ≤ k * ∑ x ∈ s, f x ^ 2 := by
  refine (sq_sum_le_card_mul_sum_sq (s := s) (f := f)).trans ?_
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Finset.sum_nonneg fun x _ => sq_nonneg _)

section Stage

variable {j : ℕ} {i : Fin h} {n : T.Ed j → ℕ}

/-- Loads on middle segments. -/
theorem mid_le (hj : j < J) {n' : T.Ed (j + 1) → ℕ}
    (hmid : ∀ e', T.ty e' = i → n' e' ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e) :
    ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), (n' e' : ℝ) ^ 2 ≤
      D * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 := by
  have h1 : ∀ e' ∈ univ.filter (fun e' : T.Ed (j + 1) => T.ty e' = i), (n' e' : ℝ) ^ 2 ≤
      D * ∑ e ∈ univ.filter (fun e => T.πE e = e'), (n e : ℝ) ^ 2 := by
    intro e' he'
    have h2 := hmid e' (mem_filter.1 he').2
    have h3 : (n' e' : ℝ) ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), (n e : ℝ) := by exact_mod_cast h2
    refine (pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2).trans ?_
    exact sq_sum_le _ _ (T.fibre hj e')
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun e : T.Ed j => T.ty e = i)
    (t := univ.filter fun e' : T.Ed (j + 1) => T.ty e' = i) (g := T.πE) (f := fun e => (n e : ℝ) ^ 2)]
  · refine Finset.sum_congr rfl fun e' he' => Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hh
      refine ⟨?_, hh⟩
      rw [← T.π_ty hj e, hh]
      exact (mem_filter.1 he').2
    · exact fun hh => hh.2
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    rw [T.π_ty hj e, he]

/-- Units at chambers. -/
theorem sum_be_sq (hj : j ≤ J) : ∑ c, (T.be i n c : ℝ) ^ 2 ≤
    2 * r * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 := by
  have h1 : ∀ c, (T.be i n c : ℝ) ^ 2 ≤
      r * ∑ e, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then (n e : ℝ) ^ 2 else 0 := by
    intro c
    have e1 : (T.be i n c : ℝ) = ∑ e ∈ univ.filter (fun e => T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c)), (n e : ℝ) := by
      unfold be
      rw [Finset.sum_filter]
      push_cast
      rfl
    rw [e1, ← Finset.sum_filter]
    exact sq_sum_le _ _ (T.deg j hj c i)
  refine (Finset.sum_le_sum fun c _ => h1 c).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ e : T.Ed j, (∑ c, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then (n e : ℝ) ^ 2 else 0) =
      if T.ty e = i then 2 * (n e : ℝ) ^ 2 else 0 := by
    intro e
    by_cases ht : T.ty e = i
    · rw [if_pos ht]
      have h3 : ∀ c, (if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then (n e : ℝ) ^ 2 else 0) =
          (if T.e0 e = c then (n e : ℝ) ^ 2 else 0) + if T.e1 e = c then (n e : ℝ) ^ 2 else 0 := by
        intro c
        have hne := T.e_ne e
        by_cases h0 : T.e0 e = c
        · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
          simp [ht, h0, h1]
        · by_cases h1 : T.e1 e = c <;> simp [ht, h0, h1]
      rw [Finset.sum_congr rfl fun c _ => h3 c, Finset.sum_add_distrib]
      simp
      ring
    · rw [if_neg ht]
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => ht hh.1
  rw [Finset.sum_congr rfl fun e _ => h2 e, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun e _ => ?_)
  split_ifs <;> ring

/-- A pair of a vertex carries the end segments of at most two chambers. -/
theorem card_two (hj : j < J) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    (univ.filter fun c : T.X j => T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q).card ≤ 2 := by
  induction q using Sym2.inductionOn with
  | _ f f' =>
    have h1 : (univ.filter fun c : T.X j => T.πV (T.vx i c) = ω ∧
        s(T.co i (T.host i (T.vx i c)), T.co i c) = s(f, f')).card ≤ ({(f, f'), (f', f)} : Finset (T.Fl × T.Fl)).card := by
      refine card_le_card_of_injOn (fun c => (T.co i (T.host i (T.vx i c)), T.co i c)) ?_ ?_
      · intro c hc
        have := (mem_filter.1 (mem_coe.1 hc)).2.2
        rw [Sym2.eq_iff] at this
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        exact this
      · intro c hc c' hc' heq
        simp only [Prod.mk.injEq] at heq
        have hv := (mem_filter.1 (mem_coe.1 hc)).2.1
        have hv' := (mem_filter.1 (mem_coe.1 hc')).2.1
        have hh : T.host i (T.vx i c) = T.host i (T.vx i c') := by
          apply (T.vx_co (Nat.succ_le_of_lt hj) i).1
          simp only [Prod.mk.injEq]
          refine ⟨?_, heq.1⟩
          rw [T.host_vx hj, T.host_vx hj, hv, hv']
        have hvx := T.host_inj hj i hh
        apply (T.vx_co hj.le i).1
        simp only [Prod.mk.injEq]
        exact ⟨hvx, heq.2⟩
    exact h1.trans card_le_two

/-- Loads of end segments. -/
theorem sum_end_sq (hj : j < J) :
    ∑ ω, ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 ≤ 2 * ∑ c, (T.be i n c : ℝ) ^ 2 := by
  have h1 : ∀ ω q, (T.nEnd i n ω q : ℝ) ^ 2 ≤ 2 * ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q then (T.be i n c : ℝ) ^ 2 else 0 := by
    intro ω q
    have e1 : (T.nEnd i n ω q : ℝ) = ∑ c ∈ univ.filter (fun c : T.X j => T.πV (T.vx i c) = ω ∧
        s(T.co i (T.host i (T.vx i c)), T.co i c) = q), (T.be i n c : ℝ) := by
      unfold nEnd
      rw [Finset.sum_filter]
      push_cast
      rfl
    rw [e1, ← Finset.sum_filter]
    have := sq_sum_le _ (fun c => (T.be i n c : ℝ)) (card_two (T := T) hj ω q)
    exact_mod_cast this
  refine (Finset.sum_le_sum fun ω _ => Finset.sum_le_sum fun q _ => h1 ω q).trans ?_
  simp only [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
  have e2 : ∀ ω, (∑ q : Sym2 T.Fl, ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q then (T.be i n c : ℝ) ^ 2 else 0) =
      ∑ c : T.X j, if T.πV (T.vx i c) = ω then (T.be i n c : ℝ) ^ 2 else 0 := by
    intro ω
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hω : T.πV (T.vx i c) = ω
    · simp [hω]
    · simp [hω]
  rw [Finset.sum_congr rfl fun ω _ => e2 ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

end Stage

/-- Minkowski's inequality, one summand constant. -/
theorem minkowski {κ : Type*} [Fintype κ] (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a) :
    √(∑ x, (f x + a) ^ 2) ≤ √(∑ x, f x ^ 2) + √(Fintype.card κ) * a := by
  have h1 : 0 ≤ ∑ x, f x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hc : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  have hcs : ∑ x, f x ≤ √(Fintype.card κ) * √(∑ x, f x ^ 2) := by
    rw [← Real.sqrt_mul hc]
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset κ)) (f := f)
    rwa [card_univ] at this
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have e1 : ∑ x, (f x + a) ^ 2 = ∑ x, f x ^ 2 + 2 * a * ∑ x, f x + Fintype.card κ * a ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : (√(∑ x, f x ^ 2) + √(Fintype.card κ) * a) ^ 2 =
      ∑ x, f x ^ 2 + 2 * a * (√(Fintype.card κ) * √(∑ x, f x ^ 2)) + Fintype.card κ * a ^ 2 := by
    rw [add_sq, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt hc]
    ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left hcs (by linarith : 0 ≤ 2 * a)
  linarith

theorem alg {C N y k : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hy : 0 ≤ y) (hk : k ^ 2 ≤ N ^ 2 + C * (√8 * N + y) ^ 2) :
    k ≤ √(1 + 8 * C) * N + √C * y := by
  have hS0 : 0 ≤ √(1 + 8 * C) := Real.sqrt_nonneg _
  have hS2 : √(1 + 8 * C) ^ 2 = 1 + 8 * C := Real.sq_sqrt (by linarith)
  have hc0 : 0 ≤ √C := Real.sqrt_nonneg _
  have hc2 : √C ^ 2 = C := Real.sq_sqrt hC
  have h82 : (√8 : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hcross : √C * √8 ≤ √(1 + 8 * C) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hc2, h82]
    linarith
  generalize √(1 + 8 * C) = S at *
  generalize hs : √C = s at *
  generalize (√8 : ℝ) = e at *
  have h0 : 0 ≤ S * N + s * y := by positivity
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  refine hk.trans ?_
  have e1 : C * (e * N + y) ^ 2 = 8 * C * N ^ 2 + 2 * (s * (s * e) * (N * y)) + C * y ^ 2 := by
    have : C * (e * N + y) ^ 2 = e ^ 2 * C * N ^ 2 + 2 * (C * e * (N * y)) + C * y ^ 2 := by ring
    rw [this, h82, ← hc2]
    ring
  have e2 : (S * N + s * y) ^ 2 = (1 + 8 * C) * N ^ 2 + 2 * (s * S * (N * y)) + C * y ^ 2 := by
    have : (S * N + s * y) ^ 2 = S ^ 2 * N ^ 2 + 2 * (s * S * (N * y)) + s ^ 2 * y ^ 2 := by ring
    rw [this, hS2, hc2]
  have h1 : s * (s * e) ≤ s * S := mul_le_mul_of_nonneg_left hcross hc0
  have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hN hy)
  rw [e1, e2]
  linarith

theorem NN2_nonneg (hb : 0 < b) (m : Sym2 T.Fl → ℕ) : 0 ≤ T.NN2 m := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  unfold NN2
  refine mul_nonneg ?_ (Finset.sum_nonneg fun q _ => ?_)
  · have : (0 : ℝ) ≤ b - 1 := by linarith
    positivity
  · split_ifs
    · exact le_rfl
    · exact sq_nonneg _

/-- The norms of the loads of end segments. -/
theorem end_norm {j : ℕ} (hj : j < J) (hb : 0 < b) (hbD : b ≤ 2 * D) {i : Fin h} {n : T.Ed j → ℕ} :
    (Fintype.card (T.X (j + 1)) : ℝ) / b * ∑ ω, √(T.NN2 (T.nEnd i n ω)) ^ 2 ≤
      8 * ((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hDb : (b : ℝ) ≤ 2 * D := by exact_mod_cast hbD
  have hcX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j hj
  rw [hcX]
  have h6 := sum_end_sq (T := T) (n := n) (i := i) hj
  have h7 := sum_be_sq (T := T) (n := n) (i := i) hj.le
  set Pn : ℝ := ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 with hP
  have hP0 : 0 ≤ Pn := Finset.sum_nonneg fun e _ => sq_nonneg _
  set x : ℝ := (Fintype.card (T.X (j + 1)) : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have h1 : ∀ ω, √(T.NN2 (T.nEnd i n ω)) ^ 2 ≤ (b : ℝ) ^ 2 / 2 * ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := by
    intro ω
    rw [Real.sq_sqrt (NN2_nonneg hb _)]
    unfold NN2
    have h2 : (∑ q : Sym2 T.Fl, if q.IsDiag then (0 : ℝ) else (T.nEnd i n ω q : ℝ) ^ 2) ≤
        ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := by
      refine Finset.sum_le_sum fun q _ => ?_
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
    have h3 : (0 : ℝ) ≤ ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
    have h4 : (b : ℝ) * (b - 1) / 2 ≤ (b : ℝ) ^ 2 / 2 := by nlinarith
    have h5 : (0 : ℝ) ≤ (b : ℝ) * (b - 1) / 2 := by
      have : (0 : ℝ) ≤ b - 1 := by linarith
      positivity
    calc _ ≤ (b : ℝ) * (b - 1) / 2 * ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h5
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 h3
  have hrP : (0 : ℝ) ≤ r * x * Pn := by positivity
  calc x / b * ∑ ω, √(T.NN2 (T.nEnd i n ω)) ^ 2 ≤
      x / b * ∑ ω, (b : ℝ) ^ 2 / 2 * ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => h1 ω) (by positivity)
    _ = x * b / 2 * ∑ ω, ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := by
        rw [← Finset.mul_sum]
        field_simp
    _ ≤ x * b / 2 * (2 * (2 * r * Pn)) :=
        mul_le_mul_of_nonneg_left (h6.trans (by linarith)) (by positivity)
    _ = 2 * (r * x * Pn) * b := by ring
    _ ≤ 2 * (r * x * Pn) * (2 * D) := mul_le_mul_of_nonneg_left hDb (by positivity)
    _ = _ := by ring

/-- The new loads at the vertices. -/
theorem other_le {j : ℕ} (hj : j < J) (hr : 0 < r) (hb : 0 < b) (hbD : b ≤ 2 * D) {i : Fin h}
    {n : T.Ed j → ℕ} {n' : T.Ed (j + 1) → ℕ} {C₁ a₁ N : ℝ} (hC : 0 ≤ C₁) (ha : 0 ≤ a₁) (hN0 : 0 ≤ N)
    (hN2 : N ^ 2 = (r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2)
    (t : T.V (j + 1) i → ℕ)
    (hal : ∀ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr (Nat.succ_le_of_lt hj) i).symm (ω, ν)).1 : ℝ) ^ 2 ≤
      C₁ * a₁ ^ 2 * (t ω : ℝ) ^ 2)
    (ht : ∀ ω, a₁ * t ω ≤ √(T.NN2 (T.nEnd i n ω)) + a₁) :
    (r : ℝ) * Fintype.card (T.X (j + 1)) / 2 * ∑ e' ∈ univ.filter (fun e' => ¬ T.ty e' = i), (n' e' : ℝ) ^ 2 ≤
      C₁ * (√8 * N + a₁ * (Fintype.card (T.X (j + 1)) / b)) ^ 2 := by
  have hj' := Nat.succ_le_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hfsq := end_norm (T := T) (n := n) (i := i) hj hb hbD
  rw [← hN2] at hfsq
  set x : ℝ := (Fintype.card (T.X (j + 1)) : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hcV : (Fintype.card (T.V (j + 1) i) : ℝ) = x / b := by
    rw [hx, eq_div_iff hbR.ne']; exact_mod_cast card_V hj' i
  have hxb : 0 ≤ x / b := by positivity
  set f : T.V (j + 1) i → ℝ := fun ω => √(T.NN2 (T.nEnd i n ω)) with hf
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => Real.sqrt_nonneg _
  have e1 : ∑ e' ∈ univ.filter (fun e' : T.Ed (j + 1) => ¬ T.ty e' = i), (n' e' : ℝ) ^ 2 =
      ∑ ω, ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 := by
    rw [← Fintype.sum_prod_type' (f := fun ω ν => (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2)]
    rw [← Equiv.sum_comp (T.nr hj' i) (fun p => (n' ((T.nr hj' i).symm p).1 : ℝ) ^ 2)]
    simp only [Equiv.symm_apply_apply]
    exact (Finset.sum_subtype (univ.filter fun e' : T.Ed (j + 1) => ¬ T.ty e' = i) (p := fun e' => T.ty e' ≠ i)
      (by simp) fun e' => (n' e' : ℝ) ^ 2)
  rw [e1]
  have h1 : ∀ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 ≤ C₁ * (f ω + a₁) ^ 2 := by
    intro ω
    refine (hal ω).trans ?_
    have h2 : (a₁ * (t ω : ℝ)) ^ 2 ≤ (f ω + a₁) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg ha (Nat.cast_nonneg _)) (ht ω) 2
    calc C₁ * a₁ ^ 2 * (t ω : ℝ) ^ 2 = C₁ * (a₁ * (t ω : ℝ)) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hC
  have h3 : (r : ℝ) * x / 2 * ∑ ω, ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 =
      x / b * ∑ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 := by
    rw [← Finset.mul_sum]
    field_simp
  rw [h3]
  have h4 : x / b * ∑ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 ≤
      C₁ * (x / b * ∑ ω, (f ω + a₁) ^ 2) := by
    calc _ ≤ x / b * ∑ ω, C₁ * (f ω + a₁) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => h1 ω) hxb
      _ = _ := by rw [← Finset.mul_sum]; ring
  refine h4.trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hs0 : 0 ≤ ∑ ω, (f ω + a₁) ^ 2 := Finset.sum_nonneg fun ω _ => sq_nonneg _
  have h5 : √(x / b * ∑ ω, (f ω + a₁) ^ 2) ≤ √8 * N + a₁ * (x / b) := by
    rw [Real.sqrt_mul hxb]
    have h6 := minkowski f hf0 ha
    rw [hcV] at h6
    have h7 := mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg (x / b))
    refine h7.trans ?_
    rw [mul_add, ← Real.sqrt_mul hxb, ← mul_assoc, Real.mul_self_sqrt hxb]
    have h8 : √(x / b * ∑ ω, f ω ^ 2) ≤ √8 * N := by
      rw [← Real.sqrt_sq hN0, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hfsq
    linarith
  calc x / b * ∑ ω, (f ω + a₁) ^ 2 = √(x / b * ∑ ω, (f ω + a₁) ^ 2) ^ 2 :=
        (Real.sq_sqrt (mul_nonneg hxb hs0)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2

/-- **One stage.** -/
theorem load_step {j : ℕ} (hj : j < J) (hr : 0 < r) (hb : 0 < b) (hbD : b ≤ 2 * D) {i : Fin h}
    {n : T.Ed j → ℕ} {n' : T.Ed (j + 1) → ℕ} {C₁ a₁ ρ : ℝ} (hC : 0 ≤ C₁) (ha : 0 ≤ a₁) (hρ : 0 ≤ ρ)
    (hρ1 : 1 + 8 * C₁ ≤ ρ ^ 2 * h)
    (hi : (h : ℝ) * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 ≤ ∑ e, (n e : ℝ) ^ 2)
    (hmid : ∀ e', T.ty e' = i → n' e' ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e)
    (t : T.V (j + 1) i → ℕ)
    (hal : ∀ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr (Nat.succ_le_of_lt hj) i).symm (ω, ν)).1 : ℝ) ^ 2 ≤
      C₁ * a₁ ^ 2 * (t ω : ℝ) ^ 2)
    (ht : ∀ ω, a₁ * t ω ≤ √(T.NN2 (T.nEnd i n ω)) + a₁) :
    T.kap n' ≤ ρ * T.kap n + √C₁ * a₁ / b * Fintype.card (T.X (j + 1)) := by
  have hcX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j hj
  have hP0 : 0 ≤ ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  have hA : (0 : ℝ) ≤ (r : ℝ) * Fintype.card (T.X j) / 2 := by positivity
  have hN0 := Real.sqrt_nonneg ((r : ℝ) * Fintype.card (T.X j) / 2 *
    ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2)
  have hN2 := Real.sq_sqrt (mul_nonneg hA hP0)
  set N : ℝ := √((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) with hN
  have hother := other_le hj hr hb hbD hC ha hN0 hN2 t hal ht
  have hm' : (r : ℝ) * Fintype.card (T.X (j + 1)) / 2 *
      ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), (n' e' : ℝ) ^ 2 ≤ N ^ 2 := by
    rw [hN2, hcX]
    have := mul_le_mul_of_nonneg_left (mid_le hj hmid)
      (by positivity : 0 ≤ (r : ℝ) * Fintype.card (T.X (j + 1)) / 2)
    refine this.trans (le_of_eq ?_)
    ring
  have hsum : ∑ e', (n' e' : ℝ) ^ 2 = ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), (n' e' : ℝ) ^ 2 +
      ∑ e' ∈ univ.filter (fun e' => ¬ T.ty e' = i), (n' e' : ℝ) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hk2 : T.kap n' ^ 2 ≤ N ^ 2 + C₁ * (√8 * N + a₁ * (Fintype.card (T.X (j + 1)) / b)) ^ 2 := by
    rw [kap_sq, hsum, mul_add]
    exact add_le_add hm' hother
  have hkap := alg hC hN0 (by positivity) hk2
  have hSN : √(1 + 8 * C₁) * N ≤ ρ * T.kap n := by
    have h0 : 0 ≤ ρ * T.kap n := mul_nonneg hρ (kap_nonneg n)
    refine (abs_le_of_sq_le_sq' ?_ h0).2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + 8 * C₁), hN2, kap_sq]
    calc (1 + 8 * C₁) * ((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2)
        ≤ (ρ ^ 2 * h) * ((r : ℝ) * Fintype.card (T.X j) / 2 *
          ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hA hP0)
      _ = ρ ^ 2 * ((r : ℝ) * Fintype.card (T.X j) / 2) *
          (h * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) := by ring
      _ ≤ ρ ^ 2 * ((r : ℝ) * Fintype.card (T.X j) / 2) * ∑ e, (n e : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hi (mul_nonneg (sq_nonneg _) hA)
      _ = _ := by ring
  have e3 : √C₁ * (a₁ * (Fintype.card (T.X (j + 1)) / b)) = √C₁ * a₁ / b * Fintype.card (T.X (j + 1)) := by ring
  linarith

end Tower

end Nc.Tow
