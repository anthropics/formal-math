/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Count.lean — the zero-count sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "It remains to bound ∑_{γ∉I'} m_ρ D⁻³ (zeros counted with multiplicity).
Zeros with γ > 2T+D₀: grouping them into γ ∈ (2T+D₀+j, 2T+D₀+j+1], j ≥ 0, this part is at
most ∑_{j≥0} A₀ log(2T+D₀+j+4)(D₀+j)⁻³ ≤ (3/2)A₀ log(4T) D₀⁻² for T large (split at j = T
and use D₀ ≥ 2). Zeros with 0 < γ < T−D₀ contribute likewise at most (3/2)A₀ log(4T)D₀⁻²,
and zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³
≪ T⁻² log T. Altogether ∑_{γ∉I'} m_ρ D⁻³ ≤ 4A₀ log(4T) D₀⁻² for T ≥ T₀."

We prove the bound for every FINITE sub-family of tail zeros (which yields both the
summability and the bound for the full series downstream), with the explicit absolute
threshold T₀ of Zeta23/Tail/Basic.lean. Only the final constant 4 is load-bearing (it is
the 4 in θ₀); we do not follow the paper's intermediate 3/2 + 3/2 + o(1) split. Our
grouping: unit windows indexed by the integer distance j from the nearer endpoint of
I = [T,2T] (lower side: T−j−1 < γ ≤ T−j, which also covers ALL γ ≤ 0; upper side:
2T+j < γ ≤ 2T+j+1), each window weighted by max(D₀, j)⁻³ and counted by the two-sided
local count ≤ A₀ log(2T+4+j); integrals are replaced by telescoping sums.
-/
import Zeta23.Tail.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-! #### Telescoping sums replacing ∫ x⁻³ and ∫ x⁻² -/

lemma inv_pow_three_step {a : ℝ} (ha : 0 < a) :
    ((a + 1) ^ 3)⁻¹ ≤ ((a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹) / 2 := by
  rw [← sub_nonneg]
  have key : ((a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹) / 2 - ((a + 1) ^ 3)⁻¹
      = (3 * a + 1) / (2 * a ^ 2 * (a + 1) ^ 3) := by
    field_simp; ring
  rw [key]; positivity

lemma inv_pow_two_step {a : ℝ} (ha : 0 < a) :
    ((a + 1) ^ 2)⁻¹ ≤ a⁻¹ - (a + 1)⁻¹ := by
  rw [← sub_nonneg]
  have key : a⁻¹ - (a + 1)⁻¹ - ((a + 1) ^ 2)⁻¹ = 1 / (a * (a + 1) ^ 2) := by
    field_simp; ring
  rw [key]; positivity

lemma sum_inv_pow_three_le_telescope {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range (n + 1), ((D + i) ^ 3)⁻¹ ≤ (D ^ 3)⁻¹ + ((D ^ 2)⁻¹ - ((D + n) ^ 2)⁻¹) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_three_step (a := D + n) (by positivity)
    have e : (D + ((n + 1 : ℕ) : ℝ)) = D + n + 1 := by push_cast; ring
    rw [e]
    calc _ ≤ (D ^ 3)⁻¹ + ((D ^ 2)⁻¹ - ((D + n) ^ 2)⁻¹) / 2
          + (((D + n) ^ 2)⁻¹ - ((D + n + 1) ^ 2)⁻¹) / 2 := add_le_add ih hstep
      _ = _ := by ring

lemma sum_inv_pow_two_le_telescope {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range (n + 1), ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + (D⁻¹ - (D + n)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_two_step (a := D + n) (by positivity)
    have e : (D + ((n + 1 : ℕ) : ℝ)) = D + n + 1 := by push_cast; ring
    rw [e]
    calc _ ≤ (D ^ 2)⁻¹ + (D⁻¹ - (D + n)⁻¹) + ((D + n)⁻¹ - (D + n + 1)⁻¹) :=
          add_le_add ih hstep
      _ = _ := by ring

/-- ∑_{i<n} (D + i)⁻³ ≤ D⁻³ + D⁻²/2 for D > 0 (any n). -/
lemma sum_inv_pow_three_le {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range n, ((D + i) ^ 3)⁻¹ ≤ (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2 := by
  cases n with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ n =>
    refine (sum_inv_pow_three_le_telescope hD n).trans ?_
    have : 0 ≤ ((D + n) ^ 2)⁻¹ := by positivity
    linarith

/-- ∑_{i<n} (D + i)⁻² ≤ D⁻² + D⁻¹ for D > 0 (any n). -/
lemma sum_inv_pow_two_le {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range n, ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + D⁻¹ := by
  cases n with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ n =>
    refine (sum_inv_pow_two_le_telescope hD n).trans ?_
    have : 0 ≤ (D + n)⁻¹ := by positivity
    linarith

/-- log(B + j) ≤ log B + j/B. -/
lemma log_add_le_log_add_div {B j : ℝ} (hB : 0 < B) (hj : 0 ≤ j) :
    Real.log (B + j) ≤ Real.log B + j / B := by
  have e : B + j = B * (1 + j / B) := by field_simp
  rw [e, Real.log_mul hB.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + j / B by positivity)
  linarith

/-! #### Summing the window weights -/

/-- The window weights: for a finite set F of window indices j with j + 1 ≥ D₀ (D₀ ≥ 2),
∑_{j∈F} max(D₀,j)⁻³ · log(B + j) ≤ (2D₀⁻³ + D₀⁻²/2)·log B + (2D₀⁻² + D₀⁻¹)/B. -/
lemma sum_window_weights_le (F : Finset ℕ) {B D₀ : ℝ} (hB : 1 ≤ B) (hD₀ : 2 ≤ D₀)
    (hF : ∀ j ∈ F, D₀ ≤ (j : ℝ) + 1) :
    ∑ j ∈ F, ((max D₀ j) ^ 3)⁻¹ * Real.log (B + j)
      ≤ (2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B := by
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D₀ := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  set g : ℕ → ℝ := fun j => ((max D₀ j) ^ 3)⁻¹ * Real.log (B + j) with hg
  have hg_nn : ∀ j, 0 ≤ g j := fun j => by
    have : 1 ≤ B + j := by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg this)
  -- F ⊆ Ico J₀ N with J₀ := ⌈D₀⌉₊ − 1.
  set J₀ : ℕ := ⌈D₀⌉₊ - 1 with hJ₀
  have hceil : 1 ≤ ⌈D₀⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hJ₀succ : J₀ + 1 = ⌈D₀⌉₊ := Nat.sub_add_cancel hceil
  have hJ₀le : (J₀ : ℝ) ≤ D₀ := by
    have h1 : ((J₀ + 1 : ℕ) : ℝ) = ⌈D₀⌉₊ := by rw [hJ₀succ]
    have h2 : (⌈D₀⌉₊ : ℝ) < D₀ + 1 := Nat.ceil_lt_add_one hD0.le
    push_cast at h1; linarith
  have hJ₀ge : ∀ i : ℕ, D₀ + i ≤ ((J₀ + 1 + i : ℕ) : ℝ) := fun i => by
    rw [hJ₀succ]; push_cast; linarith [Nat.le_ceil D₀]
  set N : ℕ := F.sup id + 1
  have hsub : F ⊆ Finset.Ico J₀ N := by
    intro j hj
    rw [Finset.mem_Ico]
    refine ⟨?_, Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩
    have : ⌈D₀⌉₊ ≤ j + 1 := Nat.ceil_le.mpr (by exact_mod_cast hF j hj)
    omega
  calc ∑ j ∈ F, g j
      ≤ ∑ j ∈ Finset.Ico J₀ N, g j :=
        sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hg_nn j
    _ = ∑ i ∈ range (N - J₀), g (J₀ + i) := Finset.sum_Ico_eq_sum_range _ _ _
    _ ≤ _ := ?_
  rcases Nat.eq_zero_or_eq_succ_pred (N - J₀) with h0 | hsucc
  · rw [h0, sum_range_zero]; positivity
  set n := (N - J₀).pred
  rw [hsucc, sum_range_succ']
  -- the first window j = J₀ ≤ D₀: weight D₀⁻³, log(B + J₀) ≤ log B + D₀/B.
  have hfirst : g (J₀ + 0) ≤ (D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B := by
    simp only [hg, add_zero]
    have hmax : max D₀ (J₀ : ℝ) = D₀ := max_eq_left hJ₀le
    rw [hmax]
    have hl : Real.log (B + J₀) ≤ Real.log B + D₀ / B :=
      (log_add_le_log_add_div hB0 (Nat.cast_nonneg _)).trans
        (by gcongr)
    calc (D₀ ^ 3)⁻¹ * Real.log (B + J₀) ≤ (D₀ ^ 3)⁻¹ * (Real.log B + D₀ / B) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp
  -- the windows j = J₀ + 1 + i ≥ D₀ + i: weight j⁻³, log(B+j) ≤ log B + j/B.
  have hrest : ∀ i ∈ range n, g (J₀ + (i + 1))
      ≤ ((D₀ + i) ^ 3)⁻¹ * Real.log B + ((D₀ + i) ^ 2)⁻¹ / B := by
    intro i _
    simp only [hg]
    have hji : D₀ + i ≤ ((J₀ + (i + 1) : ℕ) : ℝ) := by
      have := hJ₀ge i; rw [show J₀ + 1 + i = J₀ + (i + 1) by ring] at this; exact this
    set j : ℝ := ((J₀ + (i + 1) : ℕ) : ℝ) with hj
    have hDi : 0 < D₀ + i := by positivity
    have hjpos : 0 < j := lt_of_lt_of_le hDi hji
    have hmax : max D₀ j = j := max_eq_right (by
      have := (Nat.cast_nonneg i : (0:ℝ) ≤ i); linarith)
    rw [hmax]
    have hl : Real.log (B + j) ≤ Real.log B + j / B :=
      log_add_le_log_add_div hB0 hjpos.le
    calc (j ^ 3)⁻¹ * Real.log (B + j) ≤ (j ^ 3)⁻¹ * (Real.log B + j / B) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = (j ^ 3)⁻¹ * Real.log B + (j ^ 2)⁻¹ / B := by field_simp
      _ ≤ ((D₀ + i) ^ 3)⁻¹ * Real.log B + ((D₀ + i) ^ 2)⁻¹ / B := by
          gcongr
  calc ∑ i ∈ range n, g (J₀ + (i + 1)) + g (J₀ + 0)
      ≤ ∑ i ∈ range n, (((D₀ + i) ^ 3)⁻¹ * Real.log B + ((D₀ + i) ^ 2)⁻¹ / B)
        + ((D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B) := add_le_add (sum_le_sum hrest) hfirst
    _ = (∑ i ∈ range n, ((D₀ + i) ^ 3)⁻¹) * Real.log B
        + (∑ i ∈ range n, ((D₀ + i) ^ 2)⁻¹) / B
        + ((D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B) := by
          rw [sum_add_distrib, sum_mul, sum_div]
    _ ≤ ((D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + ((D₀ ^ 2)⁻¹ + D₀⁻¹) / B
        + ((D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B) := by
          gcongr
          · exact sum_inv_pow_three_le hD0 n
          · exact sum_inv_pow_two_le hD0 n
    _ = _ := by ring

/-! #### One side of the tail, abstractly -/

/-- One side of the tail: zeros at (signed) distance x_ρ ≥ D₀ beyond an endpoint of I,
grouped by an integer key with key ≤ x ≤ key + 1, each group counted by A₀ log(B + key). -/
lemma one_side_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (m : ι → ℕ) (key : ι → ℕ)
    {A₀ B D₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB : 1 ≤ B) (hD₀ : 2 ≤ D₀)
    (hx : ∀ ρ ∈ s, D₀ ≤ x ρ) (hkey_le : ∀ ρ ∈ s, (key ρ : ℝ) ≤ x ρ)
    (hkey_ge : ∀ ρ ∈ s, x ρ ≤ key ρ + 1)
    (hcount : ∀ j : ℕ, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ A₀ * Real.log (B + j)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
      ≤ A₀ * ((2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B
          + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B) := by
  have hD0 : 0 < D₀ := by linarith
  rw [← sum_fiberwise_of_maps_to (g := key) (t := s.image key)
    (fun ρ hρ => mem_image_of_mem key hρ)]
  have hfiber : ∀ j ∈ s.image key,
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
        ≤ A₀ * (((max D₀ j) ^ 3)⁻¹ * Real.log (B + j)) := by
    intro j _
    have hM : 0 < max D₀ (j : ℝ) := lt_max_of_lt_left hD0
    calc ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
        ≤ ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) * ((max D₀ j) ^ 3)⁻¹ := by
          apply sum_le_sum
          intro ρ hρ
          simp only [mem_filter] at hρ
          obtain ⟨hρs, hρj⟩ := hρ
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply inv_anti₀ (pow_pos hM 3)
          apply pow_le_pow_left₀ hM.le
          refine max_le (hx ρ hρs) ?_
          have := hkey_le ρ hρs
          rw [hρj] at this
          exact this
      _ = ((max D₀ j) ^ 3)⁻¹ * ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) := by
          rw [mul_sum]
          exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ ((max D₀ j) ^ 3)⁻¹ * (A₀ * Real.log (B + j)) :=
          mul_le_mul_of_nonneg_left (hcount j) (by positivity)
      _ = _ := by ring
  refine (sum_le_sum hfiber).trans ?_
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hA₀
  apply sum_window_weights_le _ hB hD₀
  intro j hj
  obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hj
  exact (hx ρ hρ).trans (hkey_ge ρ hρ)

/-! #### Numerics at T ≥ T₀ -/

lemma one_le_log_four_mul {T : ℝ} (hT : T₀ ≤ T) : 1 ≤ Real.log (4 * T) := by
  have hT' : (300 : ℝ) ≤ T := hT
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The window-weight total, doubled (two sides), is ≤ 4 log(4T)/T for T ≥ T₀. -/
lemma two_sides_numeric {T : ℝ} (hT : T₀ ≤ T) :
    2 * ((2 * (Real.sqrt T ^ 3)⁻¹ + (Real.sqrt T ^ 2)⁻¹ / 2) * Real.log (2 * T + 4)
          + (2 * (Real.sqrt T ^ 2)⁻¹ + (Real.sqrt T)⁻¹) / (2 * T + 4))
      ≤ 4 * Real.log (4 * T) / T := by
  have hT' : (300 : ℝ) ≤ T := hT
  set u := Real.sqrt T with hu
  have hu2 : u ^ 2 = T := Real.sq_sqrt (by linarith)
  have hu17 : 17 ≤ u := by
    rw [hu, Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hu0 : 0 < u := by linarith
  set ℓ := Real.log (4 * T) with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log_four_mul hT
  have hℓ' : Real.log (2 * T + 4) ≤ ℓ :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog_nn : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  rw [← hu2] at hℓ' ⊢
  -- replace log(2T+4) by ℓ and 2T+4 by 2T in the denominator
  have step1 : (2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * Real.log (2 * u ^ 2 + 4)
      ≤ (2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * ℓ :=
    mul_le_mul_of_nonneg_left hℓ' (by positivity)
  have step2 : (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2 + 4) ≤ (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have step3 : 2 * ((2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * ℓ + (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2))
      ≤ 4 * ℓ / u ^ 2 := by
    rw [← sub_nonneg]
    have key : 4 * ℓ / u ^ 2
        - 2 * ((2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * ℓ + (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2))
        = (ℓ * (3 * u ^ 2 - 4 * u) - 2 - u) / u ^ 4 := by
      field_simp
      ring
    rw [key]
    apply div_nonneg _ (by positivity)
    have h34 : 0 ≤ 3 * u ^ 2 - 4 * u := by nlinarith
    have := mul_le_mul_of_nonneg_right hℓ1 h34
    nlinarith
  linarith

/-! #### The zero-count sum -/

/-- **Zero-count sum** (proof of [prop:tail]). For T ≥ T₀ and every finite set s of tail
zeros (γ_ρ ∉ I'), ∑_{ρ∈s} m_ρ · dist(γ_ρ, I)⁻³ ≤ 4 A₀ log(4T) / D₀², with D₀² = T. -/
theorem tail_count_sum_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι) (hs : ∀ ρ ∈ s, InTail T (γ ρ)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ 4 * A₀ * Real.log (4 * T) / T := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := hN.A₀_pos.le
  set D₀ := Real.sqrt T with hD₀def
  have hD₀ : 17 ≤ D₀ := by
    rw [hD₀def, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hD₀2 : (2 : ℝ) ≤ D₀ := by linarith
  have hD₀T : D₀ ≤ T := by
    have : D₀ ^ 2 = T := Real.sq_sqrt hT0
    nlinarith
  set B : ℝ := 2 * T + 4 with hBdef
  have hB : (1 : ℝ) ≤ B := by linarith
  -- the common per-side bound
  set W : ℝ := (2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B
  -- split s into the lower side (γ ≤ T − D₀, includes all γ ≤ 0) and the upper side.
  set slo := s.filter (fun ρ => γ ρ ≤ T - D₀) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T - D₀) with hshi
  have hshi_mem : ∀ ρ ∈ shi, 2 * T + D₀ < γ ρ := by
    intro ρ hρ
    rw [hshi, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h hρ.2
    · exact h
  have hsplit : ∑ ρ ∈ s, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
      = ∑ ρ ∈ slo, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
        + ∑ ρ ∈ shi, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ :=
    (sum_filter_add_sum_filter_not s _ _).symm
  -- log monotonicity helper: A₀ log(|t|+3) ≤ A₀ log(B + j) when |t| + 3 ≤ B + j
  have hlogmono : ∀ (t : ℝ) (j : ℕ), |t| + 3 ≤ B + j →
      A₀ * Real.log (|t| + 3) ≤ A₀ * Real.log (B + j) := fun t j h =>
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h) hA₀
  ---------------- lower side: x = T − γ, key = ⌊T − γ⌋₊ ----------------
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ A₀ * W := by
    have hmem : ∀ ρ ∈ slo, γ ρ ≤ T - D₀ := fun ρ hρ => (mem_filter.mp hρ).2
    have e : ∀ ρ ∈ slo, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
        = (m ρ : ℝ) * ((T - γ ρ) ^ 3)⁻¹ := fun ρ hρ => by
      rw [distI_of_le hT0 (by linarith [hmem ρ hρ])]
    rw [sum_congr rfl e]
    apply one_side_sum_le slo (fun ρ => T - γ ρ) m (fun ρ => ⌊T - γ ρ⌋₊) hA₀ hB hD₀2
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ; exact Nat.floor_le (by linarith [hmem ρ hρ])
    · intro ρ hρ; exact (Nat.lt_floor_add_one _).le
    · intro j
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmono _ _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [hmem ρ hρs]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have : |T - j - 1| ≤ T + j + 1 := by
          rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
        rw [hBdef]; linarith
  ---------------- upper side: x = γ − 2T, key = ⌈γ − 2T⌉₊ − 1 ----------------
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ A₀ * W := by
    have hmem := hshi_mem
    have e : ∀ ρ ∈ shi, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
        = (m ρ : ℝ) * ((γ ρ - 2 * T) ^ 3)⁻¹ := fun ρ hρ => by
      rw [distI_of_ge hT0 (by linarith [hmem ρ hρ])]
    rw [sum_congr rfl e]
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [hmem ρ hρ])
    have hcast : ∀ ρ ∈ shi, (((⌈γ ρ - 2 * T⌉₊ - 1 : ℕ) : ℝ)) = ⌈γ ρ - 2 * T⌉₊ - 1 :=
      fun ρ hρ => by rw [Nat.cast_sub (hceil1 ρ hρ)]; simp
    apply one_side_sum_le shi (fun ρ => γ ρ - 2 * T) m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1)
      hA₀ hB hD₀2
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ
      rw [hcast ρ hρ]
      have := Nat.ceil_lt_add_one (show 0 ≤ γ ρ - 2 * T by linarith [hmem ρ hρ])
      linarith
    · intro ρ hρ
      rw [hcast ρ hρ]
      have := Nat.le_ceil (γ ρ - 2 * T)
      linarith
    · intro j
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmono _ _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · rw [abs_of_nonneg (by positivity), hBdef]; linarith
  ---------------- combine ----------------
  rw [hsplit]
  have hnum := two_sides_numeric hT
  calc _ ≤ A₀ * W + A₀ * W := add_le_add hlo hhi
    _ = A₀ * (2 * W) := by ring
    _ ≤ A₀ * (4 * Real.log (4 * T) / T) := mul_le_mul_of_nonneg_left hnum hA₀
    _ = _ := by ring

/-! #### The boundary count N(I' ∖ I) -/

/-- Counting by unit windows: if every zero of s falls in one of K windows (key < K) and each
window holds total multiplicity ≤ C, then ∑_s m ≤ K·C. -/
lemma sum_mult_le_of_windows {ι : Type*} (s : Finset ι) (m : ι → ℕ) (key : ι → ℕ) (K : ℕ)
    {C : ℝ} (hkey : ∀ ρ ∈ s, key ρ < K)
    (hcount : ∀ j < K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ C) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ K * C := by
  rw [← sum_fiberwise_of_maps_to (g := key) (t := range K)
    (fun ρ hρ => mem_range.mpr (hkey ρ hρ))]
  calc ∑ j ∈ range K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
      ≤ ∑ j ∈ range K, C := sum_le_sum fun j hj => hcount j (mem_range.mp hj)
    _ = K * C := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **Boundary count** N(I' ∖ I) = N(T−D₀, T] + N(2T, 2T+D₀] ≪ D₀·l (used in
[prop:zeroside], [prop:zeroside-rank]: "N(I'∖I) ≪ D₀ l by N(t+1)−N(t) ≤ A₀ log(t+3)").
Explicit form: for T ≥ T₀ and every finite set s of zeros with
γ_ρ ∈ (T−√T, T] ∪ (2T, 2T+√T], ∑_{ρ∈s} m_ρ ≤ 3 · A₀ · √T · log(4T)
(and log(4T) ≤ 2 log(T/2π) = 2l for T ≥ T₀, see log_four_mul_le_two_mul_l). -/
theorem boundary_count_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι)
    (hs : ∀ ρ ∈ s, (T - Real.sqrt T < γ ρ ∧ γ ρ ≤ T)
      ∨ (2 * T < γ ρ ∧ γ ρ ≤ 2 * T + Real.sqrt T)) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := hN.A₀_pos.le
  set D₀ := Real.sqrt T with hD₀def
  have hD₀ : 17 ≤ D₀ := by
    rw [hD₀def, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hD₀T : D₀ ^ 2 = T := Real.sq_sqrt hT0
  have hD₀leT : D₀ + 4 ≤ T := by nlinarith
  set K : ℕ := ⌈D₀⌉₊ with hK
  have hKlt : (K : ℝ) < D₀ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKge : D₀ ≤ K := Nat.le_ceil D₀
  set C : ℝ := A₀ * Real.log (4 * T) with hCdef
  have hlog1 : 1 ≤ Real.log (4 * T) := one_le_log_four_mul hT
  have hC : 0 ≤ C := by positivity
  have hlogmono : ∀ (t : ℝ), |t| + 3 ≤ 4 * T →
      A₀ * Real.log (|t| + 3) ≤ C := fun t h =>
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h) hA₀
  set slo := s.filter (fun ρ => γ ρ ≤ T) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T) with hshi
  have hlo_mem : ∀ ρ ∈ slo, T - D₀ < γ ρ ∧ γ ρ ≤ T := by
    intro ρ hρ
    rw [hslo, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact h
    · exact absurd hρ.2 (by linarith [h.1])
  have hhi_mem : ∀ ρ ∈ shi, 2 * T < γ ρ ∧ γ ρ ≤ 2 * T + D₀ := by
    intro ρ hρ
    rw [hshi, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h.2 hρ.2
    · exact h
  -- lower boundary strip: key = ⌊T − γ⌋₊ < K
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ) ≤ K * C := by
    apply sum_mult_le_of_windows slo m (fun ρ => ⌊T - γ ρ⌋₊) K
    · intro ρ hρ
      have h := hlo_mem ρ hρ
      have : (⌊T - γ ρ⌋₊ : ℝ) < K :=
        lt_of_le_of_lt (Nat.floor_le (by linarith [h.2])) (by linarith [h.1])
      exact_mod_cast this
    · intro j hj
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [(hlo_mem ρ hρs).2]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D₀ + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by linarith)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- upper boundary strip: key = ⌈γ − 2T⌉₊ − 1 < K
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ) ≤ K * C := by
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [(hhi_mem ρ hρ).1])
    apply sum_mult_le_of_windows shi m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1) K
    · intro ρ hρ
      have h := hhi_mem ρ hρ
      have : ⌈γ ρ - 2 * T⌉₊ ≤ K := by rw [hK]; exact Nat.ceil_mono (by linarith [h.2])
      have := hceil1 ρ hρ
      omega
    · intro j hj
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D₀ + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by positivity)]
        linarith
  -- combine: 2·K·C ≤ 2(D₀+1)·A₀ log(4T) ≤ 3 D₀ A₀ log(4T)
  rw [← sum_filter_add_sum_filter_not s (fun ρ => γ ρ ≤ T)]
  have hK' : (K : ℝ) * C ≤ (D₀ + 1) * C := mul_le_mul_of_nonneg_right hKlt.le hC
  have : (2 : ℝ) * ((D₀ + 1) * C) ≤ 3 * A₀ * D₀ * Real.log (4 * T) := by
    rw [hCdef]
    have : 2 * (D₀ + 1) ≤ 3 * D₀ := by linarith
    have hAl : 0 ≤ A₀ * Real.log (4 * T) := hC
    nlinarith
  linarith

end Tail
end Zeta23
