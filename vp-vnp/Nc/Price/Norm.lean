/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Price.LawF

/-!
# Norms of loads

For the proof of Theorem thm:laws (`Paper/Laws.lean`): the norms ‖n‖² = Σ n_e²/α e of loads, and, if
Σ_e α e·w(e)² ≤ Σ_ν β ν·w(ν)², a new load of norm ≤ (1+η)·S·R that costs at least as much as S times an old load of
norm ≤ R.
-/

namespace Nc.Price

open Finset

section Norm

variable {E : Type} [Fintype E]

/-- The norm of a load: √(Σ n_e²/α e). -/
noncomputable def nrm (α : E → ℝ) (n : E → ℝ) : ℝ := √(∑ e, n e ^ 2 / α e)

theorem nrm_eq_norm (α : E → ℝ) (hα : ∀ e, 0 < α e) (n : E → ℝ) :
    nrm α n = ‖(WithLp.toLp 2 fun e => n e / √(α e) : EuclideanSpace ℝ E)‖ := by
  rw [EuclideanSpace.norm_eq, nrm]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (hα e).le]

theorem nrm_nonneg (α : E → ℝ) (n : E → ℝ) : 0 ≤ nrm α n := Real.sqrt_nonneg _

theorem nrm_add_le (α : E → ℝ) (hα : ∀ e, 0 < α e) (n n' : E → ℝ) :
    nrm α (fun e => n e + n' e) ≤ nrm α n + nrm α n' := by
  rw [nrm_eq_norm α hα, nrm_eq_norm α hα, nrm_eq_norm α hα]
  refine le_trans (le_of_eq ?_) (norm_add_le _ _)
  congr 1
  ext e
  simp [add_div]

theorem nrm_smul (α : E → ℝ) {c : ℝ} (hc : 0 ≤ c) (n : E → ℝ) :
    nrm α (fun e => c * n e) = c * nrm α n := by
  rw [nrm, nrm]
  have : ∑ e, (c * n e) ^ 2 / α e = c ^ 2 * ∑ e, n e ^ 2 / α e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [mul_pow, mul_div_assoc]
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem nrm_mono (α : E → ℝ) (hα : ∀ e, 0 < α e) {n n' : E → ℝ} (h0 : ∀ e, 0 ≤ n e)
    (h : ∀ e, n e ≤ n' e) : nrm α n ≤ nrm α n' :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun e _ =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (h0 e) (h e) 2) (hα e).le)

theorem nrm_zero (α : E → ℝ) : nrm α (fun _ => 0) = 0 := by simp [nrm]

theorem nrm_sum_le {B : Type*} (s : Finset B) (α : E → ℝ) (hα : ∀ e, 0 < α e) (n : B → E → ℝ) :
    nrm α (fun e => ∑ β ∈ s, n β e) ≤ ∑ β ∈ s, nrm α (n β) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nrm_zero]
  | insert β s hβ ih =>
    simp only [Finset.sum_insert hβ]
    exact (nrm_add_le α hα _ _).trans (add_le_add le_rfl ih)

theorem le_nrm (α : E → ℝ) (hα : ∀ e, 0 < α e) (n : E → ℝ) (e : E) : n e ≤ nrm α n * √(α e) := by
  have h1 : n e ^ 2 / α e ≤ ∑ e, n e ^ 2 / α e :=
    Finset.single_le_sum (f := fun e => n e ^ 2 / α e)
      (fun e _ => div_nonneg (sq_nonneg _) (hα e).le) (Finset.mem_univ e)
  rw [div_le_iff₀ (hα e)] at h1
  rw [nrm, ← Real.sqrt_mul' _ (hα e).le]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

/-- Cauchy–Schwarz. -/
theorem sum_mul_le_nrm (α : E → ℝ) (hα : ∀ e, 0 < α e) (n w : E → ℝ) :
    ∑ e, n e * w e ≤ nrm α n * √(∑ e, α e * w e ^ 2) := by
  rw [nrm, ← Real.sqrt_mul (Finset.sum_nonneg fun e _ => div_nonneg (sq_nonneg _) (hα e).le)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e => n e / √(α e))
    (fun e => √(α e) * w e)
  have e1 : ∀ e, n e / √(α e) * (√(α e) * w e) = n e * w e := fun e => by
    have := (Real.sqrt_pos.2 (hα e)).ne'
    field_simp
  have e2 : ∀ e, (n e / √(α e)) ^ 2 = n e ^ 2 / α e := fun e => by
    rw [div_pow, Real.sq_sqrt (hα e).le]
  have e3 : ∀ e, (√(α e) * w e) ^ 2 = α e * w e ^ 2 := fun e => by
    rw [mul_pow, Real.sq_sqrt (hα e).le]
  simpa only [e1, e2, e3] using h

end Norm

/-- Natural loads of bounded norm: a finite set. -/
def Loads {N : Type} [Fintype N] (β : N → ℝ) (r : ℝ) : Type :=
  {x : N → ℕ // nrm β (fun ν => (x ν : ℝ)) ≤ r}

theorem finite_loads {N : Type} [Fintype N] (β : N → ℝ) (hβ : ∀ ν, 0 < β ν) (r : ℝ) :
    Finite (Loads β r) := by
  have : ({x : N → ℕ | nrm β (fun ν => (x ν : ℝ)) ≤ r} : Set (N → ℕ)).Finite := by
    refine (Set.Finite.pi' fun ν : N => Set.finite_Iic ⌊r * √(β ν)⌋₊).subset ?_
    intro x hx ν
    refine Nat.le_floor ((le_nrm β hβ (fun ν => (x ν : ℝ)) ν).trans ?_)
    exact mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)
  exact this.to_subtype

/-- One price: if Σα·w² ≤ Σβ·w′² and ‖n‖ ≤ R, then for S large (S·η·R ≥ ‖1‖) there is a natural
load x with ‖x‖ ≤ (1+η)·S·R and Σ S·n·w ≤ Σ x·w′. -/
theorem exists_load {E N : Type} [Fintype E] [Fintype N] (α : E → ℝ) (hα : ∀ e, 0 < α e)
    (β : N → ℝ) (hβ : ∀ ν, 0 < β ν) (w : E → ℝ) (w' : N → ℝ) (hw' : ∀ ν, 0 ≤ w' ν)
    (h : ∑ e, α e * w e ^ 2 ≤ ∑ ν, β ν * w' ν ^ 2) (n : E → ℕ) {R η : ℝ} (hR : 0 ≤ R)
    (hη : 0 ≤ η) (hn : nrm α (fun e => (n e : ℝ)) ≤ R) (S : ℕ) (hS : nrm β (fun _ => 1) ≤ S * η * R) :
    ∃ x : N → ℕ, nrm β (fun ν => (x ν : ℝ)) ≤ (1 + η) * S * R ∧
      ∑ e, ((S * n e : ℕ) : ℝ) * w e ≤ ∑ ν, (x ν : ℝ) * w' ν := by
  set W := √(∑ ν, β ν * w' ν ^ 2) with hW
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hQ0 : 0 ≤ ∑ ν, β ν * w' ν ^ 2 :=
    Finset.sum_nonneg fun ν _ => mul_nonneg (hβ ν).le (sq_nonneg _)
  have hWsq : W ^ 2 = ∑ ν, β ν * w' ν ^ 2 := Real.sq_sqrt hQ0
  have h1 : ∑ e, ((S * n e : ℕ) : ℝ) * w e ≤ S * R * W := by
    have e1 : ∑ e, ((S * n e : ℕ) : ℝ) * w e = S * ∑ e, (n e : ℝ) * w e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by push_cast; ring
    rw [e1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hS0
    refine (sum_mul_le_nrm α hα _ _).trans ?_
    exact mul_le_mul hn (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) hR
  rcases hW0.eq_or_lt with h0 | h0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp only [Nat.cast_zero, nrm_zero]
      positivity
    · rw [← h0, mul_zero] at h1
      simpa using h1
  · refine ⟨fun ν => ⌈S * R / W * (β ν * w' ν)⌉₊, ?_, ?_⟩
    · have h2 : nrm β (fun ν => ((⌈S * R / W * (β ν * w' ν)⌉₊ : ℕ) : ℝ)) ≤
          nrm β (fun ν => S * R / W * (β ν * w' ν) + 1) := by
        refine nrm_mono β hβ (fun ν => Nat.cast_nonneg _) fun ν => ?_
        exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity)
          (mul_nonneg (hβ ν).le (hw' ν)))).le
      have h3 : nrm β (fun ν => β ν * w' ν) = W := by
        rw [nrm, hW]
        congr 1
        refine Finset.sum_congr rfl fun ν _ => ?_
        have := (hβ ν).ne'
        field_simp
      refine h2.trans ((nrm_add_le β hβ _ _).trans ?_)
      rw [nrm_smul β (by positivity), h3, div_mul_cancel₀ _ h0.ne']
      linarith
    · refine h1.trans ?_
      have h4 : S * R * W = ∑ ν, S * R / W * (β ν * w' ν) * w' ν := by
        have : ∀ ν, S * R / W * (β ν * w' ν) * w' ν = S * R / W * (β ν * w' ν ^ 2) :=
          fun ν => by ring
        rw [Finset.sum_congr rfl fun ν _ => this ν, ← Finset.mul_sum, ← hWsq]
        field_simp
      rw [h4]
      exact Finset.sum_le_sum fun ν _ => mul_le_mul_of_nonneg_right (Nat.le_ceil _) (hw' ν)

end Nc.Price
