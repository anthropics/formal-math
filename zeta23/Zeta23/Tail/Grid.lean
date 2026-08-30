/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Grid.lean — the grid sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "Let D := dist(γ, I) ≥ D₀. The points τ_k, 0 ≤ k < d, lie in I with
spacing h = 2π/L, so ‖u_ρ‖₂² ≤ C₁²X^{1/2} ∑_{0≤k<d} |γ−τ_k|⁻⁴
≤ C₁²X^{1/2}(D⁻⁴ + (L/2π)·D⁻³/3) ≤ C₁²X^{1/2} L D⁻³ (as D ≥ 1, L ≥ 2)."
Here τ_k := T + k h [eq:fk], h := 2π/L, d := ⌊T/h⌋ so that τ_0,…,τ_{d−1} ∈ [T, 2T).
We prove the pure inequality ∑_{k<d} |γ − τ_k|⁻⁴ ≤ L·D⁻³ (the constant C₁²X^{1/2} is
threaded in Zeta23/Tail.lean), replacing the integral comparison by a telescoping sum.
-/
import Zeta23.Tail.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-- Telescoping replacement for ∫ x⁻⁴: for a > 0, h > 0, h·(a+h)⁻⁴ ≤ (a⁻³ − (a+h)⁻³)/3. -/
lemma inv_pow_four_step {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    h * ((a + h) ^ 4)⁻¹ ≤ ((a ^ 3)⁻¹ - ((a + h) ^ 3)⁻¹) / 3 := by
  have hah : 0 < a + h := by linarith
  rw [← sub_nonneg]
  have key : ((a ^ 3)⁻¹ - ((a + h) ^ 3)⁻¹) / 3 - h * ((a + h) ^ 4)⁻¹
      = (6 * a ^ 2 * h ^ 2 + 4 * a * h ^ 3 + h ^ 4) / (3 * a ^ 3 * (a + h) ^ 4) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Telescoped form: ∑_{k ≤ d} (D + k h)⁻⁴ ≤ D⁻⁴ + (D⁻³ − (D + d h)⁻³)/(3h). -/
lemma sum_inv_pow_four_le_telescope {D h : ℝ} (hD : 0 < D) (hh : 0 < h) (d : ℕ) :
    ∑ k ∈ range (d + 1), ((D + k * h) ^ 4)⁻¹
      ≤ (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_four_step (a := D + d * h) (h := h) (by positivity) hh
    have hstep' : ((D + ((d + 1 : ℕ) : ℝ) * h) ^ 4)⁻¹
        ≤ (((D + d * h) ^ 3)⁻¹ - ((D + ((d + 1 : ℕ) : ℝ) * h) ^ 3)⁻¹) / (3 * h) := by
      have e : D + ((d + 1 : ℕ) : ℝ) * h = D + d * h + h := by push_cast; ring
      rw [e, le_div_iff₀ (by positivity)]
      calc ((D + d * h + h) ^ 4)⁻¹ * (3 * h) = 3 * (h * ((D + d * h + h) ^ 4)⁻¹) := by ring
        _ ≤ 3 * ((((D + d * h) ^ 3)⁻¹ - ((D + d * h + h) ^ 3)⁻¹) / 3) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = _ := by ring
    calc _ ≤ (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h)
            + (((D + d * h) ^ 3)⁻¹ - ((D + ((d + 1 : ℕ) : ℝ) * h) ^ 3)⁻¹) / (3 * h) :=
          add_le_add ih hstep'
      _ = _ := by ring

/-- ∑_{k<d} (D + k h)⁻⁴ ≤ D⁻⁴ + D⁻³/(3h) for D, h > 0 (any d). -/
lemma sum_inv_pow_four_le {D h : ℝ} (hD : 0 < D) (hh : 0 < h) (d : ℕ) :
    ∑ k ∈ range d, ((D + k * h) ^ 4)⁻¹ ≤ (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) := by
  cases d with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ d =>
    refine (sum_inv_pow_four_le_telescope hD hh d).trans ?_
    have : 0 ≤ ((D + d * h) ^ 3)⁻¹ / (3 * h) := by positivity
    calc (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h)
        = (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) - ((D + d * h) ^ 3)⁻¹ / (3 * h) := by ring
      _ ≤ _ := by linarith

/-- From D⁻⁴ + D⁻³/(3h), h = 2π/L, to L·D⁻³ "(as D ≥ 1, L ≥ 2)". -/
lemma grid_const_bound {D L : ℝ} (hD : 1 ≤ D) (hL : 2 ≤ L) :
    (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * (2 * π / L)) ≤ L * (D ^ 3)⁻¹ := by
  have hD0 : 0 < D := by linarith
  have hπ : 2 ≤ π := Real.two_le_pi
  have h1 : (D ^ 4)⁻¹ ≤ (D ^ 3)⁻¹ := by
    apply inv_anti₀ (by positivity)
    calc D ^ 3 = D ^ 3 * 1 := by ring
      _ ≤ D ^ 3 * D := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = D ^ 4 := by ring
  have h2 : (D ^ 3)⁻¹ / (3 * (2 * π / L)) = (L / (6 * π)) * (D ^ 3)⁻¹ := by
    field_simp
    ring
  rw [h2]
  have h3 : L / (6 * π) ≤ L / 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have hD3 : 0 ≤ (D ^ 3)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 hD3]

/-- **Grid estimate** (proof of [prop:tail]): with τ_k := T + k·h, h = 2π/L, d·h ≤ T,
L ≥ 2 and D := dist(γ, I) ≥ 1 (I = [T,2T]):  ∑_{k<d} |γ − τ_k|⁻⁴ ≤ L · D⁻³. -/
theorem grid_sum_le {T L γ : ℝ} {d : ℕ} (hL : 2 ≤ L) (hT : 0 < T)
    (hd : (d : ℝ) * (2 * π / L) ≤ T) (hD : 1 ≤ distI T γ) :
    ∑ k ∈ range d, (|γ - (T + k * (2 * π / L))| ^ 4)⁻¹ ≤ L * ((distI T γ) ^ 3)⁻¹ := by
  set h := 2 * π / L with hh_def
  have hLpos : 0 < L := by linarith
  have hh : 0 < h := by positivity
  -- γ is at distance ≥ 1 from I, so it lies on one side of it.
  have hside : 1 ≤ T - γ ∨ 1 ≤ γ - 2 * T := by
    unfold distI at hD
    rcases le_max_iff.mp hD with h0 | h1
    · exact absurd h0 (by norm_num)
    · exact le_max_iff.mp h1
  rcases hside with hlt | hgt
  · -- γ below I: |γ − τ_k| = D + k h with D = T − γ.
    have hDeq : distI T γ = T - γ := distI_of_le hT.le (by linarith)
    rw [hDeq] at hD ⊢
    have hterm : ∀ k ∈ range d,
        (|γ - (T + k * h)| ^ 4)⁻¹ = ((T - γ + k * h) ^ 4)⁻¹ := by
      intro k _
      have hk : 0 ≤ (k : ℝ) * h := by positivity
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [sum_congr rfl hterm]
    exact (sum_inv_pow_four_le (by linarith) hh d).trans (grid_const_bound hD hL)
  · -- γ above I: reflect k ↦ d−1−k; |γ − τ_{d−1−k}| ≥ D + k h with D = γ − 2T.
    have hDeq : distI T γ = γ - 2 * T := distI_of_ge hT.le (by linarith)
    rw [hDeq] at hD ⊢
    have hD0 : 0 < γ - 2 * T := by linarith
    rw [← sum_range_reflect]
    have hterm : ∀ k ∈ range d,
        (|γ - (T + ((d - 1 - k : ℕ) : ℝ) * h)| ^ 4)⁻¹ ≤ ((γ - 2 * T + k * h) ^ 4)⁻¹ := by
      intro k hk
      have hkd : k < d := mem_range.mp hk
      have hcast : ((d - 1 - k : ℕ) : ℝ) = d - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [hcast]
      have hk0 : 0 ≤ (k : ℝ) * h := by positivity
      -- τ_{d-1-k} = T + (d-1-k)h ≤ T + d h − h − k h ≤ 2T − h − k h
      have hle : T + ((d : ℝ) - 1 - k) * h ≤ 2 * T - h - k * h := by nlinarith
      have hpos : γ - 2 * T + k * h ≤ γ - (T + ((d : ℝ) - 1 - k) * h) := by linarith
      have hpos' : 0 < γ - 2 * T + k * h := by linarith
      rw [abs_of_pos (by linarith)]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hpos'.le hpos 4
    exact (sum_le_sum hterm).trans
      ((sum_inv_pow_four_le hD0 hh d).trans (grid_const_bound hD hL))

end Tail
end Zeta23
