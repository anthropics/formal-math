/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import LevelsStatement
public import ClauseBound.Gen.PartA
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Part (a) of Theorem A, along its proof in Appendix A

The proof is followed sentence by sentence, in the order of the text: the recursion for x_ℓ = log
K_ℓ and the closed formula; x_ℓ ≥ 2^ℓ·x₀ ≥ max(ℓ, x₀) and x_{ℓ+1} ≤ 10·x_ℓ;
e_ℓ ≥ ρ^ℓ/2; the recursion for y_ℓ = e_ℓ·ρ^{−ℓ}; K_ℓ ≥ 2^{18(ℓ+1)}; the bound on y_ℓ by an
exponential times a sum, and its value below 0.85; ρ^ℓ = (2^ℓ)^{−α'} and 2^ℓ ≥ x_ℓ/(3x₀+6).
`thmRunningTime_a` collects the four assertions of part (a). Only the definition of x_ℓ by its
recursion and K_ℓ = 2^{x_ℓ} in three forms (`K_eq`, `K_cast`, `logb_K`) are taken from the imported
module `ClauseBound.Gen.PartA`. -/

@[expose] public section

namespace GeneralPieces.PartA

open Finset Levels.Gen ClauseBound.Gen

/-! ## The numbers x_ℓ -/

/-- «The numbers x_ℓ = log K_ℓ»: the logarithm of K_ℓ to base 2 is the natural number x_ℓ. -/
theorem logK_eq_x (x₀ l : ℕ) : Real.logb 2 (K x₀ l) = x x₀ l := logb_K x₀ l

/-- «… satisfy x_{ℓ+1} = 2x_ℓ + 6ℓ + 2x₀». -/
theorem x_succ (x₀ l : ℕ) : x x₀ (l + 1) = 2 * x x₀ l + 6 * l + 2 * x₀ := by
  rw [x]; ring

/-- «… which gives the formula by induction»: x_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6. -/
theorem x_formula (x₀ l : ℕ) : (x x₀ l : ℝ) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6 := by
  induction l with
  | zero => simp only [x]; push_cast; ring
  | succ l ih => rw [x_succ]; push_cast; rw [ih, pow_succ]; ring

/-- The first assertion of part (a): log K_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6. -/
theorem logK_formula (x₀ l : ℕ) : Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6 := by
  rw [logK_eq_x, x_formula]

/-- «x_ℓ ≥ 2^ℓ·x₀». -/
theorem x_ge_pow (x₀ l : ℕ) : 2 ^ l * x₀ ≤ x x₀ l := by
  induction l with
  | zero => simp [x]
  | succ l ih =>
    have h : 2 ^ (l + 1) * x₀ = 2 * (2 ^ l * x₀) := by ring
    rw [x_succ, h]; omega

/-- «2^ℓ·x₀ ≥ max{ℓ, x₀}». -/
theorem pow_ge_max (x₀ l : ℕ) (hx : 1 ≤ x₀) : max l x₀ ≤ 2 ^ l * x₀ := by
  have h1 : l < 2 ^ l := Nat.lt_two_pow_self
  have h2 : 2 ^ l * 1 ≤ 2 ^ l * x₀ := Nat.mul_le_mul_left _ hx
  have h3 : 1 * x₀ ≤ 2 ^ l * x₀ := Nat.mul_le_mul_right _ Nat.one_le_two_pow
  exact max_le (by omega) (by omega)

/-- «… we get x_{ℓ+1} ≤ 10·x_ℓ». -/
theorem x_succ_le (x₀ l : ℕ) (hx : 1 ≤ x₀) : x x₀ (l + 1) ≤ 10 * x x₀ l := by
  have h := le_trans (pow_ge_max x₀ l hx) (x_ge_pow x₀ l)
  have h1 : l ≤ x x₀ l := le_trans (le_max_left _ _) h
  have h2 : x₀ ≤ x x₀ l := le_trans (le_max_right _ _) h
  rw [x_succ]; omega

/-- x_ℓ < x_{ℓ+1}, from the recursion. -/
theorem x_lt_succ (x₀ l : ℕ) (hx : 1 ≤ x₀) : x x₀ l < x x₀ (l + 1) := by
  rw [x_succ]; omega

/-- The second assertion of part (a): K_ℓ < K_{ℓ+1} ≤ K_ℓ^10. -/
theorem K_lt_le (x₀ l : ℕ) (hx : 1 ≤ x₀) : K x₀ l < K x₀ (l + 1) ∧ K x₀ (l + 1) ≤ K x₀ l ^ 10 := by
  rw [K_eq, K_eq, ← pow_mul]
  exact ⟨Nat.pow_lt_pow_right (by norm_num) (x_lt_succ x₀ l hx),
    Nat.pow_le_pow_right (by norm_num) (by have := x_succ_le x₀ l hx; omega)⟩

/-! ## The numbers e_ℓ -/

/-- «Clearly e_ℓ ≥ ρ^ℓ/2»: e₀ = 1/2, and e_{ℓ+1} ≥ ρ·e_ℓ, because the other two terms of the
recursion are not negative. -/
theorem e_ge_half_pow (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) : 1 / 2 * ρ ^ l ≤ e ρ x₀ l := by
  have hρ0 : 0 < ρ := by linarith
  induction l with
  | zero => simp [e]
  | succ l ih =>
    have he : 0 ≤ e ρ x₀ l := le_trans (by positivity) ih
    have hz : 0 < zeta l := by unfold zeta; positivity
    have hK : (0 : ℝ) ≤ 3 / K x₀ l := by positivity
    have h1 : ρ * (1 / 2 * ρ ^ l) ≤ ρ * e ρ x₀ l := mul_le_mul_of_nonneg_left ih hρ0.le
    have h2 : 0 ≤ 3 * zeta l * e ρ x₀ l := by positivity
    rw [e, pow_succ]
    nlinarith

/-- y_ℓ = e_ℓ·ρ^{−ℓ}. -/
noncomputable def y (ρ : ℝ) (x₀ l : ℕ) : ℝ := e ρ x₀ l / ρ ^ l

/-- y₀ = 1/2. -/
theorem y_zero (ρ : ℝ) (x₀ : ℕ) : y ρ x₀ 0 = 1 / 2 := by simp [y, e]

/-- «By ρ ≥ 1/2, the numbers y_ℓ = e_ℓ·ρ^{−ℓ} satisfy y_{ℓ+1} ≤ (1 + 2^{−ℓ−2})·y_ℓ + 6·2^ℓ/K_ℓ.» -/
theorem y_succ_le (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) :
    y ρ x₀ (l + 1) ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l + 6 * 2 ^ l / K x₀ l := by
  have hρ0 : 0 < ρ := by linarith
  have hr : 0 < ρ ^ l := by positivity
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have hy : 0 ≤ y ρ x₀ l := div_nonneg (le_trans (by positivity) (e_ge_half_pow ρ x₀ l hρ)) hr.le
  -- the two parts of e_{ℓ+1}, divided by ρ^{ℓ+1}
  have h0 : y ρ x₀ (l + 1) = (1 + 3 * zeta l / ρ) * y ρ x₀ l + 3 / K x₀ l / ρ ^ (l + 1) := by
    simp only [y, e, pow_succ]; field_simp
  -- 3ζ_ℓ/ρ ≤ 6ζ_ℓ ≤ 2^{−ℓ−2}
  have h1 : 3 * zeta l / ρ ≤ 1 / 2 ^ (l + 2) := by
    have hz : zeta l = 1 / 2 ^ (l + 2) / 8 := by rw [zeta, pow_add, pow_add]; field_simp; norm_num
    have hp : (0 : ℝ) < 1 / 2 ^ (l + 2) := by positivity
    rw [hz, div_le_iff₀ hρ0]
    nlinarith
  -- 1/ρ^{ℓ+1} ≤ 2^{ℓ+1}
  have h2 : 3 / (K x₀ l : ℝ) / ρ ^ (l + 1) ≤ 6 * 2 ^ l / K x₀ l := by
    have hp : (1 / 2 : ℝ) ^ (l + 1) ≤ ρ ^ (l + 1) := pow_le_pow_left₀ (by norm_num) hρ _
    have hq : (1 : ℝ) ≤ 2 ^ (l + 1) * ρ ^ (l + 1) := by
      have : (2 : ℝ) ^ (l + 1) * (1 / 2) ^ (l + 1) = 1 := by rw [← mul_pow]; norm_num
      calc (1 : ℝ) = 2 ^ (l + 1) * (1 / 2) ^ (l + 1) := this.symm
        _ ≤ 2 ^ (l + 1) * ρ ^ (l + 1) := mul_le_mul_of_nonneg_left hp (by positivity)
    rw [div_div, div_le_div_iff₀ (by positivity) hK]
    have : 3 * (K x₀ l : ℝ) * 1 ≤ 3 * (K x₀ l : ℝ) * (2 ^ (l + 1) * ρ ^ (l + 1)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    calc 3 * (K x₀ l : ℝ) = 3 * (K x₀ l : ℝ) * 1 := (mul_one _).symm
      _ ≤ 3 * (K x₀ l : ℝ) * (2 ^ (l + 1) * ρ ^ (l + 1)) := this
      _ = 6 * 2 ^ l * (K x₀ l * ρ ^ (l + 1)) := by rw [pow_succ (2 : ℝ) l]; ring
  rw [h0]
  have h3 : (1 + 3 * zeta l / ρ) * y ρ x₀ l ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l :=
    mul_le_mul_of_nonneg_right (by linarith) hy
  linarith

/-- «… and K_ℓ ≥ 2^{18(ℓ+1)}», because x_ℓ ≥ 2^ℓ·x₀ ≥ (ℓ+1)·18. -/
theorem K_ge_pow (x₀ l : ℕ) (hx : 18 ≤ x₀) : 2 ^ (18 * (l + 1)) ≤ K x₀ l := by
  have h1 : l + 1 ≤ 2 ^ l := Nat.lt_two_pow_self
  have h2 : (l + 1) * 18 ≤ 2 ^ l * x₀ := Nat.mul_le_mul h1 hx
  have h3 := x_ge_pow x₀ l
  rw [K_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The two together: y_{ℓ+1} ≤ (1 + 2^{−ℓ−2})·y_ℓ + 6·2^{ℓ−18(ℓ+1)}. -/
theorem y_succ_le' (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) :
    y ρ x₀ (l + 1) ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l + 6 * 2 ^ l / 2 ^ (18 * (l + 1)) := by
  have h1 : (2 : ℝ) ^ (18 * (l + 1)) ≤ K x₀ l := by exact_mod_cast K_ge_pow x₀ l hx
  have h2 : 6 * 2 ^ l / (K x₀ l : ℝ) ≤ 6 * 2 ^ l / 2 ^ (18 * (l + 1)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  linarith [y_succ_le ρ x₀ l hρ]

/-- The step that the text leaves to the reader: if u_{ℓ+1} ≤ (1 + a_ℓ)·u_ℓ + b_ℓ with a_ℓ, b_ℓ, u₀
≥ 0, then u_ℓ ≤ exp(Σ_{j<ℓ} a_j)·(u₀ + Σ_{j<ℓ} b_j), because 1 + a ≤ exp a. -/
theorem le_exp_sum_mul (u a b : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hu : 0 ≤ u 0)
    (h : ∀ l, u (l + 1) ≤ (1 + a l) * u l + b l) (l : ℕ) :
    u l ≤ Real.exp (∑ j ∈ range l, a j) * (u 0 + ∑ j ∈ range l, b j) := by
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range l, a j := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T, T = u 0 + ∑ j ∈ range l, b j := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS ▸ sum_nonneg fun j _ => ha j
    have hT0 : 0 ≤ T := hT ▸ add_nonneg hu (sum_nonneg fun j _ => hb j)
    rw [sum_range_succ, sum_range_succ, ← add_assoc, ← hS, ← hT, Real.exp_add]
    rw [← hS, ← hT] at ih
    have hE : 0 < Real.exp S := Real.exp_pos _
    have h1 : (1 + a l) * u l ≤ (1 + a l) * (Real.exp S * T) :=
      mul_le_mul_of_nonneg_left ih (by linarith [ha l])
    have h2 : (1 + a l) * (Real.exp S * T) ≤ Real.exp (a l) * (Real.exp S * T) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (a l)]) (by positivity)
    have h3 : 1 * b l ≤ Real.exp S * Real.exp (a l) * b l :=
      mul_le_mul_of_nonneg_right
        (one_le_mul_of_one_le_of_one_le (Real.one_le_exp hS0) (Real.one_le_exp (ha l))) (hb l)
    nlinarith [h l]

/-- Σ_{j≥0} 2^{−j−2} = 1/2. -/
theorem hasSum_a : HasSum (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 2)) (1 / 2) := by
  have h := hasSum_geometric_two.mul_left (1 / 4 : ℝ)
  have hf : (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 2)) = fun j : ℕ => 1 / 4 * (1 / 2) ^ j := by
    funext j; rw [pow_add, one_div_pow]; field_simp; norm_num
  rw [hf]
  have h2 : (1 / 4 : ℝ) * 2 = 1 / 2 := by norm_num
  rwa [h2] at h

/-- Σ_{j≥0} 6·2^{j−18(j+1)} = 6·2^{−18}/(1 − 2^{−17}). -/
theorem hasSum_b : HasSum (fun j : ℕ => (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) (6 / 2 ^ 18 * (1 - 1 / 2 ^ 17)⁻¹) := by
  have h := (hasSum_geometric_of_lt_one (r := (1 / 2 ^ 17 : ℝ)) (by positivity) (by norm_num)).mul_left (6 / 2 ^ 18 : ℝ)
  have hf : (fun j : ℕ => (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) = fun j : ℕ => 6 / 2 ^ 18 * (1 / 2 ^ 17) ^ j := by
    funext j
    rw [show 18 * (j + 1) = 18 + 17 * j + j by ring, pow_add, pow_add, pow_mul, one_div_pow]
    field_simp
  rw [hf]
  exact h

/-- «So y_ℓ ≤ exp(Σ_{j≥0} 2^{−j−2})·(1/2 + Σ_{j≥0} 6·2^{j−18(j+1)})». -/
theorem y_le_exp_tsum (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) :
    y ρ x₀ l ≤ Real.exp (∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2)) * (1 / 2 + ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) := by
  have h := le_exp_sum_mul (y ρ x₀) (fun j => 1 / 2 ^ (j + 2)) (fun j => 6 * 2 ^ j / 2 ^ (18 * (j + 1)))
    (fun j => by positivity) (fun j => by positivity) (by rw [y_zero]; norm_num)
    (fun l => y_succ_le' ρ x₀ l hρ hx) l
  rw [y_zero] at h
  have ha : ∑ j ∈ range l, (1 : ℝ) / 2 ^ (j + 2) ≤ ∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2) :=
    hasSum_a.summable.sum_le_tsum _ (fun j _ => by positivity)
  have hb : ∑ j ∈ range l, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1)) ≤ ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1)) :=
    hasSum_b.summable.sum_le_tsum _ (fun j _ => by positivity)
  refine le_trans h (mul_le_mul (Real.exp_le_exp.mpr ha) (by linarith) ?_ (Real.exp_pos _).le)
  exact add_nonneg (by norm_num) (sum_nonneg fun j _ => by positivity)

/-- «… ≤ e^{1/2}·0.51». -/
theorem exp_tsum_le : Real.exp (∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2)) * (1 / 2 + ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) ≤
    Real.exp (1 / 2) * 0.51 := by
  rw [hasSum_a.tsum_eq, hasSum_b.tsum_eq]
  exact mul_le_mul_of_nonneg_left (by norm_num) (Real.exp_pos _).le

/-- «… < 0.85». -/
theorem exp_half_mul_lt : Real.exp (1 / 2) * 0.51 < 0.85 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have h4 : Real.exp (1 / 2) < 1.66 := by
    by_contra hc
    have hc' : 1.66 ≤ Real.exp (1 / 2) := not_lt.mp hc
    nlinarith
  linarith

/-- y_ℓ < 0.85. -/
theorem y_lt (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) : y ρ x₀ l < 0.85 :=
  lt_of_le_of_lt (le_trans (y_le_exp_tsum ρ x₀ l hρ hx) exp_tsum_le) exp_half_mul_lt

/-- e_ℓ ≤ 0.85·ρ^ℓ, from y_ℓ < 0.85. -/
theorem e_le_of_y (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) : e ρ x₀ l ≤ 0.85 * ρ ^ l := by
  have hr : 0 < ρ ^ l := by have : 0 < ρ := by linarith
                            positivity
  have h := (y_lt ρ x₀ l hρ hx).le
  rwa [y, div_le_iff₀ hr] at h

/-! ## ρ^ℓ against log K_ℓ -/

/-- «Finally ρ^ℓ = (2^ℓ)^{−α'}», where α' = log(1/ρ). -/
theorem rho_pow_eq (ρ : ℝ) (l : ℕ) (hρ : 0 < ρ) : ρ ^ l = ((2 : ℝ) ^ l) ^ (-Real.logb 2 (1 / ρ)) := by
  have h : (2 : ℝ) ^ (-Real.logb 2 (1 / ρ)) = ρ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    simp
  rw [← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num), h,
    Real.rpow_natCast]

/-- «… and 2^ℓ ≥ x_ℓ/(3x₀+6).» -/
theorem two_pow_ge (x₀ l : ℕ) : (x x₀ l : ℝ) / (3 * x₀ + 6) ≤ 2 ^ l := by
  rw [div_le_iff₀ (by positivity), x_formula]
  have h1 : (0 : ℝ) ≤ l := by positivity
  have h2 : (0 : ℝ) ≤ x₀ := by positivity
  nlinarith

/-- The last assertion of part (a): ρ^ℓ ≤ ((3x₀+6)/log K_ℓ)^{α'}. -/
theorem rho_pow_le (ρ : ℝ) (x₀ l : ℕ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hx : 1 ≤ x₀) :
    ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ) := by
  have hα : 0 ≤ Real.logb 2 (1 / ρ) := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hρ]; linarith)
  have hxpos : (0 : ℝ) < x x₀ l := by
    have h1 := x_ge_pow x₀ l
    have h2 : 0 < 2 ^ l * x₀ := by positivity
    exact_mod_cast lt_of_lt_of_le h2 h1
  rw [rho_pow_eq ρ l hρ, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), logK_eq_x]
  apply Real.rpow_le_rpow (by positivity) _ hα
  have h := two_pow_ge x₀ l
  rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
  exact h

/-! ## Part (a) -/

/-- The four assertions of part (a) of Theorem A, for one ρ and one x₀. -/
structure TheoremAa (ρ : ℝ) (x₀ : ℕ) : Prop where
  /-- log K_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6 -/
  logK : ∀ l : ℕ, Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6
  /-- so K_ℓ < K_{ℓ+1} ≤ K_ℓ^10 -/
  K_lt_le : ∀ l : ℕ, K x₀ l < K x₀ (l + 1) ∧ K x₀ (l + 1) ≤ K x₀ l ^ 10
  /-- ρ^ℓ/2 ≤ e_ℓ ≤ 0.85·ρ^ℓ -/
  e_bounds : ∀ l : ℕ, 1 / 2 * ρ ^ l ≤ e ρ x₀ l ∧ e ρ x₀ l ≤ 0.85 * ρ ^ l
  /-- where ρ^ℓ ≤ ((3x₀+6)/log K_ℓ)^{α'}, α' = log(1/ρ) -/
  rho_pow : ∀ l : ℕ, ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ)

/-- Part (a) of Theorem A, for 1/2 ≤ ρ < 1 and every x₀ ≥ 18. It does not need pieces, nor 2^x₀ ≥ c + 5. -/
theorem thmRunningTime_a (ρ : ℝ) (x₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) : TheoremAa ρ x₀ where
  logK := logK_formula x₀
  K_lt_le := fun l => K_lt_le x₀ l (by omega)
  e_bounds := fun l => ⟨e_ge_half_pow ρ x₀ l hρ, e_le_of_y ρ x₀ l hρ hx⟩
  rho_pow := fun l => rho_pow_le ρ x₀ l (by linarith) hρ1.le (by omega)

end GeneralPieces.PartA
