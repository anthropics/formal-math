/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.Small
public import VariableBound.Printed.ThmVariablesA
import VariableBound.Paper.Arith

/-! # What the bound absorbs

`lg_le_exp`: for every α ≥ 0 there is a c₁ with log n ≤ c₁·n·log log n/(log n)^α for all n ≥ 4. For
large n this is the fact «k log n ≤ en for large n» of Step 5 of Appendix D
(`MainTheoremForms.stepSparsifyLarge`) at k = 1 and e = (log n)^{−⌈α⌉}; for the finitely many other
n
it follows from `SmallCasesAreWithinTheBound`. `absorb`: so q·(t + X + 1)^q is within the bound if t
is, with the constant D, and X + 1 ≤ (n + 2)^D; the constant becomes q·(2D + 2)·c₁. -/

public section

namespace FixedWidthSteps

open MainTheoremForms FixedWidth

/-- x^m = 2^{m·log x}. -/
theorem pow_eq_two_rpow {x : ℝ} (hx : 0 < x) (m : ℕ) : x ^ m = (2 : ℝ) ^ ((m : ℝ) * lg x) := by
  rw [mul_comm, Real.rpow_mul (by norm_num), show (2 : ℝ) ^ lg x = x from Real.rpow_logb (by norm_num) (by norm_num) hx, Real.rpow_natCast]

/-- 2^{a·E} ≤ 2^{b·E} for a ≤ b and E ≥ 0. -/
theorem two_rpow_mono {a b : ℕ} (h : a ≤ b) {E : ℝ} (hE : 0 ≤ E) : (2 : ℝ) ^ ((a : ℝ) * E) ≤ (2 : ℝ) ^ ((b : ℝ) * E) :=
  Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) hE)

/-- log n ≤ c₁·n·log log n/(log n)^α for all n ≥ 4. -/
theorem lg_le_exp (hSmall : SmallCasesAreWithinTheBound) (α : ℝ) (hα : 0 ≤ α) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ n : ℕ, 4 ≤ n → lg n ≤ c₁ * expVariables α n := by
  obtain ⟨n₁, h₁⟩ := MainTheoremForms.stepSparsifyLarge ⌈α⌉₊
  obtain ⟨C, hC⟩ := hSmall α 1 0 n₁ hα
  refine ⟨C + 1, by omega, fun n hn => ?_⟩
  obtain ⟨hl2, hll⟩ := lg_facts hn
  have hE := expVariables_pos α hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have e1 : ((C + 1 : ℕ) : ℝ) * expVariables α n = C * expVariables α n + expVariables α n := by push_cast; ring
  rw [e1]
  by_cases h : n₁ ≤ n
  · have h2 := h₁ 1 n (1 / lg n ^ ⌈α⌉₊) h (by norm_num; linarith) le_rfl
    have h3 : lg n ^ α ≤ lg n ^ ⌈α⌉₊ := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil α)
    have h4 : 0 < lg n ^ α := Real.rpow_pos_of_pos (by linarith) _
    have h5 : 1 / lg n ^ ⌈α⌉₊ * n ≤ expVariables α n := by
      rw [one_div_mul_eq_div]
      show (n : ℝ) / lg n ^ ⌈α⌉₊ ≤ (n : ℝ) * lg (lg n) / lg n ^ α
      exact div_le_div₀ (mul_nonneg hn0.le (by linarith)) (by nlinarith [mul_nonneg hn0.le (sub_nonneg.2 hll)]) h4 h3
    rw [Nat.cast_one, one_mul] at h2
    have := mul_nonneg hC0 hE.le
    linarith
  · have h2 := hC n hn (not_le.1 h)
    simp only [one_mul, pow_zero, mul_one] at h2
    have h3 : (2 : ℝ) ^ (n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * expVariables α n) := by
      rw [Real.rpow_natCast]
      exact le_trans (by exact_mod_cast h2) (timeVariables_le α C n)
    have h4 : (n : ℝ) ≤ C * expVariables α n := (Real.rpow_le_rpow_left_iff one_lt_two).1 h3
    have h5 : lg n ≤ (n : ℝ) - 1 := VariableBound.Paper.lg_le_sub_one (by omega)
    linarith

/-- If t ≤ 2^{D·E(n)} and X + 1 ≤ (n + 2)^D, then q·(t + X + 1)^q ≤ 2^{C·E(n)} with C = q·(2D + 2)·c₁,
where E(n) = n·log log n/(log n)^α. -/
theorem absorb (α : ℝ) {c₁ : ℕ} (hc : 1 ≤ c₁) (hB : ∀ n : ℕ, 4 ≤ n → lg n ≤ c₁ * expVariables α n) (q D : ℕ) {n t X : ℕ} (hn : 4 ≤ n)
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * expVariables α n)) (hX : X + 1 ≤ (n + 2) ^ D) : q * (t + X + 1) ^ q ≤ timeVariables α (q * (2 * D + 2) * c₁) n := by
  obtain ⟨hl2, -⟩ := lg_facts hn
  have hE := expVariables_pos α hn
  have hBn := hB n hn
  unfold timeVariables
  apply Nat.le_floor
  generalize expVariables α n = E at *
  have hc' : (1 : ℝ) ≤ c₁ := by exact_mod_cast hc
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = c₁ * E := ⟨_, rfl⟩
  rw [← hy] at hBn
  have hEy : E ≤ y := by rw [hy]; nlinarith
  have hy1 : 1 ≤ y := by linarith
  have ht' : (t : ℝ) ≤ (2 : ℝ) ^ (2 * (D : ℝ) * y) :=
    ht.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith [mul_le_mul_of_nonneg_left hEy hD, mul_nonneg hD (by linarith : (0 : ℝ) ≤ y)]))
  have hX' : (X : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * (D : ℝ) * y) := by
    have h1 : (X : ℝ) + 1 ≤ ((n : ℝ) + 2) ^ D := by exact_mod_cast hX
    have h2 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc (X : ℝ) + 1 ≤ ((n : ℝ) + 2) ^ D := h1
      _ ≤ ((n : ℝ) ^ 2) ^ D := pow_le_pow_left₀ (by positivity) h2 D
      _ = (2 : ℝ) ^ (2 * (D : ℝ) * lg n) := by rw [← pow_mul, pow_eq_two_rpow (x := (n : ℝ)) (by linarith), Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hBn (by positivity))
  have hsum : (t : ℝ) + X + 1 ≤ (2 : ℝ) ^ ((2 * (D : ℝ) + 1) * y) := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ y := by
      have := Real.rpow_le_rpow_of_exponent_le (one_le_two (α := ℝ)) hy1
      rwa [Real.rpow_one] at this
    have e : (2 : ℝ) ^ ((2 * (D : ℝ) + 1) * y) = (2 : ℝ) ^ y * (2 : ℝ) ^ (2 * (D : ℝ) * y) := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hp : 0 < (2 : ℝ) ^ (2 * (D : ℝ) * y) := by positivity
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right h2 hp.le]
  have hpow : ((t : ℝ) + X + 1) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * ((2 * (D : ℝ) + 1) * y)) := by
    calc ((t : ℝ) + X + 1) ^ q ≤ ((2 : ℝ) ^ ((2 * (D : ℝ) + 1) * y)) ^ q := pow_le_pow_left₀ (by positivity) hsum q
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  have hq : (q : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) * y) := by
    calc (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast Nat.lt_two_pow_self.le
      _ = (2 : ℝ) ^ (q : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
  push_cast
  calc (q : ℝ) * ((t : ℝ) + X + 1) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * y) * (2 : ℝ) ^ ((q : ℝ) * ((2 * (D : ℝ) + 1) * y)) := mul_le_mul hq hpow (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num), hy]; congr 1; ring

end FixedWidthSteps
