/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- A bound `|f n| ≤ C * g n` from some `n₀` on gives `f = O(g)`. -/
theorem isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  refine IsBigO.of_bound |C| (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  exact (h n hn).trans (le_abs_self _)

/-- Every constant is eventually at most `n ^ η`, for `η > 0`. -/
theorem eventually_le_rpow (c : ℝ) {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ η :=
  ((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- `⌈n ^ μ⌉` tends to infinity with `n`, for `μ > 0`. -/
theorem tendsto_ceil_rpow_atTop {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n : ℕ => ⌈(n : ℝ) ^ μ⌉₊) atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_rpow_atTop hμ).comp tendsto_natCast_atTop_atTop)

/-- `n ^ a = O(n ^ b)` for `a ≤ b`. -/
theorem isBigO_rpow_rpow_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine isBigO_of_abs_le 1 1 fun n hn => ?_
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hab

/-- `n ^ a * n ^ b = n ^ (a + b)` for all large `n`. -/
theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]

/-- `(log n) ^ e = o(n ^ η)` for `η > 0`. -/
theorem isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop (e : ℝ) hη).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h

/-- `(log n) ^ e = O((log n) ^ e')` for `e ≤ e'`. -/
theorem isBigO_log_pow_log_pow_of_le {e e' : ℕ} (he : e ≤ e') :
    (fun n : ℕ => Real.log n ^ e) =O[atTop] fun n : ℕ => Real.log n ^ e' := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlog
  refine isBigO_of_abs_le 1 n₀ fun n hn => ?_
  rw [one_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans (hn₀ n hn)) e)]
  exact pow_le_pow_right₀ (hn₀ n hn) he

/-- `n ^ a * (log n) ^ e = O(n ^ b * (log n) ^ e')` for `a ≤ b` and `e ≤ e'`. -/
theorem isBigO_rpow_mul_log_pow_of_le {a b : ℝ} {e e' : ℕ} (hab : a ≤ b) (he : e ≤ e') :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b * Real.log n ^ e' :=
  (isBigO_rpow_rpow_of_le hab).mul (isBigO_log_pow_log_pow_of_le he)

/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`. -/
theorem isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)

/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = O(n ^ b)` for `a < b`. -/
theorem isBigO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop] fun n : ℕ => (n : ℝ) ^ b :=
  (isLittleO_rpow_mul_log_pow_rpow hab e).isBigO

/-- Constants are absorbed as well: `C * (n ^ a * (log n) ^ e) ≤ n ^ b` for all large `n`, if
`a < b`. -/
theorem eventually_mul_rpow_mul_log_pow_le (C : ℝ) {a b : ℝ} (hab : a < b) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ a * Real.log n ^ e) ≤ (n : ℝ) ^ b := by
  have h := ((isLittleO_rpow_mul_log_pow_rpow hab e).const_mul_left C).def zero_lt_one
  filter_upwards [h] with n hn
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg b)] at hn
  exact (le_abs_self _).trans hn

/-- `C * n ^ a ≤ n ^ b` for all large `n`, if `a < b`. -/
theorem eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  simpa only [pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le C hab 0

end ThreeSumApsp
