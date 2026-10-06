/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log

/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/

/-- `log x + 1 = O(x ^ η)` on `x ≥ 1`, for `η > 0`. -/
theorem dominated_log_add_one_rpow {η : ℝ} (hη : 0 < η) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => log x + 1) fun x => x ^ η := by
  refine .of_le_const_mul (C := 1 / η + 1) (by positivity) fun x hx => ?_
  have hlog : log x ≤ x ^ η / η := log_le_rpow_div (zero_le_one.trans hx) hη
  have hone : 1 ≤ x ^ η := one_le_rpow hx hη.le
  rw [add_mul, one_mul, one_div_mul_eq_div]
  exact add_le_add hlog hone

/-- `(log x + 1) ^ e = O(x ^ η)` on `x ≥ 1`, for `η > 0`. -/
theorem dominated_log_add_one_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => (log x + 1) ^ e) fun x => x ^ η := by
  have hstep := (dominated_log_add_one_rpow (div_pos hη (Nat.cast_add_one_pos e))).pow
    (fun x hx => add_nonneg (log_nonneg hx) zero_le_one) e
  refine hstep.mono_right fun x hx => ?_
  rw [← rpow_natCast, ← rpow_mul (zero_le_one.trans hx)]
  refine rpow_le_rpow_of_exponent_le hx ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (Nat.cast_add_one_pos e)]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hη.le

/-- Logarithms are absorbed: `x ^ a * (log x + 1) ^ e = O(x ^ b)` on `x ≥ 1`, for `a < b`. -/
theorem dominated_rpow_mul_log_add_one_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => x ^ a * (log x + 1) ^ e) fun x => x ^ b :=
  ((dominated_log_add_one_pow_rpow (sub_pos.2 hab) e).mul_left
    fun x hx => rpow_nonneg (zero_le_one.trans hx) a).congr (fun _ _ => rfl) fun x hx => by
      rw [← rpow_add (zero_lt_one.trans_le hx), add_sub_cancel]

/-- Logarithms are absorbed: `x ^ a * (log x) ^ e = O(x ^ b)` on `x ≥ 1`, for `a < b`. -/
theorem dominated_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => x ^ a * log x ^ e) fun x => x ^ b :=
  (dominated_rpow_mul_log_add_one_pow_rpow hab e).mono_left fun _ hx =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (log_nonneg hx) (le_add_of_nonneg_right zero_le_one) e)
      (rpow_nonneg (zero_le_one.trans hx) a)

/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/

/-- `log x + 1 = O(log x)` on `x ≥ 2`. -/
theorem dominated_log_add_one_log :
    Dominated (fun x : ℝ => 2 ≤ x) (fun x => log x + 1) fun x => log x :=
  .of_le_const_mul (C := 3) (by norm_num) fun _ hx => by
    linarith [one_half_le_log_of_two_le hx]

/-- `⌈log_b n⌉ + 1 = O(log n)` on `n ≥ 2`, for every natural number `b`. -/
theorem dominated_clog_add_one_log (b : ℕ) :
    Dominated (fun n : ℕ => 2 ≤ n) (fun n => (Nat.clog b n : ℝ) + 1) fun n => log n := by
  have hlogb : 0 ≤ log b := log_natCast_nonneg b
  refine .of_le_const_mul (C := 1 / log b + 4) (by positivity) fun n hn => ?_
  have hhalf : 1 / 2 ≤ log n := one_half_le_log_of_two_le (by exact_mod_cast hn)
  have hclog := natCast_clog_lt_logb_add_one b n
  rw [add_mul, one_div_mul_eq_div]
  -- `⌈log_b n⌉ + 1 < log n / log b + 2` and `2 ≤ 4 log n`
  rw [logb] at hclog
  linarith [hclog, hhalf]

end ThreeSumApsp
