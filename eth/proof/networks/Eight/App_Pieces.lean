/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import EightSquareStatement
import Mathlib.Tactic

/-! # Arithmetic bounds on t = ⌈λ/3⌉, (2λ)^c and log₂(2λ)

In Appendix A the functions A_0, …, A_t of Definition 5 are pieces with parameters (11/12, c) for
every integer c ≥ 8, with I = {0, …, t} and d = 2^t; part (c) of Definition 7 asks that the numbers
involved be below 2^((2λ)^c).
The lemmas here are elementary bounds of that kind, for λ ≥ 1 and c ≥ 1: t ≤ λ, 2λ ≤ (2λ)^c, 2^t <
2^((2λ)^c) and log₂(2λ) ≥ 1.
They concern only sizes, not running times. -/

public section

namespace Eight

open Finset

/-- t = ⌈λ/3⌉ ≤ λ for λ ≥ 1. -/
theorem tOf_le {lam : ℕ} (hl : 1 ≤ lam) : tOf lam ≤ lam := by
  unfold tOf
  omega

/-- 2λ ≤ (2λ)^c for c ≥ 1. -/
theorem two_mul_le_pow (lam : ℕ) {c : ℕ} (hc : 1 ≤ c) : 2 * lam ≤ (2 * lam) ^ c :=
  Nat.le_self_pow (by omega) _

/-- 2^t < 2^((2λ)^c). -/
theorem two_pow_tOf_lt {lam c : ℕ} (hl : 1 ≤ lam) (hc : 1 ≤ c) : (2 : ℤ) ^ tOf lam < 2 ^ (2 * lam) ^ c := by
  have h1 := tOf_le hl
  have h2 := two_mul_le_pow lam hc
  exact pow_lt_pow_right₀ (by norm_num) (by omega)

/-- log₂(2λ) ≥ 1 for λ ≥ 1. -/
theorem one_le_logb {lam : ℕ} (hl : 1 ≤ lam) : (1 : ℝ) ≤ Real.logb 2 (2 * lam) := by
  have h : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  linarith

end Eight
