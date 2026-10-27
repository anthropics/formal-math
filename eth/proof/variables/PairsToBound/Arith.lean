/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PairsToBound.Defs
import VariableBound.Paper.Arith
import VariableBound.Printed.VariablesA.StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Theorem D (b) from Theorem D (a): the arithmetic

Sentences (5), (6) and (8) of Step 6 of Appendix D, in the numbering of
proof/variables/PairsToBound/Defs.lean, and the numbers for the main statement.

* `mainRegimeBound`: sentence (5). It is the «In particular» of Theorem D (a)
  (`MainTheoremForms.ThmVariablesAInParticular`) at α′ = 1/2, where (log n)^(1/2) = √(log n).
* `theBoundIncreasesWithTheWidth`: «the bound increases with k».
* `fallBackIsWithinTheBound`: sentence (8). The one inequality that needs work is log n ≤ n/√(log
  n), that is (log n)³ ≤ n² (`lg_cube_le`): with y = (2/3)·ln n, log n ≤ (50/23)·y ≤ 1 + y + y²/2 ≤
  e^y, and (e^y)³ = n².
* `choice_le`: if t and len + 1 are at most 2^{c₁·X} and X ≥ 1, then q·(t + len + 1)^q ≤
  2^{q(c₁+2)·X}. `main_case_le` and `fall_back_case_le` apply it with X = k²·n·log log n/√(log n) to
  the two branches of the algorithm of Step 6; `le_of_wide` and `le_of_small` give n ≤ D·X in the
  two cases in which the algorithm tries all
  assignments. -/

public section

namespace PairsToBound

open MainTheoremForms VariableBound.Paper

/-! ### Sentence (5): the main regime -/

/-- «So for n ≥ K₀^17 and 3 ≤ k ≤ (log n)^(1/4) the algorithm of Theorem D (a) takes time
2^{O(k²·n·log log n/√(log n))}» (Step 6 of Appendix D), for every machine with the conclusion of
Theorem D (a). -/
theorem mainRegimeBound : MainRegimeBound := by
  intro Idx _ S e C₀ Q a he M C' hM
  obtain ⟨C, hC⟩ := VariableBound.VariablesA.thmVariablesAInParticular Idx S e C₀ Q (1 / 2) a (by norm_num) (fun l => by rw [← Real.sqrt_eq_rpow]; exact he l) M C' hM
  refine ⟨C, fun k n φ h1 h2 h3 h4 => ?_⟩
  have h := hC k n φ h1 h2 h3 h4
  have e : timeVariablesAAlpha C k n (1 / 2) = timeN C k n := by
    unfold timeVariablesAAlpha timeN expN
    rw [← Real.sqrt_eq_rpow]
  rwa [e] at h

/-! ### «The bound increases with k» -/

/-- For n ≥ 4 and k ≤ k′: k²·n·log log n/√(log n) is at most the same number at k′. -/
theorem expN_mono {k k' n : ℕ} (hn : 4 ≤ n) (h : k ≤ k') : expN k n ≤ expN k' n := by
  rw [expN_eq, expN_eq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast h) 2) (by linarith [two_le_base hn])

/-- For 3 ≤ k ≤ k′ and 0 < e ≤ 1: k²·e·n·log(k/e) is at most the same number at k′. -/
theorem expVariablesA_mono {k k' n : ℕ} {e : ℝ} (hk : 3 ≤ k) (h : k ≤ k') (he : 0 < e) (he1 : e ≤ 1) : expVariablesA k n e ≤ expVariablesA k' n e := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkk : (k : ℝ) ≤ k' := by exact_mod_cast h
  have h1 : 1 ≤ (k : ℝ) / e := by rw [le_div_iff₀ he]; linarith
  have hl0 : 0 ≤ lg ((k : ℝ) / e) := Real.logb_nonneg one_lt_two h1
  have hl : lg ((k : ℝ) / e) ≤ lg ((k' : ℝ) / e) := lg_mono (by linarith) (div_le_div_of_nonneg_right hkk he.le)
  unfold expVariablesA
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg k) hkk 2) he.le) (Nat.cast_nonneg n)) hl hl0 (by positivity)

/-- «the bound increases with k» (Step 5 of Appendix D), for the bound of Theorem D (b) and for that
of Theorem D (a). -/
theorem theBoundIncreasesWithTheWidth : TheBoundIncreasesWithTheWidth :=
  ⟨fun C _ _ _ hn h => Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (expN_mono hn h) (Nat.cast_nonneg C))),
   fun C _ _ _ _ hk h he he1 => Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (expVariablesA_mono hk h he he1) (Nat.cast_nonneg C)))⟩

/-! ### Sentence (8): trying all assignments is within the bound -/

/-- (log n)³ ≤ n² for n ≥ 1. -/
theorem lg_cube_le {n : ℕ} (hn : 1 ≤ n) : lg n ^ 3 ≤ (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog : lg n * Real.log 2 = Real.log n := by
    unfold lg
    rw [Real.logb, div_mul_cancel₀ _ (by linarith : Real.log 2 ≠ 0)]
  have hL0 : 0 ≤ lg n := Real.logb_nonneg one_lt_two hn1
  obtain ⟨y, hy⟩ : ∃ y, y = 2 / 3 * Real.log n := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; have := Real.log_nonneg hn1; positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hy0
  have h2 : lg n ≤ Real.exp y := by
    have h3 : 0.69 * lg n ≤ 3 / 2 * y := by rw [hy]; nlinarith
    nlinarith [sq_nonneg (y - 27 / 23)]
  calc lg n ^ 3 ≤ Real.exp y ^ 3 := pow_le_pow_left₀ hL0 h2 3
    _ = (n : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * y = ((2 : ℕ) : ℝ) * Real.log n by rw [hy]; push_cast; ring, Real.exp_nat_mul, Real.exp_log hn0]

/-- «log n ≤ n/√(log n)», for n ≥ 2. -/
theorem lg_le_div_sqrt {n : ℕ} (hn : 2 ≤ n) : lg n ≤ n / Real.sqrt (lg n) := by
  have hL := one_le_lg hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hs]
  refine (sq_le_sq₀ (by positivity) (Nat.cast_nonneg n)).1 ?_
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  calc lg n ^ 2 * lg n = lg n ^ 3 := by ring
    _ ≤ (n : ℝ) ^ 2 := lg_cube_le (by omega)

/-- «n/√(log n) ≤ n·log log n/√(log n)», for n ≥ 4. -/
theorem div_sqrt_le_base {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) / Real.sqrt (lg n) ≤ n * lg (lg n) / Real.sqrt (lg n) := by
  obtain ⟨-, -, hl1, -, -⟩ := lg_add_four hn
  exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (Nat.cast_nonneg n) hl1) (Real.sqrt_nonneg _)

/-- «so k·log n ≤ k²·n·log log n/√(log n)», for k ≥ 1 and n ≥ 4. -/
theorem mul_lg_le_expN {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : (k : ℝ) * lg n ≤ expN k n := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 := (lg_le_div_sqrt (n := n) (by omega)).trans (div_sqrt_le_base hn)
  have h0 : 0 ≤ lg n := by linarith [one_le_lg (m := n) (by omega)]
  rw [expN_eq]
  exact mul_le_mul (by nlinarith) h1 h0 (by positivity)

/-- «if k > (log n)^(1/4), then k²·n·log log n/√(log n) ≥ n·log log n», for n ≥ 4. -/
theorem mul_lglg_le_expN {k n : ℕ} (hn : 4 ≤ n) (h : lg n < (k : ℝ) ^ 4) : (n : ℝ) * lg (lg n) ≤ expN k n := by
  obtain ⟨hL2, -, hl1, -, -⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have hsk : Real.sqrt (lg n) ≤ (k : ℝ) ^ 2 := Real.sqrt_le_iff.2 ⟨by positivity, by rw [← pow_mul]; exact h.le⟩
  unfold expN
  rw [le_div_iff₀ hs]
  calc (n : ℝ) * lg (lg n) * Real.sqrt (lg n) ≤ (n : ℝ) * lg (lg n) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsk (mul_nonneg (Nat.cast_nonneg n) (by linarith))
    _ = (k : ℝ) ^ 2 * n * lg (lg n) := by ring

/-- «and if n < K₀^17, then n·log log n/√(log n) ≥ n/√(17·log K₀)», for n ≥ 4. -/
theorem div_sqrt_level_le_base {K₀ n : ℕ} (hn : 4 ≤ n) (h : n < K₀ ^ 17) : (n : ℝ) / Real.sqrt (17 * lg K₀) ≤ n * lg (lg n) / Real.sqrt (lg n) := by
  obtain ⟨hL2, -, -, -, -⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have hle : lg n ≤ 17 * lg K₀ := by
    have h1 : lg n ≤ lg ((K₀ : ℝ) ^ 17) := lg_mono (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast h.le)
    have h2 : lg ((K₀ : ℝ) ^ 17) = 17 * lg K₀ := by
      unfold lg
      rw [Real.logb_pow]
      norm_num
    linarith
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hs (Real.sqrt_le_sqrt hle)).trans (div_sqrt_le_base hn)

/-- «It is within the bound: …» (Step 6 of Appendix D): the printed inequalities. -/
theorem fallBackIsWithinTheBound : FallBackIsWithinTheBound :=
  ⟨fun _ hn => ⟨lg_le_div_sqrt (by omega), div_sqrt_le_base hn⟩, fun _ _ hk hn => mul_lg_le_expN hk hn,
   fun _ n hn h => ⟨mul_lglg_le_expN hn h, le_mul_of_one_le_right (Nat.cast_nonneg n) (lg_add_four hn).2.2.1⟩,
   fun _ _ _ hn h => div_sqrt_level_le_base hn h⟩

/-! ### The numbers for the main statement -/

/-- «which multiplies k² by at most 9»: if k′² ≤ 9k², the exponent at k′ is at most 9 times that at
k, for n ≥ 4. -/
theorem expN_le_nine {k k' n : ℕ} (hn : 4 ≤ n) (h : k' ^ 2 ≤ 9 * k ^ 2) : expN k' n ≤ 9 * expN k n := by
  have h' : (k' : ℝ) ^ 2 ≤ 9 * (k : ℝ) ^ 2 := by exact_mod_cast h
  rw [expN_eq, expN_eq]
  calc (k' : ℝ) ^ 2 * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) ≤ 9 * (k : ℝ) ^ 2 * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) :=
        mul_le_mul_of_nonneg_right h' (by linarith [two_le_base hn])
    _ = _ := by ring

/-- If the width k′ used by the algorithm exceeds (log n)^(1/4) and k′² ≤ 9k², then n ≤ 9·k²·n·log
log n/√(log n). -/
theorem le_of_wide {k k' n : ℕ} (hn : 4 ≤ n) (h : lg n < (k' : ℝ) ^ 4) (hk : k' ^ 2 ≤ 9 * k ^ 2) : (n : ℝ) ≤ 9 * expN k n :=
  (le_mul_of_one_le_right (Nat.cast_nonneg n) (lg_add_four hn).2.2.1).trans ((mul_lglg_le_expN hn h).trans (expN_le_nine hn hk))

/-- If n < K₀^17 and √(17·log K₀) ≤ D, then n ≤ D·k²·n·log log n/√(log n), for k ≥ 1, K₀ ≥ 2 and n ≥ 4. -/
theorem le_of_small {K₀ k n : ℕ} {D : ℝ} (hK : 2 ≤ K₀) (hk : 1 ≤ k) (hn : 4 ≤ n) (h : n < K₀ ^ 17) (hD : Real.sqrt (17 * lg K₀) ≤ D) : (n : ℝ) ≤ D * expN k n := by
  have hs : 0 < Real.sqrt (17 * lg K₀) := Real.sqrt_pos.2 (by linarith [one_le_lg hK])
  have h1 := div_sqrt_level_le_base hn h
  rw [div_le_iff₀ hs] at h1
  have hb := two_le_base hn
  have h2 : (n : ℝ) * lg (lg n) / Real.sqrt (lg n) ≤ expN k n := by
    rw [expN_eq]
    exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by exact_mod_cast hk))
  calc (n : ℝ) ≤ (n : ℝ) * lg (lg n) / Real.sqrt (lg n) * Real.sqrt (17 * lg K₀) := h1
    _ ≤ expN k n * D := mul_le_mul h2 hD hs.le (by linarith)
    _ = D * expN k n := mul_comm _ _

/-- n^j = 2^{j·log n} for n ≥ 1. -/
theorem natCast_pow_eq {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : (n : ℝ) ^ j = (2 : ℝ) ^ ((j : ℝ) * lg n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_comm, Real.rpow_mul two_pos.le, lg, Real.rpow_logb two_pos (by norm_num) hn0, Real.rpow_natCast]

/-- 2^{a·X} ≤ 2^{b·X} for natural numbers a ≤ b and X ≥ 0. -/
theorem two_rpow_mono {a b : ℕ} (h : a ≤ b) {X : ℝ} (hX : 0 ≤ X) : (2 : ℝ) ^ ((a : ℝ) * X) ≤ (2 : ℝ) ^ ((b : ℝ) * X) :=
  Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hX)

/-- The polynomial factor q·(t + len + 1)^q goes into the constant: if t ≤ 2^{c₁·X}, len + 1 ≤
2^{c₁·X} and X ≥ 1, then q·(t + len + 1)^q ≤ 2^{q(c₁+2)·X}, rounded down. -/
theorem choice_le (q c₁ : ℕ) {t len : ℕ} {X : ℝ} (hX : 1 ≤ X) (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * X)) (hl : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * X)) :
    q * (t + len + 1) ^ q ≤ ⌊(2 : ℝ) ^ (((q * (c₁ + 2) : ℕ) : ℝ) * X)⌋₊ := by
  refine Nat.le_floor ?_
  have h1 : (t : ℝ) + len + 1 ≤ (2 : ℝ) ^ (((c₁ : ℝ) + 1) * X) := by
    have e : (2 : ℝ) ^ (((c₁ : ℝ) + 1) * X) = (2 : ℝ) ^ ((c₁ : ℝ) * X) * (2 : ℝ) ^ X := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ X := by
      have := Real.rpow_le_rpow_of_exponent_le one_le_two hX
      rwa [Real.rpow_one] at this
    have hp : (0 : ℝ) < (2 : ℝ) ^ ((c₁ : ℝ) * X) := by positivity
    push_cast at hl
    rw [e]
    nlinarith
  calc ((q * (t + len + 1) ^ q : ℕ) : ℝ) = (q : ℝ) * ((t : ℝ) + len + 1) ^ q := by push_cast; ring
    _ ≤ (2 : ℝ) ^ ((q : ℝ) * X) * ((2 : ℝ) ^ (((c₁ : ℝ) + 1) * X)) ^ q :=
        mul_le_mul (natCast_le_two_rpow q hX) (pow_le_pow_left₀ (by positivity) h1 q) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (((q * (c₁ + 2) : ℕ) : ℝ) * X) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring

/-- A code of length len with len + 1 ≤ (n+2)^(5k) has len + 1 ≤ 2^{10·X}, X = k²·n·log log n/√(log
n), for k ≥ 1 and n ≥ 4. -/
theorem length_le_rpow {k n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * expN k n) := by
  have h1 : (n + 2) ^ (5 * k) ≤ n ^ (10 * k) := by
    calc (n + 2) ^ (5 * k) ≤ (n ^ 2) ^ (5 * k) := Nat.pow_le_pow_left (by nlinarith) _
      _ = n ^ (10 * k) := by rw [← pow_mul, show 2 * (5 * k) = 10 * k by ring]
  calc ((len + 1 : ℕ) : ℝ) ≤ ((n ^ (10 * k) : ℕ) : ℝ) := by exact_mod_cast hlen.trans h1
    _ = (2 : ℝ) ^ (((10 * k : ℕ) : ℝ) * lg n) := by rw [Nat.cast_pow, natCast_pow_eq (by omega)]
    _ ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have := mul_lg_le_expN hk hn
        push_cast
        nlinarith

/-- The branch of the main regime, as numbers: for k ≥ 1, n ≥ 4, k′² ≤ 9k², len + 1 ≤ (n+2)^(5k) and
c₁ at least 9C₁ and at least 10, q·(2^{C₁·k′²·n·log log n/√(log n)} + len + 1)^q ≤
2^{q(c₁+2)·k²·n·log log n/√(log n)}, both powers of 2 rounded down. -/
theorem main_case_le (q C₁ c₁ : ℕ) (h1 : 9 * C₁ ≤ c₁) (h2 : 10 ≤ c₁) {k k' n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hkk : k' ^ 2 ≤ 9 * k ^ 2) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (timeN C₁ k' n + len + 1) ^ q ≤ timeN (q * (c₁ + 2)) k n := by
  have hX := two_le_expN hk hn
  refine choice_le q c₁ (by linarith) ?_ ((length_le_rpow hk hn hlen).trans (two_rpow_mono h2 (by linarith)))
  calc (timeN C₁ k' n : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * expN k' n) := Nat.floor_le (by positivity)
    _ ≤ (2 : ℝ) ^ (((9 * C₁ : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have := mul_le_mul_of_nonneg_left (expN_le_nine hn hkk) (Nat.cast_nonneg C₁ : (0 : ℝ) ≤ C₁)
        push_cast
        linarith
    _ ≤ _ := two_rpow_mono h1 (by linarith)

/-- The branch that tries all assignments, as numbers: for k ≥ 1, n ≥ 4, n ≤ D·k²·n·log log n/√(log
n), len + 1 ≤ (n+2)^(5k) and c₁ at least c(D+1) and at least 10, q·(2^{c·n}·n^{c·k} + len + 1)^q ≤
2^{q(c₁+2)·k²·n·log log n/√(log n)}, rounded down. -/
theorem fall_back_case_le (q c D c₁ : ℕ) (h1 : c * (D + 1) ≤ c₁) (h2 : 10 ≤ c₁) {k n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hD : (n : ℝ) ≤ (D : ℝ) * expN k n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (2 ^ (c * n) * n ^ (c * k) + len + 1) ^ q ≤ timeN (q * (c₁ + 2)) k n := by
  have hX := two_le_expN hk hn
  refine choice_le q c₁ (by linarith) ?_ ((length_le_rpow hk hn hlen).trans (two_rpow_mono h2 (by linarith)))
  calc ((2 ^ (c * n) * n ^ (c * k) : ℕ) : ℝ) = (2 : ℝ) ^ (((c * n : ℕ) : ℝ) + ((c * k : ℕ) : ℝ) * lg n) := by
        rw [Real.rpow_add two_pos, Real.rpow_natCast, ← natCast_pow_eq (by omega)]
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ (((c * (D + 1) : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have a1 := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
        have a2 := mul_le_mul_of_nonneg_left (mul_lg_le_expN hk hn) (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
        push_cast
        linarith
    _ ≤ _ := two_rpow_mono h1 (by linarith)

end PairsToBound
