/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.ThmVariablesADefs
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.Arith
import ClauseBound.Alg.End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The end of Step 5, and the «In particular» of Theorem D (a)

* `stepSparsifyFacts`: log K > (log n)/(17C₀) and log(k/e) ≤ (C₀ + 1/4)·log log n.
* `stepSparsifyLarge`: k·log n ≤ e·n for large n. `stepSparsifySmall`: for the finitely many smaller
  n, n and k·log n are O(k²·e·n·log(k/e)).
* `thmVariablesAInParticular`: if e_ℓ ≤ c·(log K_ℓ)^(−α′), a machine with the bound of Theorem D (a)
  takes at most 2^{O(k²·n·log log n/(log n)^α′)} steps. -/

public section

namespace VariableBound.VariablesA

open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)

/-- Step 5: «log K > (log n)/(17C₀), and log(k/e) ≤ (C₀ + 1/4)·log log n», for the level ℓ of n, K =
K_ℓ, e = e_ℓ and 1 ≤ k ≤ (log n)^(1/4). -/
theorem stepSparsifyFacts : StepSparsifyFactsStmt := by
  intro Idx _ S e C₀ Q k n l hl hk hk4
  have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast one_le_C₀ Q
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hy : 1 ≤ MainTheoremForms.lg n := (one_le_pow₀ hk').trans hk4
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  have he0 := e_pos Q l
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    have := lg_lt Q hl
    linarith
  · have h1 : MainTheoremForms.lg (k / e l) = MainTheoremForms.lg k - MainTheoremForms.lg (e l) := Real.logb_div (by positivity) he0.ne'
    have h2 : 4 * MainTheoremForms.lg k ≤ MainTheoremForms.lg (MainTheoremForms.lg n) := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hk4
      rw [Real.logb_pow] at this
      simpa [MainTheoremForms.lg] using this
    have h3 : -((C₀ : ℝ) * MainTheoremForms.lg (MainTheoremForms.lg n)) ≤ MainTheoremForms.lg (e l) := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (e_ge_n Q hl)
      rw [one_div, Real.logb_inv, Real.logb_pow] at this
      simpa [MainTheoremForms.lg] using this
    rw [h1]
    linarith

/-- log n ≤ n. -/
theorem lg_le_self (n : ℕ) : MainTheoremForms.lg n ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h, MainTheoremForms.lg]
  · rw [MainTheoremForms.lg, Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast h), Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

/-- Step 5: «k log n ≤ en for large n», where n is large if it exceeds a bound that depends only on
C₀; for k ≤ (log n)^(1/4) and e ≥ (log n)^(−C₀). -/
theorem stepSparsifyLarge : StepSparsifyLargeStmt := by
  intro C₀
  set c₃ : ℕ := 3 * (C₀ + 3).factorial * 2 ^ (C₀ + 3) with hc₃
  have hc₃1 : 1 ≤ c₃ := by
    have := Nat.factorial_pos (C₀ + 3)
    have h2 : 0 < 2 ^ (C₀ + 3) := by positivity
    have : 0 < 3 * (C₀ + 3).factorial * 2 ^ (C₀ + 3) := by positivity
    omega
  refine ⟨2 ^ c₃, fun k n x hn hk4 hx => ?_⟩
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hy : (c₃ : ℝ) ≤ MainTheoremForms.lg n := by
    rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_natCast]
    exact_mod_cast hn
  have hc₃' : (1 : ℝ) ≤ c₃ := by exact_mod_cast hc₃1
  have hy1 : 1 ≤ MainTheoremForms.lg n := hc₃'.trans hy
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  -- k ≤ log n
  have hky : (k : ℝ) ≤ MainTheoremForms.lg n := by
    refine le_trans ?_ hk4
    exact_mod_cast Nat.le_self_pow (by norm_num) k
  -- (log n)^(C₀+3) ≤ c₃·n, hence (log n)^(C₀+2) ≤ n
  have h1 : MainTheoremForms.lg n ^ (C₀ + 3) ≤ (c₃ : ℝ) * n := by
    refine le_trans (pow_le_pow_left₀ hy0.le ?_ _) (log_pow_le (C₀ + 3) hn1)
    exact Real.logb_le_logb_of_le (by norm_num) hn0 (by linarith)
  have h2 : MainTheoremForms.lg n ^ (C₀ + 2) ≤ n := by
    have h3 : (c₃ : ℝ) * MainTheoremForms.lg n ^ (C₀ + 2) ≤ (c₃ : ℝ) * n := by
      refine le_trans ?_ h1
      rw [pow_succ (MainTheoremForms.lg n) (C₀ + 2), mul_comm (MainTheoremForms.lg n ^ (C₀ + 2))]
      exact mul_le_mul_of_nonneg_right hy (by positivity)
    exact le_of_mul_le_mul_left h3 (by linarith)
  have h4 : MainTheoremForms.lg n ^ 2 ≤ 1 / MainTheoremForms.lg n ^ C₀ * n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), ← pow_add]
    rwa [add_comm] at h2
  calc (k : ℝ) * MainTheoremForms.lg n ≤ MainTheoremForms.lg n * MainTheoremForms.lg n := mul_le_mul_of_nonneg_right hky hy0.le
    _ = MainTheoremForms.lg n ^ 2 := (sq _).symm
    _ ≤ 1 / MainTheoremForms.lg n ^ C₀ * n := h4
    _ ≤ x * n := mul_le_mul_of_nonneg_right hx hn0.le

/-- Step 5: «For the finitely many smaller n …, trying all assignments is within the bound»: n ≤
c·k²·e·n·log(k/e) and k·log n ≤ c·k²·e·n·log(k/e) for 2 ≤ n < n₁, k ≥ 3 and (log n)^(−C₀) ≤ e ≤ 1,
with c depending on C₀ and n₁ only. -/
theorem stepSparsifySmall : StepSparsifySmallStmt := by
  intro C₀ n₁
  refine ⟨n₁ ^ C₀, fun k n x hn2 hn hk hx hx1 => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hy1 : 1 ≤ MainTheoremForms.lg n := by
    rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_one]
    exact_mod_cast hn2
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  have hyn : MainTheoremForms.lg n ≤ (n₁ : ℝ) := (lg_le_self n).trans (by exact_mod_cast hn.le)
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : 1 / (n₁ : ℝ) ^ C₀ ≤ x := le_trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hy0.le hyn _)) hx
  have hp : (0 : ℝ) < (n₁ : ℝ) ^ C₀ := pow_pos (by linarith) _
  have h2 : 1 ≤ (n₁ : ℝ) ^ C₀ * x := by
    rw [div_le_iff₀ hp] at h1
    linarith
  obtain ⟨w1, w2⟩ := lg_div_facts hk hx0 hx1
  have hw : 1 ≤ MainTheoremForms.lg (k / x) := w1.trans w2
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have h3 : 1 ≤ (k : ℝ) ^ 2 * MainTheoremForms.lg (k / x) := one_le_mul_of_one_le_of_one_le hk2 hw
  have h4 : 1 ≤ ((n₁ : ℝ) ^ C₀ * x) * ((k : ℝ) ^ 2 * MainTheoremForms.lg (k / x)) := one_le_mul_of_one_le_of_one_le h2 h3
  have h5 : (n : ℝ) ≤ ((n₁ ^ C₀ : ℕ) : ℝ) * expVariablesA k n x := by
    calc (n : ℝ) = n * 1 := (mul_one _).symm
      _ ≤ n * (((n₁ : ℝ) ^ C₀ * x) * ((k : ℝ) ^ 2 * MainTheoremForms.lg (k / x))) := mul_le_mul_of_nonneg_left h4 hn0.le
      _ = _ := by rw [expVariablesA]; push_cast; ring
  refine ⟨h5, ?_⟩
  have h6 : 1 ≤ ((n₁ : ℝ) ^ C₀ * x) * MainTheoremForms.lg (k / x) := one_le_mul_of_one_le_of_one_le h2 hw
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  calc (k : ℝ) * MainTheoremForms.lg n ≤ (k : ℝ) ^ 2 * n := mul_le_mul hkk (lg_le_self n) hy0.le (by positivity)
    _ = (k : ℝ) ^ 2 * n * 1 := (mul_one _).symm
    _ ≤ (k : ℝ) ^ 2 * n * (((n₁ : ℝ) ^ C₀ * x) * MainTheoremForms.lg (k / x)) := mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [expVariablesA]; push_cast; ring

/-- Theorem D (a), last sentence: if e_ℓ ≤ c·(log K_ℓ)^(−α′) for all ℓ, with α′ > 0, then a machine
with the bound of Theorem D (a) takes at most 2^{C'·k²·n·log log n/(log n)^α′} steps, for n ≥ K₀^17
and 3 ≤ k ≤ (log n)^(1/4). -/
theorem thmVariablesAInParticular : ThmVariablesAInParticular := by
  intro Idx _ S e C₀ Q α' c hα he M C hM
  set R : ℕ := ⌈((17 * C₀ : ℕ) : ℝ) ^ α'⌉₊ with hR
  refine ⟨C * (c * R * (C₀ + 1)), fun k n φ hn hk hk4 hφ => ?_⟩
  have hl := isLevel_pick Q hn
  set l := (Q.pick (ClauseBound.TopN.root17 n)).1.length with hldef
  obtain ⟨ev⟩ := hM k n l φ hl hk hk4 hφ
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  obtain ⟨f1, f2⟩ := stepSparsifyFacts Idx S e C₀ Q k n l hl (by omega) hk4
  have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast one_le_C₀ Q
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hy : 1 ≤ MainTheoremForms.lg n := (one_le_pow₀ (by linarith)).trans hk4
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  have hyy : 0 ≤ MainTheoremForms.lg (MainTheoremForms.lg n) := Real.logb_nonneg (by norm_num) hy
  have he0 := e_pos Q l
  obtain ⟨w1, w2⟩ := lg_div_facts hk he0 (Q.e_le l)
  have hw0 : 0 ≤ MainTheoremForms.lg (k / e l) := by linarith
  -- e ≤ c·R/(log n)^α′
  have h1 : e l ≤ (c : ℝ) * R / MainTheoremForms.lg n ^ α' := by
    refine (he l).trans ?_
    have g0 : (0 : ℝ) < ((17 * C₀ : ℕ) : ℝ) := by push_cast; positivity
    have g1 : (MainTheoremForms.lg n / ((17 * C₀ : ℕ) : ℝ)) ^ α' ≤ MainTheoremForms.lg (S.K (Q.idx l)) ^ α' := by
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      push_cast
      exact f1.le
    rw [Real.div_rpow hy0.le g0.le] at g1
    have g2 : 0 < MainTheoremForms.lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    have g3 : 0 < ((17 * C₀ : ℕ) : ℝ) ^ α' := Real.rpow_pos_of_pos g0 _
    have g4 : ((17 * C₀ : ℕ) : ℝ) ^ α' ≤ R := Nat.le_ceil _
    have g5 : 0 < MainTheoremForms.lg (S.K (Q.idx l)) ^ α' := lt_of_lt_of_le (by positivity) g1
    rw [div_le_div_iff₀ g5 g2]
    have g6 : MainTheoremForms.lg n ^ α' ≤ (R : ℝ) * MainTheoremForms.lg (S.K (Q.idx l)) ^ α' := by
      rw [div_le_iff₀ g3] at g1
      exact g1.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right g4 g5.le)
    calc (c : ℝ) * MainTheoremForms.lg n ^ α' ≤ c * ((R : ℝ) * MainTheoremForms.lg (S.K (Q.idx l)) ^ α') := mul_le_mul_of_nonneg_left g6 (by positivity)
      _ = _ := by ring
  have h2 : MainTheoremForms.lg (k / e l) ≤ ((C₀ : ℝ) + 1) * MainTheoremForms.lg (MainTheoremForms.lg n) := f2.trans (mul_le_mul_of_nonneg_right (by linarith) hyy)
  have h3 : expVariablesA k n (e l) ≤ ((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * MainTheoremForms.lg (MainTheoremForms.lg n) / MainTheoremForms.lg n ^ α') := by
    have g2 : 0 < MainTheoremForms.lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    calc expVariablesA k n (e l) = (k : ℝ) ^ 2 * n * (e l * MainTheoremForms.lg (k / e l)) := by rw [expVariablesA]; ring
      _ ≤ (k : ℝ) ^ 2 * n * (((c : ℝ) * R / MainTheoremForms.lg n ^ α') * (((C₀ : ℝ) + 1) * MainTheoremForms.lg (MainTheoremForms.lg n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hw0 (by positivity)) (by positivity)
      _ = _ := by push_cast; ring
  rw [timeVariablesA, timeVariablesAAlpha]
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  calc (C : ℝ) * expVariablesA k n (e l) ≤ (C : ℝ) * (((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * MainTheoremForms.lg (MainTheoremForms.lg n) / MainTheoremForms.lg n ^ α')) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by push_cast; ring

end VariableBound.VariablesA
