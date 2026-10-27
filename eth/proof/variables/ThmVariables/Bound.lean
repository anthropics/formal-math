/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmVariables.Defs
import RecursionToBound.Numbers
import VariableBound.Paper.Arith
import VariableBound.Printed.VariablesA.Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Theorem D (a) with the printed hypothesis: the arithmetic on K_ℓ and e_ℓ

* `exists_level`: every n ≥ K₀^17 has a level, «the largest ℓ with K_ℓ ≤ n^(1/17)», because K_ℓ > ℓ.
* `e_pos`, `e_ge_n`, `lg_lt`: e_ℓ > 0; at the level ℓ of n, e_ℓ ≥ (log n)^(−C₀) and log n <
  17·C₀·log K_ℓ (Step 5 of Appendix D: «log K > (log n)/(17C₀)»).
* `boundAtANumberBetween`: for 0 < e ≤ e′ ≤ 2e, e′ ≤ 1 ≤ k: log(k/e′) ≤ log(k/e), so
  k²·e′·n·log(k/e′) ≤ 2·k²·e·n·log(k/e).
* `inParticular`: the last sentence of Theorem D (a).
  proof/variables/VariableBound/Printed/VariablesA/StepSparsify.lean proves it for a solver with a
  sequence of levels (`MainTheoremForms.ThmVariablesAInParticular`). That form cannot be called
  here: a sequence of levels holds a polynomial-time program that picks the level, and here K is any
  sequence with the printed inequalities. So the argument is repeated
  on K: e ≤ c·(log K)^(−α′) ≤ c·(17C₀)^α′·(log n)^(−α′) and log(k/e) ≤ (C₀ + 1)·log log n. -/

public section

namespace ThmVariables

open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)

variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

/-! ### The levels -/

/-- For K, e, C₀ with the printed inequalities (`CliqueLevels.Levels`), every n ≥ K₀^17 has a level:
an ℓ with K_ℓ^17 ≤ n < K_(ℓ+1)^17. -/
theorem exists_level (hL : Levels K e C₀) {n : ℕ} (hn : K 0 ^ 17 ≤ n) : ∃ l, ThmVariables.IsLevel K n l := by
  have hmono : StrictMono K := strictMono_nat_of_lt_succ hL.K_lt
  refine ⟨Nat.findGreatest (fun l => K l ^ 17 ≤ n) n, Nat.findGreatest_spec (P := fun l => K l ^ 17 ≤ n) (Nat.zero_le n) hn, ?_⟩
  by_contra h
  have h' := not_lt.1 h
  have h1 := hmono.le_apply (x := Nat.findGreatest (fun l => K l ^ 17 ≤ n) n + 1)
  have h2 : K (Nat.findGreatest (fun l => K l ^ 17 ≤ n) n + 1) ≤ K (Nat.findGreatest (fun l => K l ^ 17 ≤ n) n + 1) ^ 17 := Nat.le_self_pow (by norm_num) _
  exact Nat.findGreatest_is_greatest (P := fun l => K l ^ 17 ≤ n) (Nat.lt_succ_self _) ((h1.trans h2).trans h') h'

/-- For K, e, C₀ with the printed inequalities (`CliqueLevels.Levels`): e_ℓ > 0. -/
theorem e_pos (hL : Levels K e C₀) (l : ℕ) : 0 < e l := by
  have h : 0 < Real.logb 2 (K l) := lt_of_lt_of_le one_pos (one_le_lg (hL.K_two l))
  exact lt_of_lt_of_le (by positivity) (hL.e_ge l)

/-- K_ℓ ≤ n at the level ℓ of n. -/
theorem K_le_n {n l : ℕ} (h : ThmVariables.IsLevel K n l) : K l ≤ n := (Nat.le_self_pow (by norm_num) _).trans h.1

/-- For K, e, C₀ with the printed inequalities (`CliqueLevels.Levels`): (log n)^(−C₀) ≤ e_ℓ at the
level ℓ of n. -/
theorem e_ge_n (hL : Levels K e C₀) {n l : ℕ} (h : ThmVariables.IsLevel K n l) : 1 / lg n ^ C₀ ≤ e l := by
  have h1 := one_le_lg (hL.K_two l)
  have h2 : lg (K l) ≤ lg n := lg_mono (by exact_mod_cast (by have := hL.K_two l; omega : 0 < K l)) (by exact_mod_cast K_le_n h)
  refine le_trans ?_ (hL.e_ge l)
  exact one_div_le_one_div_of_le (pow_pos (by linarith : 0 < lg (K l)) _) (pow_le_pow_left₀ (by linarith) h2 _)

/-- «log K > (log n)/(17C₀)»: for K, e, C₀ with the printed inequalities (`CliqueLevels.Levels`),
log n < 17·C₀·log K_ℓ at the level ℓ of n. -/
theorem lg_lt (hL : Levels K e C₀) {n l : ℕ} (h : ThmVariables.IsLevel K n l) : lg n < 17 * C₀ * lg (K l) := by
  have hn : 1 ≤ n := le_trans (by have := hL.K_two l; omega) (K_le_n h)
  have h1 : n < K l ^ (17 * C₀) := by
    calc n < K (l + 1) ^ 17 := h.2
      _ ≤ (K l ^ C₀) ^ 17 := Nat.pow_le_pow_left (hL.K_le l) 17
      _ = _ := by rw [← pow_mul, mul_comm]
  have h3 : (n : ℝ) < (K l : ℝ) ^ (17 * C₀) := by exact_mod_cast h1
  have h4 := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hn) h3
  rw [Real.logb_pow] at h4
  simpa [lg] using h4

/-! ### The bound at a number in [e, 2e] -/

/-- For 0 < e ≤ e′ ≤ 2e, e′ ≤ 1 ≤ k: k²·e′·n·log(k/e′) ≤ 2·k²·e·n·log(k/e). -/
theorem expVariablesA_le_two_mul {k n : ℕ} {e e' : ℝ} (hk : 1 ≤ k) (he : 0 < e) (h1 : e ≤ e') (h2 : e' ≤ 2 * e) (h3 : e' ≤ 1) : expVariablesA k n e' ≤ 2 * expVariablesA k n e := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he' : 0 < e' := lt_of_lt_of_le he h1
  have g0 : 0 ≤ lg (k / e') := Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ he']; linarith)
  have g1 : lg (k / e') ≤ lg (k / e) := lg_mono (by positivity) (div_le_div_of_nonneg_left (by linarith) he h1)
  unfold expVariablesA
  calc (k : ℝ) ^ 2 * e' * n * lg (k / e') ≤ (k : ℝ) ^ 2 * (2 * e) * n * lg (k / e) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (Nat.cast_nonneg n)) g1 g0 (by positivity)
    _ = 2 * ((k : ℝ) ^ 2 * e * n * lg (k / e)) := by ring

/-- The bound at a number in [e, 2e] is the bound at e with twice the constant: for 0 < e ≤ e′ ≤ 2e,
e′ ≤ 1 and k ≥ 1, 2^{C·k²·e′·n·log(k/e′)} ≤ 2^{2C·k²·e·n·log(k/e)}, both rounded down. -/
theorem boundAtANumberBetween : BoundAtANumberBetween := by
  intro C k n e e' hk he h1 h2 h3
  unfold timeVariablesA
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have := mul_le_mul_of_nonneg_left (expVariablesA_le_two_mul (n := n) hk he h1 h2 h3) (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  push_cast
  linarith

/-! ### «In particular» -/

/-- «In particular, if e_ℓ = O((log K_ℓ)^(−α′)) for a constant α′ > 0, the time is 2^{O(k²·n·log log
n/(log n)^α′)}» (Theorem D (a)), for every machine with the bound of Theorem D (a). -/
theorem inParticular : InParticular := by
  intro K e C₀ hL α' c hα he M C hM
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = ⌈((17 * C₀ : ℕ) : ℝ) ^ α'⌉₊ := ⟨_, rfl⟩
  refine ⟨C * (c * R * (C₀ + 1)), fun k n φ hn hk hk4 hφ => ?_⟩
  obtain ⟨l, hl⟩ := exists_level hL hn
  obtain ⟨ev⟩ := hM k n l φ hl hk hk4 hφ
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast hL.C₀_pos
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hy : 1 ≤ lg n := (one_le_pow₀ (by linarith)).trans hk4
  have hy0 : 0 < lg n := by linarith
  have hyy : 0 ≤ lg (lg n) := Real.logb_nonneg (by norm_num) hy
  have he0 := e_pos hL l
  have f1 : lg n / (17 * C₀) < lg (K l) := by
    rw [div_lt_iff₀ (by positivity)]
    have := lg_lt hL hl
    linarith
  have f2 := RecursionToBound.lg_div_le (k := k) (by omega) hk4 (e_ge_n hL hl)
  obtain ⟨w1, w2⟩ := VariableBound.VariablesA.lg_div_facts hk he0 (hL.e_le l)
  have hw0 : 0 ≤ lg (k / e l) := by linarith
  have h1 : e l ≤ (c : ℝ) * R / lg n ^ α' := by
    refine (he l).trans ?_
    have g0 : (0 : ℝ) < ((17 * C₀ : ℕ) : ℝ) := by push_cast; positivity
    have g1 : (lg n / ((17 * C₀ : ℕ) : ℝ)) ^ α' ≤ lg (K l) ^ α' := by
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      push_cast
      exact f1.le
    rw [Real.div_rpow hy0.le g0.le] at g1
    have g2 : 0 < lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    have g3 : 0 < ((17 * C₀ : ℕ) : ℝ) ^ α' := Real.rpow_pos_of_pos g0 _
    have g4 : ((17 * C₀ : ℕ) : ℝ) ^ α' ≤ R := hR ▸ Nat.le_ceil _
    have g5 : 0 < lg (K l) ^ α' := lt_of_lt_of_le (by positivity) g1
    rw [div_le_div_iff₀ g5 g2]
    have g6 : lg n ^ α' ≤ (R : ℝ) * lg (K l) ^ α' := by
      rw [div_le_iff₀ g3] at g1
      exact g1.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right g4 g5.le)
    calc (c : ℝ) * lg n ^ α' ≤ c * ((R : ℝ) * lg (K l) ^ α') := mul_le_mul_of_nonneg_left g6 (by positivity)
      _ = _ := by ring
  have h2 : lg (k / e l) ≤ ((C₀ : ℝ) + 1) * lg (lg n) := f2.trans (mul_le_mul_of_nonneg_right (by linarith) hyy)
  have h3 : expVariablesA k n (e l) ≤ ((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * lg (lg n) / lg n ^ α') := by
    have g2 : 0 < lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    calc expVariablesA k n (e l) = (k : ℝ) ^ 2 * n * (e l * lg (k / e l)) := by rw [expVariablesA]; ring
      _ ≤ (k : ℝ) ^ 2 * n * (((c : ℝ) * R / lg n ^ α') * (((C₀ : ℝ) + 1) * lg (lg n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hw0 (by positivity)) (by positivity)
      _ = _ := by push_cast; ring
  rw [timeVariablesA, timeVariablesAAlpha]
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  calc (C : ℝ) * expVariablesA k n (e l) ≤ (C : ℝ) * (((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * lg (lg n) / lg n ^ α')) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by push_cast; ring

end ThmVariables
