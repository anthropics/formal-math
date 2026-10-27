/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.ThmVariablesADefs
public import ClauseBound.TopN.Defs
import all ClauseBound.TopN.Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # The level of n

For a sequence Q of levels, «the largest ℓ with K_ℓ ≤ n^(1/17)» is the ℓ with K_ℓ^17 ≤ n <
K_(ℓ+1)^17 (`MainTheoremForms.IsLevel`).
* `level_unique`: a number has at most one level. `isLevel_pick`: every n ≥ K₀^17 has a level, the
  one that `Q.pick` gives for ⌊n^(1/17)⌋; `level_eq_pick`: every level is that one.
* At the level ℓ of n: 2 ≤ K_ℓ ≤ n, 1 ≤ log K_ℓ ≤ log n, 0 < e_ℓ, (log n)^(−C₀) ≤ e_ℓ, and log n <
  17·C₀·log K_ℓ. -/

public section

namespace VariableBound.VariablesA

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms

variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

/-- K_ℓ increases strictly with ℓ. -/
theorem K_strictMono : StrictMono fun l => S.K (Q.idx l) := strictMono_nat_of_lt_succ Q.K_lt

/-- A number has at most one level. -/
theorem level_unique {n l l' : ℕ} (h : IsLevel S Q n l) (h' : IsLevel S Q n l') : l = l' := by
  have key : ∀ a b : ℕ, IsLevel S Q n a → IsLevel S Q n b → ¬ a < b := by
    intro a b ha hb hab
    have h1 : S.K (Q.idx (a + 1)) ≤ S.K (Q.idx b) := (K_strictMono Q).monotone hab
    exact absurd ((Nat.pow_le_pow_left h1 17).trans hb.1) (not_le.2 ha.2)
  exact le_antisymm (not_lt.1 (key _ _ h' h)) (not_lt.1 (key _ _ h h'))

/-- The level that `Q.pick` gives for ⌊n^(1/17)⌋ is the level of n, for n ≥ K₀^17. -/
theorem isLevel_pick {n : ℕ} (hn : S.K (Q.idx 0) ^ 17 ≤ n) : IsLevel S Q n (Q.pick (root17 n)).1.length := by
  obtain ⟨hr1, hr2⟩ := root17_spec n
  have hK0 : S.K (Q.idx 0) ≤ (root17 n).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
    exact absurd (h'.trans hn) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root17 n)
  rw [Q.pick_idx] at hle
  exact ⟨(Nat.pow_le_pow_left hle 17).trans hr1, hr2.trans_le (Nat.pow_le_pow_left (Nat.succ_le_of_lt hmax) 17)⟩

/-- The level of n is the one picked. -/
theorem level_eq_pick {n l : ℕ} (h : IsLevel S Q n l) : (Q.pick (root17 n)).1.length = l := by
  have h0 : S.K (Q.idx 0) ^ 17 ≤ n := (Nat.pow_le_pow_left ((K_strictMono Q).monotone (Nat.zero_le l)) 17).trans h.1
  exact level_unique Q (isLevel_pick Q h0) h

/-! ### What the hypothesis gives at the level of n -/

/-- 1 ≤ log K_ℓ. -/
theorem one_le_lgK (l : ℕ) : 1 ≤ MainTheoremForms.lg (S.K (Q.idx l)) := by
  have h : (2 : ℝ) ≤ S.K (Q.idx l) := by exact_mod_cast Q.K_two l
  rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  exact h

include Q in
/-- e_ℓ is positive. -/
theorem e_pos (l : ℕ) : 0 < e l := by
  have h := one_le_lgK Q l
  have h1 : 0 < 1 / Real.logb 2 (S.K (Q.idx l)) ^ C₀ := by
    have : 0 < Real.logb 2 (S.K (Q.idx l)) := lt_of_lt_of_le one_pos h
    positivity
  exact lt_of_lt_of_le h1 (Q.e_ge l)

/-- K_ℓ ≤ n at the level ℓ of n. -/
theorem K_le_n {n l : ℕ} (h : IsLevel S Q n l) : S.K (Q.idx l) ≤ n :=
  (Nat.le_self_pow (by norm_num) _).trans h.1

/-- log K_ℓ ≤ log n at the level ℓ of n. -/
theorem lgK_le {n l : ℕ} (h : IsLevel S Q n l) : MainTheoremForms.lg (S.K (Q.idx l)) ≤ MainTheoremForms.lg n := by
  have h2 : (2 : ℝ) ≤ S.K (Q.idx l) := by exact_mod_cast Q.K_two l
  exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast K_le_n Q h)

/-- (log n)^(−C₀) ≤ e_ℓ at the level ℓ of n. -/
theorem e_ge_n {n l : ℕ} (h : IsLevel S Q n l) : 1 / MainTheoremForms.lg n ^ C₀ ≤ e l := by
  have h1 := one_le_lgK Q l
  refine le_trans ?_ (Q.e_ge l)
  exact one_div_le_one_div_of_le (by have : 0 < MainTheoremForms.lg (S.K (Q.idx l)) := by linarith
                                     exact pow_pos this _) (pow_le_pow_left₀ (by linarith) (lgK_le Q h) _)

/-- Step 5: log n < 17·C₀·log K_ℓ at the level ℓ of n. -/
theorem lg_lt {n l : ℕ} (h : IsLevel S Q n l) : MainTheoremForms.lg n < 17 * C₀ * MainTheoremForms.lg (S.K (Q.idx l)) := by
  have h2 : (2 : ℝ) ≤ S.K (Q.idx l) := by exact_mod_cast Q.K_two l
  have hn : 1 ≤ n := le_trans (by have := Q.K_two l; omega) (K_le_n Q h)
  have h1 : n < S.K (Q.idx l) ^ (17 * C₀) := by
    calc n < S.K (Q.idx (l + 1)) ^ 17 := h.2
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 17 := Nat.pow_le_pow_left (Q.K_le l) 17
      _ = _ := by rw [← pow_mul, mul_comm]
  have h3 : (n : ℝ) < (S.K (Q.idx l) : ℝ) ^ (17 * C₀) := by exact_mod_cast h1
  have h4 := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hn) h3
  rw [Real.logb_pow] at h4
  simpa [MainTheoremForms.lg] using h4

include Q in
/-- C₀ ≥ 1. -/
theorem one_le_C₀ : 1 ≤ C₀ := by
  rcases Nat.eq_zero_or_pos C₀ with h | h
  · have h1 := Q.K_le 0
    have h2 := Q.K_two (0 + 1)
    have h3 : S.K (Q.idx 0) ^ C₀ = 1 := by simp [h]
    rw [h3] at h1
    omega
  · exact h

end VariableBound.VariablesA
