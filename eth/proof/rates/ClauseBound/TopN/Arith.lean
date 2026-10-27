/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
import ClauseBound.Alg.TopArith
import ClauseBound.TopN.Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! # Arithmetic lemmas in natural numbers: the seventeenth root, β, W and λ

Notation: K the number of nodes, Y = `K.size` the number of binary digits of K, s the precision, β =
`betaN k s`, b = β + 3, D = 2^β, W = `Wof k K s` = b²·D·Y.
* `root17_spec`: the integer part of the seventeenth root; `eq_replicate`: lists of units. `b_le_D`,
  `b_le_lin`, `k_le_beta`: bounds on β, among them b ≤ c_k·(s+1). `pow_le_n`: K^j ≤ n for j ≤ 17.
* `Wof_ge`: W dominates b·D, b²·Y, b², b·Y, Y, b, D and 1. `succ_le_two_pow`, `size_n_le`: if n <
  K^(17·C₀), then n has at most 17·C₀·Y binary digits.
* `two_g_div`, `lamS_mul_le`, `one_le_lamS`: 2g/K = 6K⁷ for g = 3K⁸, and bounds on the label length
  λ of the rebalanced instance. -/

namespace ClauseBound.TopN.Arith

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith

/-! ### The seventeenth root, and lists of units -/

/-- The length of `root17 m` is the integer part of the seventeenth root of m. -/
theorem root17_spec (m : ℕ) : (root17 m).length ^ 17 ≤ m ∧ m < ((root17 m).length + 1) ^ 17 := by
  have hp : ∀ a b, a ≤ b → (fun b => decide (b ^ 17 ≤ m)) b = true → (fun b => decide (b ^ 17 ≤ m)) a = true := by
    intro a b hab hb
    simp only [decide_eq_true_eq] at hb ⊢
    exact (Nat.pow_le_pow_left hab 17).trans hb
  have key := lt_length_filter_iff (fun b => decide (b ^ 17 ≤ m)) hp (m + 1)
  have hcle : ((List.range (m + 1)).filter fun b => decide (b ^ 17 ≤ m)).length ≤ m + 1 := by
    simpa using List.length_filter_le (fun b => decide (b ^ 17 ≤ m)) (List.range (m + 1))
  have hlen : (root17 m).length = ((List.range (m + 1)).filter fun b => decide (b ^ 17 ≤ m)).length - 1 := by
    simp [root17]
  generalize ((List.range (m + 1)).filter fun b => decide (b ^ 17 ≤ m)).length = c at key hcle hlen
  simp only [decide_eq_true_eq] at key
  have hc0 : 0 < c := (key 0 (by omega)).1 (by simp)
  rw [hlen]
  constructor
  · exact (key (c - 1) (by omega)).2 (by omega)
  · have e : c - 1 + 1 = c := by omega
    rw [e]
    rcases Nat.lt_or_ge c (m + 1) with h | h
    · by_contra hcon
      have := (key c h).1 (by omega)
      omega
    · have hcm : c = m + 1 := by omega
      rw [hcm]
      calc m < m + 1 := by omega
        _ ≤ (m + 1) ^ 17 := Nat.le_self_pow (by norm_num) _

/-- A list of units is determined by its length. -/
theorem eq_replicate (u : U) : u = List.replicate u.length () := List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩

/-! ### Natural numbers -/

section nat

variable {k K n s : ℕ}

/-- β + 3 ≤ 2^β. -/
theorem b_le_D (k s : ℕ) : betaN k s + 3 ≤ 2 ^ betaN k s := by
  have h3 : 3 ≤ betaN k s := by unfold betaN; omega
  obtain ⟨t, ht⟩ : ∃ t, betaN k s = t + 3 := ⟨betaN k s - 3, by omega⟩
  have h : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  rw [ht, pow_add]
  omega

/-- β + 3 ≤ c_k·(s+1). -/
theorem b_le_lin (k s : ℕ) : betaN k s + 3 ≤ (17 * (2 ^ (k + 1) + 1) + k + 6) * (s + 1) := by
  unfold betaN
  generalize 2 ^ (k + 1) + 1 = c
  nlinarith [Nat.zero_le (c * s), Nat.zero_le (k * s), Nat.zero_le s]

/-- k ≤ β. -/
theorem k_le_beta (k s : ℕ) : k ≤ betaN k s := by unfold betaN; omega

/-- Powers of K up to the seventeenth are at most n. -/
theorem pow_le_n (hK : 1 ≤ K) (hn : K ^ 17 ≤ n) {j : ℕ} (hj : j ≤ 17) : K ^ j ≤ n := (Nat.pow_le_pow_right hK hj).trans hn

/-- 2g/K = 6K⁷. -/
theorem two_g_div (hK : 1 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by
  rw [show 2 * (3 * K ^ 8) = 6 * K ^ 7 * K by ring]
  exact Nat.mul_div_cancel _ hK

/-- K²·λ·K ≤ K³ + K·Ub + g·P for the label length λ of the rebalanced instance. -/
theorem lamS_mul_le (K g Ub P : ℕ) : lamS K g Ub P * K ^ 3 ≤ K ^ 3 + K * Ub + g * P := Nat.div_mul_le_self _ _

/-- 1 ≤ λ. -/
theorem one_le_lamS (hK : 1 ≤ K) (g Ub P : ℕ) : 1 ≤ lamS K g Ub P := by
  unfold lamS
  rw [Nat.le_div_iff_mul_le (by positivity)]
  omega

end nat

/-! ### The number W, and the binary digits of n -/

section lower

variable {k K n s C₀ : ℕ}

/-- W = b²·D·Y. -/
def Wof (k K s : ℕ) : ℕ := (betaN k s + 3) ^ 2 * 2 ^ betaN k s * K.size

/-- What is used of W: it dominates b·D, b²·Y, b·Y and 1. -/
theorem Wof_ge (hK : 1 ≤ K) : (betaN k s + 3) * 2 ^ betaN k s ≤ Wof k K s ∧ (betaN k s + 3) ^ 2 * K.size ≤ Wof k K s ∧
    (betaN k s + 3) ^ 2 ≤ Wof k K s ∧ (betaN k s + 3) * K.size ≤ Wof k K s ∧ K.size ≤ Wof k K s ∧ betaN k s + 3 ≤ Wof k K s ∧ 2 ^ betaN k s ≤ Wof k K s ∧ 1 ≤ Wof k K s := by
  unfold Wof
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK
  have hD : 1 ≤ 2 ^ betaN k s := Nat.one_le_two_pow
  generalize K.size = Y at hY
  generalize 2 ^ betaN k s = D at hD
  have hb : 1 ≤ betaN k s + 3 := by omega
  generalize betaN k s + 3 = b at hb
  have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have m1 : b * D ≤ b ^ 2 * D * Y := by
    calc b * D ≤ b ^ 2 * D := Nat.mul_le_mul_right _ hbb
      _ ≤ b ^ 2 * D * Y := Nat.le_mul_of_pos_right _ hY
  have m2 : b ^ 2 * Y ≤ b ^ 2 * D * Y := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hD)
  have m3 : b ^ 2 ≤ b ^ 2 * Y := Nat.le_mul_of_pos_right _ hY
  have m4 : b * Y ≤ b ^ 2 * Y := Nat.mul_le_mul_right _ hbb
  have m5 : Y ≤ b ^ 2 * Y := Nat.le_mul_of_pos_left _ h1
  have m6 : D ≤ b * D := Nat.le_mul_of_pos_left _ hb
  exact ⟨m1, m2, m3.trans m2, m4.trans m2, m5.trans m2, (hbb.trans m3).trans m2, m6.trans m1, (h1.trans m3).trans m2⟩

/-- n + 1 ≤ 2^(17·C₀·Y). -/
theorem succ_le_two_pow (hlt : n < K ^ (17 * C₀)) : n + 1 ≤ 2 ^ (17 * C₀ * K.size) := by
  have h1 : K ≤ 2 ^ K.size := (Nat.lt_size_self K).le
  calc n + 1 ≤ K ^ (17 * C₀) := hlt
    _ ≤ (2 ^ K.size) ^ (17 * C₀) := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (17 * C₀ * K.size) := by rw [← pow_mul, Nat.mul_comm]

/-- The number of binary digits of n is at most 17·C₀·Y. -/
theorem size_n_le (hlt : n < K ^ (17 * C₀)) : n.size ≤ 17 * C₀ * K.size := Nat.size_le.2 (succ_le_two_pow hlt)

end lower

end ClauseBound.TopN.Arith
