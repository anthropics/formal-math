/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top

/-! # Arithmetic for the exponent of the top level in m

A k-CNF with m clauses is turned into a network on g = 3K⁸ nodes and rebalanced to K nodes, where K =
K_l for the largest l with K_l⁹ ≤ m; then the clique solver
at level l is called. `needTop` is the exponent of a pad that suffices for all of this. This file
holds elementary inequalities on K and on the numbers of the top instance.

Among them:

* `root9 m` is the integer part of the ninth root of m (`root9_spec`);
* (log₂ K)ⁿ ≤ n!·2ⁿ·K (`logb_pow_le`), and the number of bits of K ≥ 2 is at most 2·log₂ K
  (`size_le_two_logb`);
* in natural numbers: g·P ≤ 5km, P·(2g/K + 1)·K ≤ 15km and K²·λ ≤ 8km for the numbers P and λ of the
  top instance (`g_mul_P_le`, `P_mul_le`, `sq_mul_lam_le`). -/

public section

namespace ClauseBound.Alg.TopArith

open PaddedDescent.F

/-! ### The ninth root -/

/-- For a property that passes to smaller numbers, the number of b < n that have it is the first
number below n that does not have it. -/
theorem lt_length_filter_iff (p : ℕ → Bool) (hp : ∀ a b, a ≤ b → p b = true → p a = true) (n : ℕ) :
    ∀ b < n, (p b = true ↔ b < ((List.range n).filter p).length) := by
  induction n with
  | zero => intro b hb; omega
  | succ n ih =>
    have hle : ((List.range n).filter p).length ≤ n := by
      simpa using List.length_filter_le p (List.range n)
    intro b hb
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hn : p n = true
    · have hlen : ((List.range n).filter p).length = n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · omega
        · have := (ih (n - 1) (by omega)).1 (hp _ _ (by omega) hn)
          omega
      simp only [hlen, List.filter_cons, hn, if_true, List.filter_nil, List.length_singleton]
      exact ⟨fun _ => hb, fun _ => hp b n (by omega) hn⟩
    · simp only [List.filter_cons, hn, List.filter_nil]
      rcases Nat.lt_or_ge b n with h | h
      · simpa using ih b h
      · have hbn : b = n := by omega
        subst hbn
        constructor
        · intro h'; exact absurd h' hn
        · intro h'; simp at h'; omega

/-- root9 m is the integer part of the ninth root of m. -/
theorem root9_spec (m : ℕ) : (root9 m).length ^ 9 ≤ m ∧ m < ((root9 m).length + 1) ^ 9 := by
  have hp : ∀ a b, a ≤ b → (fun b => decide (b ^ 9 ≤ m)) b = true → (fun b => decide (b ^ 9 ≤ m)) a = true := by
    intro a b hab hb
    simp only [decide_eq_true_eq] at hb ⊢
    exact (Nat.pow_le_pow_left hab 9).trans hb
  have key := lt_length_filter_iff (fun b => decide (b ^ 9 ≤ m)) hp (m + 1)
  have hcle : ((List.range (m + 1)).filter fun b => decide (b ^ 9 ≤ m)).length ≤ m + 1 := by
    simpa using List.length_filter_le (fun b => decide (b ^ 9 ≤ m)) (List.range (m + 1))
  have hlen : (root9 m).length = ((List.range (m + 1)).filter fun b => decide (b ^ 9 ≤ m)).length - 1 := by
    simp [root9]
  generalize ((List.range (m + 1)).filter fun b => decide (b ^ 9 ≤ m)).length = c at key hcle hlen
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
        _ ≤ (m + 1) ^ 9 := Nat.le_self_pow (by norm_num) _

/-! ### Logarithms -/

/-- log₂ x ≤ n if x ≤ 2ⁿ. -/
theorem logb_le_of_le_pow (x n : ℕ) (hx : 1 ≤ x) (h : x ≤ 2 ^ n) : Real.logb 2 x ≤ n := by
  have h' : (x : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  calc Real.logb 2 x ≤ Real.logb 2 ((2 : ℝ) ^ n) := Real.logb_le_logb_of_le (by norm_num) hx' h'
    _ = n := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- n ≤ log₂ x if 2ⁿ ≤ x. -/
theorem le_logb_of_pow_le (x n : ℕ) (h : 2 ^ n ≤ x) : (n : ℝ) ≤ Real.logb 2 x := by
  have h' : (2 : ℝ) ^ n ≤ (x : ℝ) := by exact_mod_cast h
  calc (n : ℝ) = Real.logb 2 ((2 : ℝ) ^ n) := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 x := Real.logb_le_logb_of_le (by norm_num) (by positivity) h'

/-- The number of bits of K ≥ 2 is at most 2·log₂ K. -/
theorem size_le_two_logb (K : ℕ) (hK : 2 ≤ K) : (K.size : ℝ) ≤ 2 * Real.logb 2 K := by
  have h1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hs : 0 < K.size := Nat.size_pos.2 (by omega)
  have h2 : 2 ^ (K.size - 1) ≤ K := Nat.lt_size.1 (by omega)
  have h3 := le_logb_of_pow_le K _ h2
  have h4 : ((K.size - 1 : ℕ) : ℝ) = (K.size : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  linarith

/-- (log₂ K)ⁿ ≤ n!·2ⁿ·K. -/
theorem logb_pow_le (K n : ℕ) (hK : 2 ≤ K) : Real.logb 2 K ^ n ≤ (n.factorial * 2 ^ n : ℕ) * (K : ℝ) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hK0 : (0 : ℝ) < K := by linarith
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  have h1 := Real.pow_div_factorial_le_exp (Real.log K) hlog n
  rw [Real.exp_log hK0] at h1
  have h2 : Real.log K ^ n ≤ n.factorial * K := by
    rwa [div_le_iff₀' (by positivity)] at h1
  have h3 : Real.logb 2 K ≤ 2 * Real.log K := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h2 : (1 : ℝ) - 2⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h2' : (1 : ℝ) / 2 ≤ Real.log 2 := by norm_num at h2 ⊢; linarith
    nlinarith
  have h4 : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) hK1
  calc Real.logb 2 K ^ n ≤ (2 * Real.log K) ^ n := pow_le_pow_left₀ h4 h3 n
    _ = 2 ^ n * Real.log K ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (n.factorial * K) := by gcongr
    _ = (n.factorial * 2 ^ n : ℕ) * (K : ℝ) := by push_cast; ring

/-! ### The numbers of the top instance -/

section
variable {K k m : ℕ}

/-- g·P ≤ 5km. -/
theorem g_mul_P_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : 3 * K ^ 8 * PtopK (3 * K ^ 8) k m ≤ 5 * (k * m) := by
  have hg : 2 * (3 * K ^ 8) ≤ 3 * m := by
    have : 2 * K ^ 8 ≤ K ^ 9 := by rw [pow_succ K 8, mul_comm]; exact Nat.mul_le_mul_left _ hK
    omega
  have hK8 : 0 < K ^ 8 := by positivity
  generalize 3 * K ^ 8 = g at hg ⊢
  have hq : g * ((m + g - 1) / g) ≤ m + g := (Nat.mul_div_le _ _).trans (by omega)
  have hkm : m ≤ k * m := Nat.le_mul_of_pos_left _ hk
  have hkg : 2 * (k * g) ≤ 3 * (k * m) := by
    calc 2 * (k * g) = k * (2 * g) := by ring
      _ ≤ k * (3 * m) := Nat.mul_le_mul_left _ hg
      _ = 3 * (k * m) := by ring
  unfold PtopK
  rcases max_cases 1 (2 * k * ((m + g - 1) / g)) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; omega
  · rw [h]
    calc g * (2 * k * ((m + g - 1) / g)) = 2 * k * (g * ((m + g - 1) / g)) := by ring
      _ ≤ 2 * k * (m + g) := Nat.mul_le_mul_left _ hq
      _ = 2 * (k * m) + 2 * (k * g) := by ring
      _ ≤ 5 * (k * m) := by omega

/-- 2g/K = 6K⁷. -/
theorem two_g_div (hK : 2 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by
  have : 2 * (3 * K ^ 8) = 6 * K ^ 7 * K := by ring
  rw [this, Nat.mul_div_cancel _ (by omega)]

/-- P·(2g/K + 1)·K ≤ 15km. -/
theorem P_mul_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) * K ≤ 15 * (k * m) := by
  have h := g_mul_P_le hK hk hm
  rw [two_g_div hK]
  have h1 : (6 * K ^ 7 + 1) * K ≤ 3 * (3 * K ^ 8) := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) _
    calc (6 * K ^ 7 + 1) * K = 6 * K ^ 8 + K := by ring
      _ ≤ 3 * (3 * K ^ 8) := by omega
  calc PtopK (3 * K ^ 8) k m * (6 * K ^ 7 + 1) * K = PtopK (3 * K ^ 8) k m * ((6 * K ^ 7 + 1) * K) := by ring
    _ ≤ PtopK (3 * K ^ 8) k m * (3 * (3 * K ^ 8)) := Nat.mul_le_mul_left _ h1
    _ = 3 * (3 * K ^ 8 * PtopK (3 * K ^ 8) k m) := by ring
    _ ≤ 15 * (k * m) := by omega

/-- K³ ≤ km. -/
theorem cube_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : K ^ 3 ≤ k * m :=
  calc K ^ 3 ≤ K ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ m := hm
    _ ≤ k * m := Nat.le_mul_of_pos_left _ hk

/-- K²·λ ≤ 8km. -/
theorem sq_mul_lam_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : K ^ 2 * lamTopK K (3 * K ^ 8) k m ≤ 8 * (k * m) := by
  have h := g_mul_P_le hK hk hm
  have h3 := cube_le hK hk hm
  have hd : lamTopK K (3 * K ^ 8) k m * K ^ 3 ≤ K ^ 3 + K * (2 * k * m) + 3 * K ^ 8 * PtopK (3 * K ^ 8) k m := Nat.div_mul_le_self _ _
  have hK0 : 0 < K := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hK0
  have h5 : 5 * (k * m) ≤ 5 * (k * m) * K := Nat.le_mul_of_pos_right _ hK0
  have h6 : K ^ 3 ≤ k * m * K := h3.trans (Nat.le_mul_of_pos_right _ hK0)
  calc K ^ 2 * lamTopK K (3 * K ^ 8) k m * K = lamTopK K (3 * K ^ 8) k m * K ^ 3 := by ring
    _ ≤ K ^ 3 + K * (2 * k * m) + 3 * K ^ 8 * PtopK (3 * K ^ 8) k m := hd
    _ ≤ k * m * K + K * (2 * k * m) + 5 * (k * m) * K := by omega
    _ = 8 * (k * m) * K := by ring

/-- λ ≥ 1. -/
theorem one_le_lam (hK : 2 ≤ K) : 1 ≤ lamTopK K (3 * K ^ 8) k m := by
  unfold lamTopK
  rw [Nat.one_le_div_iff (by positivity)]
  omega

/-- The bound for the entries of the top instance is at least 1. -/
theorem one_le_B (hK : 2 ≤ K) : 1 ≤ PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) := by
  rw [two_g_div hK]
  have h1 : 1 ≤ PtopK (3 * K ^ 8) k m := le_max_left _ _
  have h2 : 1 ≤ 6 * K ^ 7 := by have : 0 < K ^ 7 := by positivity
                                omega
  exact Nat.mul_le_mul h1 h2

end

end ClauseBound.Alg.TopArith
