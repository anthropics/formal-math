/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Params.Defs
import ClauseBound.ParityChecks.Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Setting and parameters of Appendix D: the inequalities of the paragraph

With L = log(2Δ), the definition of n̄ says n̄·L ≤ n < 2·n̄·L (`nb_mul_le`, `lt_nb_mul`). From this
and the bound log C(t, μ) ≤ μ'·max{1, log(3t/μ')} of the paragraph, which is `binom`, proved in
proof/rates/ClauseBound/ParityChecks/Binom.lean, follow the bounds on s̄, on 3m/(n̄+1) and on β.
In the docstrings n̄ stands for any number with `IsNb n Δ n̄`; where a statement needs the r̄ or t̄
defined in the paper (`IsRb`, `IsTb`) rather than an arbitrary number, its docstring says so.
The bound r̄ ≤ 2.41·β + 1 comes from (4/3)^241 > 2^100 and the minimality of r̄. The bounds r̄ ≤ 10n
and M ≤ 14n are proved for n ≥ 29·L + 19. The bound on t̄ uses log(1+p) ≤ (3/2)·p and the minimality
of t̄. -/

public section

namespace VariableBound

open AppVariables

namespace Ineq

/-- log(2Δ) ≥ 2 for Δ ≥ 2. -/
theorem two_le_lg {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ≤ lg (2 * Δ) := by
  have h : (2 : ℝ) ^ (2 : ℕ) ≤ 2 * Δ := by
    have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at h2

/-- log(2Δ) ≤ 2Δ for Δ ≥ 1. -/
theorem lg_le {Δ : ℕ} (hΔ : 1 ≤ Δ) : lg (2 * Δ) ≤ 2 * Δ := by
  have h : ((2 * Δ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * Δ) := by exact_mod_cast (Nat.lt_two_pow_self (n := 2 * Δ)).le
  have h0 : (0 : ℝ) < ((2 * Δ : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * Δ)
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) h0 h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  push_cast at h2
  exact h2

/-- n̄·log(2Δ) ≤ n, for Δ ≥ 1. -/
theorem nb_mul_le {n Δ nb : ℕ} (hΔ : 1 ≤ Δ) (h : IsNb n Δ nb) : (nb : ℝ) * lg (2 * Δ) ≤ n := by
  have h1 : ((2 : ℝ) * Δ) ^ nb ≤ 2 ^ n := by exact_mod_cast h.2.1
  have h0 : (0 : ℝ) < 2 * Δ := by
    have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (pow_pos h0 nb) h1
  rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2

/-- n < 2·n̄·log(2Δ). -/
theorem lt_nb_mul {n Δ nb : ℕ} (h : IsNb n Δ nb) : (n : ℝ) < 2 * nb * lg (2 * Δ) := by
  have h1 : (2 : ℝ) ^ n < ((2 : ℝ) * Δ) ^ (2 * nb) := by exact_mod_cast h.2.2
  have h2 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  push_cast at h2
  exact h2

/-- The bound on binomial coefficients of «Setting and parameters»: log C(t, μ) ≤ μ'·max{1,
log(3t/μ')} for integers t ≥ 0, 0 ≤ μ ≤ μ' and μ' ≥ 1. -/
theorem binom {t μ μ' : ℕ} (h : μ ≤ μ') (h1 : 1 ≤ μ') : lg (t.choose μ) ≤ μ' * max 1 (lg (3 * t / μ')) := ClauseBound.ParityChecks.logb_choose_le h h1

/-- n̄ ≥ 1. -/
theorem nb_pos {n Δ nb : ℕ} (h : IsNb n Δ nb) : (1 : ℝ) ≤ nb := by
  obtain ⟨a, rfl⟩ := h.1
  exact_mod_cast Nat.one_le_two_pow

/-- m/n̄ < 2Δ·log(2Δ), for 2 ≤ Δ and m ≤ Δ·n. -/
theorem m_div_lt {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) : (m : ℝ) / nb < 2 * Δ * lg (2 * Δ) := by
  have hnb := nb_pos h
  have h1 := lt_nb_mul h
  have h2 : (m : ℝ) ≤ Δ * n := by exact_mod_cast hm
  have h3 : (0 : ℝ) < Δ := by exact_mod_cast (by omega : 0 < Δ)
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- 3m/(n̄+1) < 6Δ·log(2Δ), for 2 ≤ Δ and m ≤ Δ·n. -/
theorem three_m_lt {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) : 3 * (m : ℝ) / (nb + 1) < 6 * Δ * lg (2 * Δ) := by
  have hnb := nb_pos h
  have h1 := m_div_lt hΔ hm h
  have h2 : (m : ℝ) / (nb + 1) ≤ m / nb := div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by linarith) (by linarith)
  rw [mul_div_assoc]
  linarith

/-- 6Δ·log(2Δ) ≤ (2Δ)³, for Δ ≥ 2. -/
theorem six_le {Δ : ℕ} (hΔ : 2 ≤ Δ) : 6 * (Δ : ℝ) * lg (2 * Δ) ≤ (2 * Δ) ^ 3 := by
  have h1 := lg_le (Δ := Δ) (by omega)
  have h2 : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have h3 : 6 * (Δ : ℝ) * lg (2 * Δ) ≤ 6 * Δ * (2 * Δ) := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Δ) (by linarith : (0 : ℝ) ≤ Δ)) (by linarith : (0 : ℝ) ≤ Δ - 2)]

/-- β ≤ n + 3(n̄+1)·log(2Δ) + 2, for 2 ≤ Δ and n̄ < m ≤ Δ·n. -/
theorem beta_le₁ {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) :
    (beta n m nb : ℝ) ≤ n + 3 * (nb + 1) * lg (2 * Δ) + 2 := by
  have hL := two_le_lg hΔ
  have hc := ClauseBound.ParityChecks.Binom.clog_le_logb_add_one (x := m.choose (nb + 1)) (Nat.choose_pos hnm)
  have hb : Real.logb 2 (m.choose (nb + 1)) ≤ ((nb + 1 : ℕ) : ℝ) * max 1 (Real.logb 2 (3 * m / ((nb + 1 : ℕ) : ℝ))) :=
    binom (t := m) (μ := nb + 1) (μ' := nb + 1) le_rfl (Nat.le_add_left 1 nb)
  have h0 : (0 : ℝ) < 3 * m / (nb + 1) := by
    have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have h3 : Real.logb 2 (3 * m / (nb + 1)) ≤ 3 * lg (2 * Δ) := by
    have h4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) h0 ((three_m_lt hΔ hm h).le.trans (six_le hΔ))
    rwa [Real.logb_pow, Nat.cast_ofNat] at h4
  have h5 : max 1 (Real.logb 2 (3 * m / (nb + 1))) ≤ 3 * lg (2 * Δ) := max_le (by linarith) h3
  have h6 : ((nb + 1 : ℕ) : ℝ) * max 1 (Real.logb 2 (3 * m / ((nb + 1 : ℕ) : ℝ))) ≤ (nb + 1) * (3 * lg (2 * Δ)) := by
    push_cast
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  unfold beta
  push_cast
  linarith

/-- n + 3(n̄+1)·log(2Δ) + 2 ≤ 4n + 3·log(2Δ) + 2, for Δ ≥ 1. -/
theorem beta_le₂ {n Δ nb : ℕ} (hΔ : 1 ≤ Δ) (h : IsNb n Δ nb) : (n : ℝ) + 3 * (nb + 1) * lg (2 * Δ) + 2 ≤ 4 * n + 3 * lg (2 * Δ) + 2 := by
  have h1 := nb_mul_le hΔ h
  linarith

/-- r̄ ≤ 2.41·β + 1 for the r̄ of the text (`IsRb β r̄`), because 2.41·log(4/3) > 1. -/
theorem rb_le {β rb : ℕ} (h : IsRb β rb) : (rb : ℝ) ≤ 2.41 * β + 1 := by
  rcases Nat.eq_zero_or_pos rb with rfl | hpos
  · have : (0 : ℝ) ≤ β := Nat.cast_nonneg β
    push_cast
    linarith
  · obtain ⟨j, rfl⟩ : ∃ j, rb = j + 1 := ⟨rb - 1, by omega⟩
    have h1 : 4 ^ j ≤ 3 ^ j * 2 ^ β := not_lt.1 (h.2 j (Nat.lt_succ_self j))
    have h2 : (2 : ℕ) ^ 100 * 3 ^ 241 ≤ 4 ^ 241 := by norm_num
    have h3 : 2 ^ (100 * j) * 3 ^ (241 * j) ≤ 2 ^ (241 * β) * 3 ^ (241 * j) := by
      calc 2 ^ (100 * j) * 3 ^ (241 * j) = (2 ^ 100 * 3 ^ 241) ^ j := by rw [mul_pow, ← pow_mul, ← pow_mul]
        _ ≤ (4 ^ 241) ^ j := Nat.pow_le_pow_left h2 j
        _ = (4 ^ j) ^ 241 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (3 ^ j * 2 ^ β) ^ 241 := Nat.pow_le_pow_left h1 241
        _ = 2 ^ (241 * β) * 3 ^ (241 * j) := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm, mul_comm β, mul_comm j]
    have h4 : 100 * j ≤ 241 * β := (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_right h3 (by positivity))
    have h5 : (100 : ℝ) * j ≤ 241 * β := by exact_mod_cast h4
    push_cast
    linarith

/-- The bounds for large n: r̄ ≤ 10n and M ≤ 14n for the β, r̄ and M of the text, for 2 ≤ Δ, n̄ < m
≤ Δ·n and n ≥ 29·log(2Δ) + 19. -/
theorem large {n Δ m nb rb : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) (hr : IsRb (beta n m nb) rb)
    (hn : 29 * lg (2 * Δ) + 19 ≤ n) : rb ≤ 10 * n ∧ Mb (beta n m nb) rb ≤ 14 * n := by
  have hL := two_le_lg hΔ
  have h1 := (beta_le₁ hΔ hnm hm h).trans (beta_le₂ (by omega) h)
  have h2 := rb_le hr
  have hβ : 1 ≤ beta n m nb := by unfold beta; omega
  constructor
  · have : (rb : ℝ) ≤ ((10 * n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : ((Mb (beta n m nb) rb : ℕ) : ℝ) ≤ ((14 * n : ℕ) : ℝ) := by
      unfold Mb
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    exact_mod_cast this

/-- p·r̄ < 22·log(2Δ), for 2 ≤ Δ and any number r̄ ≤ 10n. -/
theorem p_rb {n Δ nb rb : ℕ} (hΔ : 2 ≤ Δ) (h : IsNb n Δ nb) (hr : rb ≤ 10 * n) : ((pp nb : ℚ) : ℝ) * rb < 22 * lg (2 * Δ) := by
  have hL := two_le_lg hΔ
  have hnb := nb_pos h
  have h1 := lt_nb_mul h
  have h2 : (rb : ℝ) ≤ 10 * n := by exact_mod_cast hr
  unfold pp
  push_cast
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

/-- log(1+p) ≤ (3/2)·p for p ≥ 0. -/
theorem lg_one_add_le {p : ℝ} (hp : 0 ≤ p) : lg (1 + p) ≤ 3 / 2 * p := by
  have h1 : Real.log (1 + p) ≤ p := by
    have := Real.log_le_sub_one_of_pos (x := 1 + p) (by linarith)
    linarith
  have h2 := Real.log_two_gt_d9
  unfold lg Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- t̄ ≤ log m + 33·log(2Δ) + 1 for the t̄ of the text (`IsTb m n̄ r̄ t̄`), for 2 ≤ Δ, m ≥ 1 and any
number r̄ ≤ 10n. -/
theorem tb_le {n Δ m nb rb tb : ℕ} (hΔ : 2 ≤ Δ) (hm : 1 ≤ m) (h : IsNb n Δ nb) (hr : rb ≤ 10 * n) (ht : IsTb m nb rb tb) :
    (tb : ℝ) ≤ lg m + 33 * lg (2 * Δ) + 1 := by
  have hL := two_le_lg hΔ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlm : 0 ≤ lg m := Real.logb_nonneg (by norm_num) hm1
  rcases Nat.eq_zero_or_pos tb with rfl | hpos
  · push_cast
    linarith
  · obtain ⟨c, rfl⟩ : ∃ c, tb = c + 1 := ⟨tb - 1, by omega⟩
    have h1 : (2 : ℚ) ^ c < (m : ℚ) * (1 + pp nb) ^ rb := not_le.1 (ht.2 c (Nat.lt_succ_self c))
    have h2 : (2 : ℝ) ^ c < (m : ℝ) * (1 + ((pp nb : ℚ) : ℝ)) ^ rb := by exact_mod_cast h1
    have hp : (0 : ℝ) ≤ ((pp nb : ℚ) : ℝ) := by
      unfold pp
      push_cast
      positivity
    have h3 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h2
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Real.logb_mul (by linarith) (by positivity), Real.logb_pow] at h3
    have h4 : (rb : ℝ) * Real.logb 2 (1 + ((pp nb : ℚ) : ℝ)) ≤ rb * (3 / 2 * ((pp nb : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (lg_one_add_le hp) (Nat.cast_nonneg rb)
    have h5 := p_rb hΔ h hr
    have h6 : lg m = Real.logb 2 m := rfl
    push_cast
    linarith

end Ineq

/-- «Setting and parameters»: the inequalities of the paragraph, each under the hypotheses listed at
its field of `ParamIneq`; the bounds r̄ ≤ 10n and M ≤ 14n under n ≥ 29·log(2Δ) + 19. -/
theorem paramIneq : ParamIneq where
  sb_lt n Δ m nb hΔ hm h := by
    have h1 := Ineq.m_div_lt hΔ hm h
    refine ⟨h1, ?_⟩
    rw [mul_div_assoc]
    linarith
  three_m n Δ m nb hΔ hm h := ⟨Ineq.three_m_lt hΔ hm h, Ineq.six_le hΔ⟩
  beta_le n Δ m nb hΔ hnm hm h := ⟨Ineq.beta_le₁ hΔ hnm hm h, Ineq.beta_le₂ (by omega) h⟩
  rb_le β rb h := Ineq.rb_le h
  large n Δ m nb rb hΔ hnm hm h hr hn := Ineq.large hΔ hnm hm h hr hn
  p_rb n Δ nb rb hΔ h hr := Ineq.p_rb hΔ h hr
  tb_le n Δ m nb rb tb hΔ hm h hr ht := Ineq.tb_le hΔ hm h hr ht

end VariableBound
