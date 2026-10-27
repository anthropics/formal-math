/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.ArithDefs
import ClauseBound.Alg.TopArith
import ClauseBound.ParityChecks.Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! # W ≤ A₁·K·e with a constant that depends on C₀ only

Notation as in proof/sparsification/UniformInK/Top/ArithDefs.lean: D = 2^β, b = β + 3, Y the number
of binary digits of K, W = b²·D·Y; y = log₂ K.
* `stMasterU`: if D⁶ ≤ K then W ≤ D³·2y ≤ e·2·D³·y^(C₀+1) ≤ e·(D⁶ + y^(2C₀+2)) ≤ A₁·K·e. The
  relative for a fixed width is `master` of proof/rates/ClauseBound/TopN/ArithR.lean, whose constant
  grows with k.
* `stSixU`: a number D ≤ (⌊log₂ n⌋ + 1)^c has D⁶ ≤ K if 2·(102·C₀·c)² ≤ ⌊log₂ n⌋ and n < K^(17·C₀). -/

public section

namespace UniformInK

open ClauseBound.Alg.TopArith

/-- W ≤ A₁·K·e if D⁶ ≤ K. -/
theorem stMasterU : StMasterU := by
  intro β K C₀ e hbD hK he h6
  have hY : (K.size : ℝ) ≤ 2 * Real.logb 2 K := size_le_two_logb K hK
  have hq := logb_pow_le K (2 * C₀ + 2) hK
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hA : (A1U C₀ : ℝ) = 1 + (((2 * C₀ + 2).factorial * 2 ^ (2 * C₀ + 2) : ℕ) : ℝ) := by
    unfold A1U; push_cast; ring
  rw [hA]
  generalize (((2 * C₀ + 2).factorial * 2 ^ (2 * C₀ + 2) : ℕ) : ℝ) = F at hq ⊢
  generalize Real.logb 2 K = y at he hy1 hY hq
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have hb : ((β + 3 : ℕ) : ℝ) ≤ ((2 ^ β : ℕ) : ℝ) := by exact_mod_cast hbD
  have h6r : ((2 ^ β : ℕ) : ℝ) ^ 6 ≤ (K : ℝ) := by exact_mod_cast h6
  have hW0 : ((WofU β K : ℕ) : ℝ) = ((β + 3 : ℕ) : ℝ) ^ 2 * ((2 ^ β : ℕ) : ℝ) * (K.size : ℝ) := by
    unfold WofU; push_cast; ring
  rw [hW0]
  have hb0 : (0 : ℝ) ≤ ((β + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ β : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) ≤ (K.size : ℝ) := Nat.cast_nonneg _
  generalize ((β + 3 : ℕ) : ℝ) = b at hb hb0 ⊢
  generalize ((2 ^ β : ℕ) : ℝ) = D at hb h6r hD0 ⊢
  generalize (K.size : ℝ) = Y at hY hY0 ⊢
  generalize (K : ℝ) = κ at h6r hq ⊢
  have hsq : 2 * D ^ 3 * y ^ (C₀ + 1) ≤ (D ^ 3) ^ 2 + (y ^ (C₀ + 1)) ^ 2 := by
    nlinarith [sq_nonneg (D ^ 3 - y ^ (C₀ + 1))]
  calc b ^ 2 * D * Y ≤ D ^ 2 * D * (2 * y) := by gcongr
    _ = 2 * D ^ 3 * y * 1 := by ring
    _ ≤ 2 * D ^ 3 * y * (e * y ^ C₀) := mul_le_mul_of_nonneg_left h1e (by positivity)
    _ = e * (2 * D ^ 3 * y ^ (C₀ + 1)) := by ring
    _ ≤ e * ((D ^ 3) ^ 2 + (y ^ (C₀ + 1)) ^ 2) := mul_le_mul_of_nonneg_left hsq he0.le
    _ = e * (D ^ 6 + y ^ (2 * C₀ + 2)) := by ring
    _ ≤ e * (κ + F * κ) := mul_le_mul_of_nonneg_left (add_le_add h6r hq) he0.le
    _ = (1 + F) * κ * e := by ring

/-- 2^(betaU k s) ≤ (⌊log₂ n⌋ + 1)^(a·k) for a = `aU C C₀`, if 2 ≤ K ≤ n, 1/(log₂ K)^C₀ ≤ e and 2^s
≤ (2/e)^C. -/
theorem stDLogU : StDLogU := by
  intro K n s C C₀ k e hK hKn he h2
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hy : Real.logb 2 K ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) :=
    logb_le_of_le_pow K (Nat.log 2 n + 1) (by omega) (hKn.trans (Nat.lt_pow_succ_log_self (by norm_num) n).le)
  have hL : 2 ≤ Nat.log 2 n + 1 := by
    have := Nat.log_pos (b := 2) (by norm_num) (hK.trans hKn)
    omega
  have hLr : (2 : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by exact_mod_cast hL
  have hfin : ((2 ^ betaU k s : ℕ) : ℝ) ≤ (((Nat.log 2 n + 1) ^ (aU C C₀ * k) : ℕ) : ℝ) := by
    rw [Nat.cast_pow (Nat.log 2 n + 1)]
    generalize ((Nat.log 2 n + 1 : ℕ) : ℝ) = L at hy hLr ⊢
    generalize Real.logb 2 K = y at he hy1 hy
    have hy0 : 0 < y := by linarith
    have hyC : 0 < y ^ C₀ := by positivity
    have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
    have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
    have h2e : 2 / e ≤ 2 * y ^ C₀ := by
      rw [div_le_iff₀ he0]
      nlinarith
    have hs : (2 : ℝ) ^ s ≤ (2 * y ^ C₀) ^ C := h2.trans (pow_le_pow_left₀ (by positivity) h2e C)
    have hs' : (2 : ℝ) ^ s ≤ (L * L ^ C₀) ^ C := hs.trans (by gcongr)
    have eβ : betaU k s = s * (8 * k) + 34 * k := by unfold betaU; ring
    calc ((2 ^ betaU k s : ℕ) : ℝ) = ((2 : ℝ) ^ s) ^ (8 * k) * 2 ^ (34 * k) := by
          rw [eβ]; push_cast; rw [pow_add, pow_mul]
      _ ≤ ((L * L ^ C₀) ^ C) ^ (8 * k) * L ^ (34 * k) := by gcongr
      _ = L ^ (aU C C₀ * k) := by unfold aU; ring
  exact_mod_cast hfin

/-- A number D ≤ (⌊log₂ n⌋ + 1)^c has D⁶ ≤ K, if 2·(102·C₀·c)² ≤ ⌊log₂ n⌋ and n < K^(17·C₀). -/
theorem stSixU : StSixU := by
  intro D c K n C₀ hc hn hlt hD hℓ
  have hC₀ : 1 ≤ C₀ := by
    rcases Nat.eq_zero_or_pos C₀ with h | h
    · subst h
      simp at hlt
      omega
    · exact h
  have hA : 1 ≤ 102 * C₀ * c := Nat.mul_pos (by omega) hc
  have hcl := ClauseBound.ParityChecks.Params.mul_clog_le (102 * C₀ * c) (Nat.log 2 n) hA hℓ
  have hpow : (D ^ 6) ^ (17 * C₀) < K ^ (17 * C₀) :=
    calc (D ^ 6) ^ (17 * C₀) = D ^ (102 * C₀) := by rw [← pow_mul]; congr 1; ring
      _ ≤ ((Nat.log 2 n + 1) ^ c) ^ (102 * C₀) := Nat.pow_le_pow_left hD _
      _ ≤ ((2 ^ Nat.clog 2 (Nat.log 2 n + 1)) ^ c) ^ (102 * C₀) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _) _
      _ = 2 ^ (102 * C₀ * c * Nat.clog 2 (Nat.log 2 n + 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) hcl
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
      _ < K ^ (17 * C₀) := hlt
  exact (lt_of_pow_lt_pow_left₀ _ (Nat.zero_le K) hpow).le

end UniformInK
