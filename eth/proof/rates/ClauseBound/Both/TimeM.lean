/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Both.Defs
import ClauseBound.Alg.End

/-! # The running time of the padding machine against the bound in m

`stTimeM : StTimeM`, from `StTopArith`: for the exponent `eM` of the algorithm for the bound in m
and every q there is a D with q·(|x| + 2^(eM x) + 1)^q ≤ D·2^(D·k·m·r(m)) on the code x of (k, φ).
This inequality
is proved here with the lemmas of proof/rates/ClauseBound/Alg/End.lean: |x| + 1 ≤ 8·(k·m)²; the
exponent is at most n ≤ k·m, which is used if m is below a
constant, and at most A·k·m·e_l otherwise; and log₂(k·m) = O(k·m·r(m)) because r(m) ≥
1/(c₁·(log₂(m+2))^c₁). -/

public section

namespace ClauseBound.Both.TimeM

open Groundwork PaddedDescent PaddedDescent.F CountKSat ClauseBound.Alg ClauseBound.Alg.End

/-- For the exponent of the algorithm for m, the running time of the padding machine is within the
bound in m. -/
theorem stTimeM (hA : StTopArith) : StTimeM := by
  intro Idx _ S e C₀ Q hS r c₁ hr he q
  set K₀ := S.K (Q.idx 0) with hK₀
  obtain ⟨A, hA⟩ := hA Idx S e C₀ Q
  -- c₁ ≥ 1, because e is positive
  have hc : 1 ≤ c₁ := by
    rcases Nat.eq_zero_or_pos c₁ with h0 | h0
    · exfalso
      have h1 := he (K₀ ^ 9) le_rfl
      have h2 := Q.e_ge (Q.pick (root9 (K₀ ^ 9))).1.length
      have h3 : (2 : ℝ) ≤ S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length) := by exact_mod_cast Q.K_two _
      have h4 : 0 < Real.logb 2 (S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length)) := Real.logb_pos (by norm_num) (by linarith)
      have h5 : 0 < 1 / Real.logb 2 (S.K (Q.idx (Q.pick (root9 (K₀ ^ 9))).1.length)) ^ C₀ := by positivity
      rw [h0] at h1
      simp only [Nat.cast_zero, zero_mul] at h1
      linarith
    · exact h0
  set H : ℕ := 2 * c₁ * (3 * (c₁ + 1).factorial * 2 ^ (c₁ + 1))
  set G : ℕ := A * c₁ + c₁ * (K₀ ^ 9 + 2) ^ c₁
  refine ⟨q * 9 ^ q + q * (2 * H + G), fun k n φ hk hm hφ ho => ?_⟩
  set m := φ.length with hmd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrm := hr m hm
  have hr0 : 0 ≤ r m := le_trans (by have := one_le_log m; positivity) hrm
  have hX : 0 ≤ (k : ℝ) * m * r m := by positivity
  have hn := n_le hφ ho
  obtain ⟨hEn, hEt⟩ := eM_enc_le hS Q.pick hk hφ.1
  -- the exponent
  have hE : (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ (G : ℝ) * ((k : ℝ) * m * r m) := by
    have hGa : ((A * c₁ : ℕ) : ℝ) * ((k : ℝ) * m * r m) ≤ (G : ℝ) * ((k : ℝ) * m * r m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) hX
    have hGb : ((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * ((k : ℝ) * m * r m) ≤ (G : ℝ) * ((k : ℝ) * m * r m) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) hX
    by_cases hs : m < K₀ ^ 9
    · refine le_trans ?_ hGb
      have h1 := one_le_mul_of_div_le hc (one_le_log m) hrm
      have h2 : Real.logb 2 ((m : ℝ) + 2) ≤ ((K₀ ^ 9 + 2 : ℕ) : ℝ) := by
        refine (log_le_self m).trans ?_
        have : m + 2 ≤ K₀ ^ 9 + 2 := by omega
        exact_mod_cast this
      have h3 : Real.logb 2 ((m : ℝ) + 2) ^ c₁ ≤ ((K₀ ^ 9 + 2 : ℕ) : ℝ) ^ c₁ := pow_le_pow_left₀ (by linarith [one_le_log m]) h2 _
      have h4 : 1 ≤ ((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * r m := by
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ hr0)
        rw [Nat.cast_mul, Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      calc (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ ((k * m : ℕ) : ℝ) := by exact_mod_cast hEn.trans hn
        _ = (k : ℝ) * m * 1 := by push_cast; ring
        _ ≤ (k : ℝ) * m * (((c₁ * (K₀ ^ 9 + 2) ^ c₁ : ℕ) : ℝ) * r m) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    · refine le_trans ?_ hGa
      have h1 := hA k m hk (not_lt.1 hs)
      have h2 := he m (not_lt.1 hs)
      calc (eM S Q.pick (SatM.enc k φ) : ℝ) ≤ (needTop S (Q.pick (root9 m)).2 k m : ℝ) := by exact_mod_cast hEt
        _ ≤ A * k * m * e (Q.pick (root9 m)).1.length := h1
        _ ≤ A * k * m * (c₁ * r m) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by push_cast; ring
  unfold SatM.bound
  refine Nat.le_floor ?_
  have ht := time_le q (SatM.enc k φ).length (eM S Q.pick (SatM.enc k φ)) (k * m) H G hX (Nat.mul_pos hk hm)
    (length_enc_succ_le hk hm hn) (mul_le_two_rpow hc hk hm hrm) hE
  refine ht.trans (le_of_eq ?_)
  congr 2
  ring

end ClauseBound.Both.TimeM
