/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmCount.Defs
import ThmCount.Rates
import SparsificationLemma.Cal.Alpha
import SparsificationLemma.Cal.Beta
import SparsificationLemma.Cal.Thr
import SparsificationLemma.One
import SparsificationLemma.StepSparsify
import SparsificationLemma.Sketch
import Mathlib.Tactic

/-! # The closing remark of Appendix C: «a bound in Calabro's proof gives M(ε) = O(ε^{-2} log²(1/ε))»

At k = 3: x = 128/ε, α = ⌈(8/ε)·⌈log₂ x⌉⌉ (proof/sparsification/SparsificationLemma/Cal/Defs.lean).
For 0 < ε ≤ 1/2 put λ = log₂(1/ε) ≥ 1.
* `alpha_le`: ⌈log₂ x⌉ ≤ 8 + λ ≤ 9λ, so α ≤ 72·λ/ε + 1 ≤ 73·λ/ε.
* `stMEps`: so 2 + 4α·(32α) = 2 + 128α² ≤ 682114·ε^{-2}·λ².
* `stMEpsClauses`: an output of the procedure has at most (2·(θ₀ + θ₁ + θ₂) + 2)·n clauses
  (`SparsificationLemma.Sketch.clauses_le`), where θ_j = `SparsificationLemma.Cal.thetaC` α j (j < 3)
  are the thresholds of the procedure, taken to be Calabro's; and θ₀ + θ₁ + θ₂ ≤ 2 + 4α·(32α)
  (`SparsificationLemma.Cal.stDegSum`). -/

public section

namespace ThmCount

open PaperSentences

/-- At k = 3 and for 0 < ε ≤ 1/2: α ≤ 73·log₂(1/ε)/ε. -/
theorem alpha_le {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : (SparsificationLemma.Cal.alphaC 3 ε : ℝ) ≤ 73 * (Real.logb 2 (1 / (ε : ℝ)) / (ε : ℝ)) := by
  have e0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have e1 : (ε : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  obtain ⟨lam, hlam⟩ : ∃ l, l = Real.logb 2 (1 / (ε : ℝ)) := ⟨_, rfl⟩
  rw [← hlam]
  have hl1 : 1 ≤ lam := by
    rw [hlam]
    refine one_le_logb ?_
    rw [le_div_iff₀ e0]
    linarith
  have hx : ((SparsificationLemma.Cal.xC 3 ε : ℚ) : ℝ) = 128 * (1 / (ε : ℝ)) := by
    unfold SparsificationLemma.Cal.xC
    push_cast
    ring
  have h128 : Real.logb 2 (128 : ℝ) = 7 := by
    rw [show (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  have hlog : Real.logb 2 ((SparsificationLemma.Cal.xC 3 ε : ℚ) : ℝ) = 7 + lam := by
    rw [hx, Real.logb_mul (by norm_num) (by positivity), ← hlam, h128]
  have hL : (SparsificationLemma.Cal.logC 3 ε : ℝ) ≤ 8 + lam := by
    have h := SparsificationLemma.Cal.stLogC 3 ε (by norm_num) h0 (by linarith)
    have h2 := Int.ceil_lt_add_one (Real.logb 2 ((SparsificationLemma.Cal.xC 3 ε : ℚ) : ℝ))
    rw [← h, hlog] at h2
    push_cast at h2
    linarith
  have hA : (SparsificationLemma.Cal.alphaC 3 ε : ℝ) ≤ 8 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) + 1 := by
    have hnn : (0 : ℚ) ≤ 2 * (((3 : ℕ) : ℚ) - 1) ^ 2 / ε * (SparsificationLemma.Cal.logC 3 ε : ℚ) := by positivity
    have h : ((SparsificationLemma.Cal.alphaC 3 ε : ℕ) : ℚ) < 2 * (((3 : ℕ) : ℚ) - 1) ^ 2 / ε * (SparsificationLemma.Cal.logC 3 ε : ℚ) + 1 := Nat.ceil_lt_add_one hnn
    have h' := (Rat.cast_le (K := ℝ)).2 h.le
    push_cast at h'
    have e : 2 * ((3 : ℝ) - 1) ^ 2 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) + 1 = 8 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) + 1 := by ring
    rw [e] at h'
    exact h'
  have h8 : (0 : ℝ) ≤ 8 / (ε : ℝ) := by positivity
  have hle : 1 ≤ lam / (ε : ℝ) := by
    rw [le_div_iff₀ e0]
    linarith
  have u1 : 8 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) ≤ 8 / (ε : ℝ) * (9 * lam) := mul_le_mul_of_nonneg_left (by linarith) h8
  have u2 : 8 / (ε : ℝ) * (9 * lam) + lam / (ε : ℝ) = 73 * (lam / (ε : ℝ)) := by ring
  linarith

/-- ε^{-2}·log₂(1/ε)² is the square of log₂(1/ε)/ε. -/
theorem sq_eq {e : ℝ} (e0 : 0 < e) (lam : ℝ) : e ^ (-2 : ℝ) * lam ^ 2 = (lam / e) ^ 2 := by
  rw [Real.rpow_neg e0.le, Real.rpow_two, div_pow]
  ring

/-- At k = 3 and for 0 < ε ≤ 1/2: 2 + 4α·(32α) ≤ 682114·ε^{-2}·log₂(1/ε)². -/
theorem deg_le {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    ((2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) : ℕ) : ℝ) ≤ 682114 * ((ε : ℝ) ^ (-2 : ℝ) * lg (1 / (ε : ℝ)) ^ 2) := by
  have e0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have e1 : (ε : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  have hα := alpha_le h0 h1
  have hl1 : 1 ≤ Real.logb 2 (1 / (ε : ℝ)) := by
    refine one_le_logb ?_
    rw [le_div_iff₀ e0]
    linarith
  unfold lg
  rw [sq_eq e0]
  obtain ⟨t, ht⟩ : ∃ t, t = Real.logb 2 (1 / (ε : ℝ)) / (ε : ℝ) := ⟨_, rfl⟩
  rw [← ht] at hα ⊢
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ e0]
    linarith
  have hα0 : (0 : ℝ) ≤ (SparsificationLemma.Cal.alphaC 3 ε : ℝ) := Nat.cast_nonneg _
  have hsq : (SparsificationLemma.Cal.alphaC 3 ε : ℝ) ^ 2 ≤ (73 * t) ^ 2 := pow_le_pow_left₀ hα0 hα 2
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
  push_cast
  nlinarith

/-- The bound on the occurrences of a literal in the formula at a leaf, at k = 3, is
O(ε^{-2}·log²(1/ε)) for 0 < ε ≤ 1/2: the statement `ThmCount.StMEps`, with the constant 682114. -/
theorem stMEps : StMEps := ⟨682114, fun _ h0 h1 => deg_le h0 h1⟩

/-- «gives M(ε) = O(ε^{-2} log²(1/ε))», at k = 3, for the outputs themselves: every output of the
procedure of Appendix C with the thresholds taken to be Calabro's has at most (A·ε^{-2}·log²(1/ε) + 2)·n
clauses, for 0 < ε ≤ 1/2. This is the statement `ThmCount.StMEpsClauses`, with A = 2·682114. -/
theorem stMEpsClauses : StMEpsClauses := by
  refine ⟨2 * 682114, fun ε h0 h1 n φ hφ Φ hΦ => ?_⟩
  have h1' : ε ≤ 1 := by linarith
  have hα := SparsificationLemma.StepSparsify.one_le_alpha (k := 3) le_rfl h0 h1'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hΦ
  have hc := (SparsificationLemma.Sketch.clauses_le (k := 3) (by norm_num) hα (SparsificationLemma.Cal.stThrCal (SparsificationLemma.Cal.alphaC 3 ε) 3 hα) le_rfl ((SparsificationLemma.stNoTaut φ).2.1 3 n hφ) x hx).2.2
  have hs := (SparsificationLemma.Cal.stDegSum (SparsificationLemma.Cal.alphaC 3 ε) 3 hα (by norm_num)).2.1
  have hs' : ∑ j ∈ Finset.range 3, SparsificationLemma.Cal.thetaC (SparsificationLemma.Cal.alphaC 3 ε) j ≤ 2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) := by
    simpa using hs
  have hd := deg_le h0 h1
  obtain ⟨Dg, hDg⟩ : ∃ Dg, Dg = 2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) := ⟨_, rfl⟩
  rw [← hDg] at hs' hd
  have h2 : (SparsificationLemma.out x).length ≤ (2 * Dg + 2) * n := hc.trans (Nat.mul_le_mul_right _ (by omega))
  have h3 : ((SparsificationLemma.out x).length : ℝ) ≤ (2 * (Dg : ℝ) + 2) * n := by exact_mod_cast h2
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
  linarith

end ThmCount
