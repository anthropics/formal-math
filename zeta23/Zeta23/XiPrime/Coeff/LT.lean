/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/LT.lean — elementary facts about the parameter L_T := ½ l(T) + iπ/4  (Defs.LT),
collected in a single home for use by Coeff.lean and Coeff/Reexpansion.lean.  Canonical names are unprimed.
-/
import Zeta23.XiPrime.Defs

noncomputable section

namespace Zeta23
namespace XiPrime

lemma re_LT (T : ℝ) : (LT T).re = l T / 2 := by simp [LT]

lemma im_LT (T : ℝ) : (LT T).im = Real.pi / 4 := by simp [LT]

lemma abs_im_LT_le (T : ℝ) : |(LT T).im| ≤ 1 := by
  rw [im_LT, abs_of_nonneg (by positivity)]
  linarith [Real.pi_le_four]

lemma norm_LT_ge (T : ℝ) : l T / 2 ≤ ‖LT T‖ := by
  calc l T / 2 ≤ |(LT T).re| := by rw [re_LT]; exact le_abs_self _
    _ ≤ ‖LT T‖ := Complex.abs_re_le_norm _

lemma LT_ne_zero {T : ℝ} (hl : 0 < l T) : LT T ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_LT, Complex.zero_re] at this
  linarith

lemma LT_add_ne_zero {T δ : ℝ} (hl : 0 < l T) (hδ : 0 ≤ δ) : LT T + (δ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.add_re, re_LT, Complex.ofReal_re, Complex.zero_re] at this
  linarith

end XiPrime
end Zeta23
