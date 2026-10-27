/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SingleBitPieces.SecNetworks_LemGrouping
public import Paper.SecProof_Proof
import all StepMachines.Prog.Count

/-! # Section 6 of the paper, paragraph «Cost», with the constants of the paper (This folder uses, in Lemma 2, pieces made from single bits, with ρ = (log 12)/4, which the paper does not print.)

The paper takes e = δ'/12 and K ≥ 72/δ'. With these constants, `network_exponent_le` is the display
of the paragraph «Cost», and `network_exponent_le'` its bound ¾δ'm + δ'g. -/

public section

namespace SingleBitPieces

open Groundwork Groundwork.Prog Finset Paper

/-- **Section 6, «Cost».** «With e = δ'/12, K ≥ 72 and 1/K ≤ δ'/72, the exponent in Lemma 1 is eU +
e·gP/K + 2gP/K < ½δ'm + (1/144)δ'(m + g) + (1/6)δ'(m + g) = (97/144)δ'm + (25/144)δ'g.» Same as in
the paper, except that
the inequality is not strict, because U ≤ 6m here (the paper: U < 6m). K ≥ 72 follows from K ≥ 72/δ'
and δ' ≤ 1. -/
theorem network_exponent_le {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U ≤ 6 * m)
    (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K ≤ 97 / 144 * δ' * m + 25 / 144 * δ' * g := by
  have hK72 : (72 : ℝ) ≤ K := by
    have : (72 : ℝ) ≤ 72 / δ' := by rw [le_div_iff₀ hδ']; nlinarith
    linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hKδ : 72 ≤ δ' * K := by
    rw [div_le_iff₀ hδ'] at hK
    linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (g : ℝ) * P / K := ⟨_, rfl⟩
  have hqK : q * K = (g : ℝ) * P := by rw [hq]; field_simp
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hU' : (U : ℝ) ≤ 6 * m := by exact_mod_cast hU
  have hP' : (g : ℝ) * P ≤ 6 * ((m : ℝ) + g) := by exact_mod_cast hP
  have hmg : (0 : ℝ) ≤ (m : ℝ) + g := by positivity
  -- q ≤ (m + g)/12 and q ≤ δ'(m + g)/12
  have a1 : 72 * q ≤ 6 * ((m : ℝ) + g) := by nlinarith
  have a2 : 72 * q ≤ δ' * (6 * ((m : ℝ) + g)) := by
    calc 72 * q ≤ δ' * K * q := mul_le_mul_of_nonneg_right hKδ hq0
      _ = δ' * (q * K) := by ring
      _ ≤ δ' * (6 * ((m : ℝ) + g)) := by rw [hqK]; exact mul_le_mul_of_nonneg_left hP' hδ'.le
  have e1 : 2 * (g : ℝ) * P / K = 2 * q := by rw [hq]; ring
  rw [e1, ← hq]
  nlinarith

/-- «… ≤ ¾δ'm + δ'g.» -/
theorem network_exponent_le' {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U ≤ 6 * m)
    (hP : g * P ≤ 6 * (m + g)) : δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K ≤ 3 / 4 * δ' * m + δ' * g := by
  have h := network_exponent_le hδ' h1 hK hU hP
  have hm : (0 : ℝ) ≤ δ' * m := by positivity
  have hg : (0 : ℝ) ≤ δ' * g := by positivity
  nlinarith

end SingleBitPieces
