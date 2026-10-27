/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs
import SparsificationLemma.Cal.Beta
import SparsificationLemma.Cal.Facts
import SparsificationLemma.One
import Mathlib.Tactic.Linarith

/-! # The theorem on sparsification with Calabro's thresholds, parts (a), (b), (c)

This file proves `SparsABC` of proof/sparsification/SparsificationLemma/Cal/Defs.lean. It takes as
hypotheses four statements proved in other files: `StAlpha` and `StDegLe` (Cal/Alpha.lean), `StYLe`
(Cal/Real.lean), and `StNodup` (Side.lean: no output has a clause twice).
The procedure runs on φ without the clauses that contain a variable together with its negation; this
formula is a k-CNF with the same satisfying assignments (`stNoTaut`).
(a) By `factIIIy` there are at most 2^(yn) outputs, and y ≤ ε by `StYLe`, whose hypotheses on x and
    α are in `StAlpha`. (b) is `stExactlyOne`, which holds for all thresholds. (c) By `gen` a
    variable occurs in at
most 2·(θ₀ + … + θ_{k−1}) + 2 clauses of an output, where the θ_i are the thresholds `thetaC`; the
sum is at most 2 + 4α·(32α)^(k−2) by `stDegSum`, and this is at most (8k/ε)^(3k) by `StDegLe`. -/

public section

namespace SparsificationLemma.Cal

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat

/-- The sparsification statement `SparsABC`, parts (a), (b), (c) (the changed algorithm of Appendix
C with Calabro's thresholds; the bounds used in Step 5 of Appendix D), from `StNodup`, `StAlpha`,
`StYLe` and `StDegLe`. -/
theorem sparsABC (hN : StNodup) (hA : StAlpha) (hY : StYLe) (hDeg : StDegLe) : SparsABC := by
  intro k n ε φ hk h0 h1 hφ
  obtain ⟨a1, a2, -, a4, -⟩ := hA k ε hk h0 h1
  obtain ⟨t1, t2, -⟩ := stNoTaut φ
  have hα : 1 ≤ alphaC k ε := by omega
  have hψ := t2 k n hφ
  obtain ⟨-, -, g3, -⟩ := gen hα (by omega : 1 ≤ k) hψ
  have hε : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have hx : ((xC k ε : ℚ) : ℝ) = 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by rw [xC]; push_cast; ring
  refine ⟨fun Φ hΦ => ⟨(g3 Φ hΦ).1, hN _ _ _ _ Φ hΦ⟩, ?_, fun b => ?_, fun Φ hΦ v => ?_⟩
  · have hy : yC k (alphaC k ε) ≤ (ε : ℝ) := by
      refine hY k (alphaC k ε) (ε : ℝ) (by omega) hε ?_ ?_
      · rw [← hx]; exact_mod_cast a1
      · rw [← hx]; exact a4
    have h3 := factIIIy (alphaC k ε) k n (noTaut φ) hα (by omega) hψ
    rw [sparsify, outputs, List.length_map]
    exact h3.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg n)))
  · obtain ⟨e1, e2⟩ := stExactlyOne (thetaC (alphaC k ε)) k (depthC (alphaC k ε) k n) (noTaut φ) b
    exact ⟨fun h => e1 ((t1 b).2 h), fun h => e2 fun h' => h ((t1 b).1 h')⟩
  · have c1 := (g3 Φ hΦ).2 v
    have c2 := (stDegSum (alphaC k ε) k hα (by omega)).2.1
    have c3 := hDeg k ε hk h0 h1
    have c4 : occN Φ v ≤ 2 * (2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2)) + 2 := by omega
    have c5 : (occN Φ v : ℝ) ≤ 2 * ((2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) : ℕ) : ℝ) + 2 := by exact_mod_cast c4
    linarith

end SparsificationLemma.Cal
