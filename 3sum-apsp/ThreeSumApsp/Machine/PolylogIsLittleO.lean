/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Machine.Solving
public import ThreeSumApsp.Util.Asymptotics.LogExponent

/-!
# A bound with polylogarithmic factors is a bound n^{a+o(1)}

Used for Theorem 22, which prints its bounds for 3SUM as `n^{a+o(1)}`.  The exponent o(1) is
`logExponent e`, for which `n^a (log n)^e ≤ n^{a + logExponent e n}` (`rpow_mul_log_pow_le`).
-/

public section

namespace ThreeSumApsp.WordRam

open Filter

/-- A bound `O(n^a (log n)^{O(1)})` is a bound `n^{a+o(1)}`. -/
theorem SolvedInPolylogTime.solvedInLittleOTime {Q : EndStatement.Problem} {a : ℝ}
    (h : SolvedInPolylogTime Q a) : SolvedInLittleOTime Q a := by
  intro κ
  obtain ⟨e, P, b, C, hs⟩ := h κ
  refine ⟨P, b, 2 * max C 0, logExponent e, tendsto_logExponent e, ?_⟩
  refine solvesWithin_iff.2 ((solvesWithin_iff.1 hs).mono le_rfl (fun x hx => hx) fun x _ => ?_)
  have hlittle : (0 : ℝ) ≤ (x.n : ℝ) ^ (a + logExponent e x.n) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- at size 0 the first bound is at most 2 and the second at least 1
  have hle : (x.n : ℝ) ^ a * Real.log x.n ^ e + 1 ≤
      2 * ((x.n : ℝ) ^ (a + logExponent e x.n) + 1) := by
    rcases Nat.eq_zero_or_pos x.n with hn | hn
    · have hpow : ((x.n : ℕ) : ℝ) ^ a ≤ 1 := by
        rw [hn, Nat.cast_zero]
        exact Real.zero_rpow_le_one a
      have hlog : Real.log x.n ^ e ≤ 1 := by
        rw [hn, Nat.cast_zero, Real.log_zero]
        exact pow_le_one₀ le_rfl zero_le_one
      have hlog0 : 0 ≤ Real.log x.n ^ e := pow_nonneg (Real.log_natCast_nonneg _) _
      have := mul_le_mul hpow hlog hlog0 zero_le_one
      linarith
    · linarith [rpow_mul_log_pow_le a e hn]
  have hnonneg : (0 : ℝ) ≤ (x.n : ℝ) ^ a * Real.log x.n ^ e + 1 := by
    have := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x.n) a)
      (pow_nonneg (Real.log_natCast_nonneg x.n) e)
    linarith
  calc C * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1)
      ≤ max C 0 * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg
    _ ≤ max C 0 * (2 * ((x.n : ℝ) ^ (a + logExponent e x.n) + 1)) :=
        mul_le_mul_of_nonneg_left hle (le_max_right _ _)
    _ = 2 * max C 0 * ((x.n : ℝ) ^ (a + logExponent e x.n) + 1) := by ring

end ThreeSumApsp.WordRam
