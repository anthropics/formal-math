/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.ConditionalTimes.Definitions

/-!
# Small facts for the deductions of Sections 5.1 and 5.2

* The claims give their bounds with a constant of unknown sign. `le_abs_mul_of_le_mul` replaces it
  by its absolute value at the moment the bound is used.
* `logU u = log (max u 2)` is nonnegative, and at most `log n` for `u ≤ n`.
* `countBound n d p` is the bound of Corollary 38. Its proof adds `productBound n D* p`, the bound
  of Corollary 26, and `buildBound n d p`, the time of Lemma 37.

In all files on the three conditional lemmas, `TimeModel`, `Claim` and `Closure` are those of the
namespace `ConditionalTimes`. That record is a parameter of the lemmas: it is given no reading, and
nothing connects it with the record for the deductions of Section 3 and Corollary 39, which is read
by programs.
-/

@[expose] public section

namespace ThreeSumApsp

namespace ConditionalTimes

/-- A bound `C g` with `g ≥ 0` and a constant of unknown sign is a bound `|C| g`. -/
theorem le_abs_mul_of_le_mul {x C g : ℝ} (h : x ≤ C * g) (hg : 0 ≤ g) : x ≤ |C| * g :=
  h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hg)

/-- `logU u ≥ 0`. -/
theorem logU_nonneg (u : ℝ) : 0 ≤ logU u :=
  Real.log_nonneg (le_max_of_le_right one_le_two)

/-- `logU u ≤ log n` for `u ≤ n` and `n ≥ 2`. -/
theorem logU_le_log {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : u ≤ n) : logU u ≤ Real.log n :=
  Real.log_le_log (lt_max_of_lt_right two_pos) (max_le hu (Nat.ofNat_le_cast.2 hn))

/-- The bound of Corollary 38: `|P| n^{0.0229} + n²/d^{0.126} + n^{2-1/440} log n`, with
`p = |P|`. -/
noncomputable abbrev countBound (n d p : ℕ) : ℝ :=
  (p : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (d : ℝ) ^ (0.126 : ℝ)
    + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n

/-- The bound of Corollary 38 is nonnegative. -/
theorem countBound_nonneg (n d p : ℕ) : 0 ≤ countBound n d p := by
  unfold countBound
  positivity

/-- The bound of Corollary 26 for `w` wanted entries: `w D^{0.437} + N²/D^{0.063}`. -/
noncomputable abbrev productBound (N D w : ℕ) : ℝ :=
  (w : ℝ) * (D : ℝ) ^ (0.437 : ℝ) + (N : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)

/-- The bound of Corollary 26 is nonnegative. -/
theorem productBound_nonneg (N D w : ℕ) : 0 ≤ productBound N D w := by
  unfold productBound
  positivity

open ComparisonCounts in
/-- The time of Lemma 37 in the proof of Corollary 38, with `s = blockLen n d` and the inner
dimension `D* = Dstar n d`: `n D* + (n d s + d s² + |P|) (log n + 1)`, with `p = |P|`. -/
noncomputable abbrev buildBound (n d p : ℕ) : ℝ :=
  (n : ℝ) * (Dstar n d : ℝ)
    + ((n : ℝ) * (d : ℝ) * (blockLen n d : ℝ) + (d : ℝ) * (blockLen n d : ℝ) ^ 2 + (p : ℝ)) *
      (Real.log n + 1)

/-- The time of Lemma 37 is nonnegative. -/
theorem buildBound_nonneg (n d p : ℕ) : 0 ≤ buildBound n d p := by
  unfold buildBound
  positivity

end ConditionalTimes

end ThreeSumApsp
