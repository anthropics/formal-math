/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.RunningTimes.Sec3.Theorem22
public import ThreeSumApsp.RunningTimes.Sec5.Corollary39
public import ThreeSumApsp.Statements.Exponents

/-!
# The five claims of the end statement

The item statements for Theorems 19 and 22 and Corollary 39 speak of the problems of the end
statement and contain the five bounds, with real exponents.  `SolvedInTime.endStatement` turns such
a bound into the form of the end statement, with the same program: a step bound with natural values,
and a rational exponent.

Which bound each claim takes, and on which of the paper's two routes it rests:

* Theorem 19: the third bound of `Items.Theorem_19`.  It follows from the second bound, so it rests
  on Theorem 17 with Corollary 16, that is, on Corollary 26 (Section 4), and not on the time bound
  of Theorem 5.
* 3SUM, the (min,+)-product and APSP: the first and the last two bounds of
  `Items.Theorem_22_second`, "using Corollary 26".
* Zero-Weight k-Clique: `Items.Corollary_39_zero`, from Theorem 19 using Corollary 26.
-/

public section

namespace ThreeSumApsp

open WordRam

/-- Theorem 19: Exact Triangle on three `n × n` matrices of integers of absolute value at
most `n^κ` is solved in time `O(n^(3 - 0.0017))`. -/
theorem endStatement_theorem_19 : EndStatement.Theorem_19 :=
  wordRam_theorem_19.rounded.endStatement (by norm_num [EndStatement.ε_T])
    (by norm_num [EndStatement.ε_T])

/-- Theorem 22: 3SUM (do three of the numbers, at three different positions, sum to 0?) on
`n` integers of absolute value at most `n^κ` is solved in time `O(n^1.9992)`. -/
theorem endStatement_theorem_22_3SUM : EndStatement.Theorem_22_3SUM :=
  wordRam_theorem_22_second.threeSum.endStatement (by norm_num) (by norm_num)

/-- Theorem 22: the (min,+)-product of two `n × n` matrices of integers of absolute value
at most `n^κ` is computed in time `O(n^2.99942)`. -/
theorem endStatement_theorem_22_MinPlus : EndStatement.Theorem_22_MinPlus :=
  wordRam_theorem_22_second.minPlus.endStatement (by norm_num) (by norm_num)

/-- Theorem 22: APSP on directed graphs with `n` vertices, integer weights of absolute
value at most `n^κ` and no negative cycle is solved in time `O(n^2.99942)`. -/
theorem endStatement_theorem_22_APSP : EndStatement.Theorem_22_APSP :=
  wordRam_theorem_22_second.apsp.endStatement (by norm_num) (by norm_num)

/-- Corollary 39: for every `k ≥ 3`, Zero-Weight `k`-Clique on `k` parts of `n` vertices,
with integer weights of absolute value at most `n^κ`, is decided in time `O(n^(k - 0.0017 ⌊k/3⌋))`.
-/
theorem endStatement_corollary_39_zeroWeight : EndStatement.Corollary_39_ZeroWeight := by
  intro k hk
  have hdiv : ((k / 3 : ℕ) : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.div_le_self k 3
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := by positivity
  refine (wordRam_corollary_39_zero k hk).endStatement (by norm_num [EndStatement.ε_T]) ?_
  norm_num [EndStatement.ε_T]
  linarith

end ThreeSumApsp
