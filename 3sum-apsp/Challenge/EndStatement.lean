/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import EndStatement

/-!
# The five claims of EndStatement.lean

`EndStatement.lean` defines a word RAM, says what it means that a problem is solved within a time
bound, and states five claims of the paper as propositions. It imports nothing, so it can be read
alone. This file states that the five propositions hold, and it imports nothing else.

**How the claims are to be read.** In all five, "is solved in time `O(n^r)`" has the meaning of
`EndStatement.Problem.SolvedInTime`: for every constant `κ` (the paper writes ν for the exponent of
the bound on the numbers) there are one deterministic program of the word RAM, a constant `b` and a
bound `T(n) = O(n^r)` such that, on every input of size `n` whose numbers have absolute value at
most `n^κ`, and at every word size of at least `b (⌊log₂ n⌋ + 1)` bits, the program halts within
`T(n)` steps with the right answer.

NOTE.  On the reading of `EndStatement.lean`; some of these points are also in its comments:
* The machine is generous on three points, none of which changes an exponent.  Every cell other
  than cell 0 and the cells of the input, with a positive or a negative name, holds 0 at the start,
  and no space is charged.  The finitely many cells that a program names in its text are arbitrary
  integers and need not be addressable by a word.  The constant `b` is chosen after `κ`.
* "O(log n)-bit words" is read as: the word size `b (⌊log₂ n⌋ + 1)` and every larger one, where
  ⌊log₂ 0⌋ is 0.
* The answer has to be right at every size `n`, 0 included; the bound `T(n) = O(n^r)` binds from
  `n = 2` on.
* `κ` ranges over the natural numbers, which covers every real constant ν ≥ 0, as n^ν ≤ n^⌈ν⌉.
  `κ = 0` is included, where Theorem 19 and Corollary 39 have ν ≥ 1.
* The bound `n^κ` is asked of every number of the input (the `n` in cell 0 is not one of them), also
  of the entries 0 and 1 of APSP's matrix of edges and of the blocks of the clique problem that do
  not count.
* How an instance is written into the cells is fixed in `EndStatement.lean` and not in the paper:
  `n` in cell 0, matrices row by row, APSP's matrix of edges and its two output cells for each pair,
  all `k²` blocks of the clique problem.
* In APSP an edge may be missing, and where there is no path the cell for the distance is free.
* Exact Triangle has a complete tripartite graph, as in Section 3.2.
* In 3SUM the three numbers stand at three different positions of the input.
* Theorem 22 prints two rounded exponents for each of its problems, one by the route through
  Theorem 5 and one by the route through Corollary 26.  The claims on these three problems have the
  exponents of the route through Corollary 26, which are the smaller ones: 1.9992 for 3SUM (the
  other is 1.99923), and 2.99942 for the (min,+)-product and for APSP (the other is 2.99949).  The
  larger exponents are stated in `Items.Theorem_22_first`.  Theorem 2 prints 2.9995 for the
  (min,+)-product and for APSP.
* The `ε_T` in the exponents of the claims on Exact Triangle and on `k`-Clique belongs to the route
  through Corollary 26 too: for this route Theorem 19 prints "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})".
* Corollary 39 speaks also of a `k`-clique of minimum, or of maximum, total edge weight; this is
  stated in `Items.Corollary_39_min_max`.
-/

namespace ThreeSumApsp

/-- Theorem 19: Exact Triangle on three `n × n` matrices of integers of absolute value at
most `n^κ` is solved in time `O(n^(3 - 0.0017))`. -/
theorem endStatement_theorem_19 : EndStatement.Theorem_19 := by
  sorry

/-- Theorem 22: 3SUM (do three of the numbers, at three different positions, sum to 0?) on
`n` integers of absolute value at most `n^κ` is solved in time `O(n^1.9992)`. -/
theorem endStatement_theorem_22_3SUM : EndStatement.Theorem_22_3SUM := by
  sorry

/-- Theorem 22: the (min,+)-product of two `n × n` matrices of integers of absolute value
at most `n^κ` is computed in time `O(n^2.99942)`. -/
theorem endStatement_theorem_22_MinPlus : EndStatement.Theorem_22_MinPlus := by
  sorry

/-- Theorem 22: APSP on directed graphs with `n` vertices, integer weights of absolute
value at most `n^κ` and no negative cycle is solved in time `O(n^2.99942)`. -/
theorem endStatement_theorem_22_APSP : EndStatement.Theorem_22_APSP := by
  sorry

/-- Corollary 39: for every `k ≥ 3`, Zero-Weight `k`-Clique on `k` parts of `n` vertices,
with integer weights of absolute value at most `n^κ`, is decided in time `O(n^(k - 0.0017 ⌊k/3⌋))`.
-/
theorem endStatement_corollary_39_zeroWeight : EndStatement.Corollary_39_ZeroWeight := by
  sorry

end ThreeSumApsp
