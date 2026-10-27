/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBoundStatement

/-! # Counting the satisfying assignments of a k-CNF on n variables within 2^{O(n·r(n))}, for a fixed width k: the definitions

Definitions only. `SatK.CountsTM k M t` (in `CountKSatStatement.lean`): the machine M outputs the
count of every instance of k-SAT on n variables, in n + 1 bits, within t n steps; here all 2ⁿ
assignments are counted, and variables need not occur. The machine and the constant C may depend on
k.

## How to read it

* In `CountInRateN k r` the width k is fixed first; then come the machine M and the constant C; then
  n and the formula. The width is not part of the input.
* A smaller rate r is the stronger statement.
* The shift n + 4 in `rN` makes log₂ log₂ (n + 4) ≥ 1, so that `rN j α n` is positive for every n.

## What `CountInRateN` does not say

* Nothing uniform in k: M and C depend on k, and nothing is said about how.
* C is not explicit, and the bounds are asymptotic: they are below exhaustive counting (2ⁿ) only
  where C·r(n) < 1.
* Nothing about inputs that are not codes of instances of k-SAT (at most k literals per clause, no
  clause written twice): a promise on the input.
* The machine model is Mathlib's multi-stack machine `Turing.FinTM2`, as explained in
  `ThreeSatStatement.lean`. -/

@[expose] public section

namespace SatK

open Turing

/-- The time bound C·2^{C·n·r(n)}, rounded down. -/
noncomputable def boundN (r : ℕ → ℝ) (C n : ℕ) : ℕ := ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n * r n)⌋₊

/-- «#k-SAT on n variables is in time 2^{O(n·r(n))}»: one machine, finite alphabets, one constant C. -/
def CountInRateN (k : ℕ) (r : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CountsTM k M (boundN r C)

/-- r(n) = (log₂ log₂ (n+4))^j / (log₂ (n+4))^α. -/
noncomputable def rN (j : ℕ) (α : ℝ) (n : ℕ) : ℝ := Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) ^ j / Real.logb 2 ((n : ℝ) + 4) ^ α

end SatK
