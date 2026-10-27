/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthVariableBoundStatement

/-! # The statement: one machine counts the satisfying assignments of a k-CNF, for all k, within 2^{O(k²·n·log log n/√(log n))} steps, and within the smaller of this and 2^{O(k·m/√(log m))}

Definitions only. Imports `FixedWidthVariableBoundStatement.lean` (and through it
`ClauseBoundStatement.lean`, `CountKSatStatement.lean`, `KSatStatement.lean`,
`ThreeSatStatement.lean`) and Mathlib.

## How to read it

* The machine M and the constant C come first; then the width k, the number n of variables and the
  formula φ. So there is ONE machine for all widths and sizes, and C does not depend on k.
* The input is `SatM.enc k φ` of `ClauseBoundStatement.lean`: 1ᵏ 0, then 1ⁿ 0, then k slots per
  clause. The width k is a declared width: at least the length of the longest clause.
* The output is the number of satisfying assignments among all 2ⁿ assignments of x₀ … xₙ₋₁, in n + 1
  bits, lowest bit first.
* The same machine with the same C satisfies three things.
  1. `CountsTMN`: on EVERY k-CNF on n ≥ 1 variables, with any number of clauses (none is allowed)
     and whether or not all variables occur, it halts within C·2^{C·k²·n·rn(n)} steps.
  2. `SatM.CountsTM`: on every k-CNF with m ≥ 1 clauses in which all variables occur, it halts
     within C·2^{C·k·m·rm(m)} steps. With rm = rPow (1/2), as in `TargetUniform`, this part alone is
     `SatM.TargetSqrt`.
  3. On every k-CNF on n ≥ 1 variables in which all variables occur, it halts within
     C·2^{C·min(k²·n·rn(n), k·m·rm(m))} steps. This follows from 1 and 2 and is written out so that
     the minimum can be seen.
* `TM2OutputsInTime … t` means: halts with that output after at most t steps.
* Why n ≥ 1 in 1 and 3: for n = 0 the bound would be C, while the machine has to pop its whole
  input, which begins with 1ᵏ 0, and that takes more than C steps once k is large. For n = 0 and m =
  1 (the formula with the empty clause only) part 2 applies.
* Why 2 and 3 ask that all variables occur: the input contains 1ⁿ, while a bound in m alone does not
  grow with n.
* No polynomial in the length of the input is added, because it would only change C. No clause is
  written twice, so there are at most (2n+1)ᵏ clauses, and the logarithm of the length of the input
  is at most a
  constant times k²·n·rn(n). When all variables occur, n ≤ k·m, so that logarithm is also at most a
  constant times k·m·rm(m). The same literals in another order count as another clause, as in
  `KSatStatement.lean`.

## What the statement does not say

* Nothing for k = 0, and for n = 0 only part 2.
* Nothing about inputs that are not codes of such formulas (at most k literals per clause, no clause
  written twice): a promise on the input.
* C is not explicit, and the bounds are asymptotic: the bound in n is below exhaustive counting (2ⁿ)
  only where C·k²·rn(n) < 1.
* The k in the bounds is the width written in the input, not the length of the longest clause.
* The input differs from that of `CountKSatStatement.lean` (there the width is fixed and not
  written), so the statements there are not literally special cases. -/

@[expose] public section

namespace SatM

open Turing
open Sat3 (CNF)

/-- `M`, started on the code of (k, φ), where k ≥ 1 and φ is a k-CNF on n ≥ 1 variables, halts
within `t k n` steps with the number of satisfying assignments, in n + 1 bits, as
output. One machine for all k and n; any number of clauses; variables need not occur. -/
def CountsTMN (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ → ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) (t k n))

/-- The time bound C·2^{C·k²·n·r(n)}, rounded down. The same C is the factor in front and the factor
in the exponent; it does not depend on k. -/
noncomputable def boundNK (r : ℕ → ℝ) (C k n : ℕ) : ℕ := ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * (k : ℝ) ^ 2 * n * r n)⌋₊

/-- The time bound C·2^{C·min(k²·n·rn(n), k·m·rm(m))}, rounded down. -/
noncomputable def boundBothK (rn rm : ℕ → ℝ) (C k n m : ℕ) : ℕ :=
  ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * min ((k : ℝ) ^ 2 * n * rn n) ((k : ℝ) * m * rm m))⌋₊

/-- One machine, finite alphabets, one constant C, for all k: the count within C·2^{C·k²·n·rn(n)}
steps on every k-CNF on n ≥ 1 variables; within C·2^{C·k·m·rm(m)} steps if all variables occur
and m ≥ 1; within C·2^{C·min(k²·n·rn(n), k·m·rm(m))} steps if all variables occur and n ≥ 1. -/
def CountUniformInRate (rn rm : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    CountsTMN M (boundNK rn C) ∧
    CountsTM M (bound rm C) ∧
    ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → AllOccur φ →
      Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
        (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) (boundBothK rn rm C k n φ.length))

/-- One machine and one constant for all k: 2^{O(k²·n·log log n/√(log n))}, 2^{O(k·m/√(log m))}, and
the minimum of the two exponents. -/
def TargetUniform : Prop := CountUniformInRate (SatK.rN 1 (1 / 2)) (rPow (1 / 2))

end SatM
