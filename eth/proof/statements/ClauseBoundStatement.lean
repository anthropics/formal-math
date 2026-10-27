/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The statements: ONE machine counts the satisfying assignments of a k-CNF with m clauses, for all k and m, within a bound in k·m

Definitions only (no theorem, no proof). Imports `CountKSatStatement.lean` (and through it
`KSatStatement.lean`, `ThreeSatStatement.lean`) and Mathlib.

## How to read it

Read first, in those files: formulas `Sat3.CNF n` (lists of clauses, a clause is a list of literals
on x₀ … xₙ₋₁), `SatK.IsKCNF k φ` (at most k literals per clause, no clause written twice), the code
`SatK.enc k φ` (1ⁿ 0, then k slots per clause), the count `SatK.numSat φ` (over all 2ⁿ assignments)
and its word `SatK.binary n N` (n + 1 bits, lowest first).
* In `CountInRate r` the machine M and the constant C are chosen before k, n, m and φ: ONE machine
  for all widths and all sizes, and the constant in the exponent does not depend on k.
* The width k is part of the input, in unary. It is a declared width: at least the length of the
  longest clause; every clause takes k slots even if it is shorter.
* The number m of clauses is `φ.length`. The time bound depends on k and m only.
* `AllOccur φ`: every one of the n variables occurs. So n ≤ k·m, and the satisfying assignments
  counted are those of the variables that occur.
* The shift m + 2 in `rPow` makes the bounds meaningful for every m ≥ 1; for m ≥ 2 it changes r(m)
  by a bounded factor, which C absorbs.
* A larger exponent α in `rPow α` is the stronger statement.

## What the statements do not say

* Nothing for k = 0 (the code does not determine the formula) and nothing for m = 0 (the bound would
  be C, but the machine has to read 1ᵏ 0).
* Nothing about inputs that are not codes of such formulas: the hypotheses are a promise on the
  input.
* C is not explicit, and the bounds are asymptotic: they are below exhaustive counting (2ⁿ with n ≤
  k·m) only where C·k·m·r(m) < n.
* Nothing in terms of n: a formula with many clauses per variable gains nothing here. Bounds in n
  need sparsification or another network at the top.
* The machine model is Mathlib's multi-stack machine `Turing.FinTM2`; one step runs a statement as
  far as its next `goto` or `halt`, as explained in `ThreeSatStatement.lean`.
* No «decides» form is stated; a machine that counts also decides. -/

@[expose] public section

namespace SatM

open Turing
open Sat3 (CNF)

/-- Every one of the variables x₀ … xₙ₋₁ occurs in some clause. Then the assignments of x₀ … xₙ₋₁
are the assignments of the variables that occur. -/
def AllOccur {n : ℕ} (φ : CNF n) : Prop := ∀ i : Fin n, ∃ C ∈ φ, ∃ l ∈ C, l.1 = i

/-- The input: 1ᵏ 0, then the code of φ as an instance of k-SAT (1ⁿ 0, then k slots per clause). The
number m of clauses is not written; it is the number of clause records. -/
def enc (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool := List.replicate k true ++ false :: SatK.enc k φ

/-- `M`, started on the code of (k, φ), where k ≥ 1, φ is a k-CNF with m ≥ 1 clauses and all its
variables occur, halts within `t k m` steps with the number of satisfying
assignments, in n + 1 bits, as output. One machine for all k, n and m. -/
def CountsTM (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ → ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → AllOccur φ →
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) (t k φ.length))

/-- The time bound C·2^{C·k·m·r(m)}, rounded down. The same C is the factor in front and the factor
in the exponent; it does not depend on k. -/
noncomputable def bound (r : ℕ → ℝ) (C k m : ℕ) : ℕ := ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * k * m * r m)⌋₊

/-- «#k-SAT with m clauses is in time 2^{O(k·m·r(m))}, the O not depending on k»: one machine,
finite alphabets, one constant C. -/
def CountInRate (r : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CountsTM M (bound r C)

/-- r(m) = 1/(log₂(m+2))^α. -/
noncomputable def rPow (α : ℝ) (m : ℕ) : ℝ := 1 / Real.logb 2 ((m : ℝ) + 2) ^ α

/-- 2^{O(km/√(log m))}. -/
def TargetSqrt : Prop := CountInRate (rPow (1 / 2))

end SatM
