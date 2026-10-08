/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.Strassen

/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/

public section

namespace Light.Sec3

/-- The scratch space, exactly. -/
theorem strScr_add (p j : ℕ) : strScr p j + p = 4 ^ j * p := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, pow_succ]
    have : 4 ^ j * 4 * p = 4 * (4 ^ j * p) := by ring
    omega

/-- The scratch space is at most the size of an operand. -/
theorem strScr_le (p j : ℕ) : strScr p j ≤ 4 ^ j * p := by
  have := strScr_add p j
  omega

/-- The scratch space grows with p. -/
theorem strScr_mono {p q : ℕ} (h : p ≤ q) (j : ℕ) : strScr p j ≤ strScr q j := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, strScr]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega

/-- The number of steps grows with p. -/
theorem strSteps_mono {p q : ℕ} (h : p ≤ q) (j : ℕ) : strSteps p j ≤ strSteps q j := by
  induction j with
  | zero =>
    rw [strSteps, strSteps]
    have h2 : p * p ≤ q * q := Nat.mul_le_mul h h
    have e1 : 32 * p * p = 32 * (p * p) := by ring
    have e2 : 32 * q * q = 32 * (q * q) := by ring
    omega
  | succ j ih =>
    rw [strSteps, strSteps]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega

end Light.Sec3
