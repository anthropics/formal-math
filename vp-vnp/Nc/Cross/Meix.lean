/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Two families of polynomials

`mB y r n = [tⁿ] (1+t)^r/(1+yt)^(r+1)`, `mC y r n = [tⁿ] (1+yt)^r/(1+t)^(r+1)`.
That these are the coefficients, the relation between the two families and the orthogonality relation are
Paper.meixner_B, meixner_C, meixner_reciprocal and eq_orth (Paper/Identity.lean).
-/

namespace Nc.Cross

variable {R : Type*} [CommRing R]

/-- `[tⁿ] (1+t)^r/(1+yt)^(r+1)`. -/
def mB (y : R) : ℕ → ℕ → R
  | 0, n => (-y) ^ n
  | _ + 1, 0 => 1
  | r + 1, n + 1 => mB y r (n + 1) + mB y r n - y * mB y (r + 1) n
termination_by r n => (r, n)

/-- `[tⁿ] (1+yt)^r/(1+t)^(r+1)`. -/
def mC (y : R) : ℕ → ℕ → R
  | 0, n => (-1) ^ n
  | _ + 1, 0 => 1
  | r + 1, n + 1 => mC y r (n + 1) + y * mC y r n - mC y (r + 1) n
termination_by r n => (r, n)

theorem mB_zero (y : R) (n : ℕ) : mB y 0 n = (-y) ^ n := by rw [mB]

theorem mB_zero_right (y : R) (r : ℕ) : mB y r 0 = 1 := by
  cases r with
  | zero => rw [mB, pow_zero]
  | succ r => rw [mB]

theorem mB_succ (y : R) (r n : ℕ) :
    mB y (r + 1) (n + 1) = mB y r (n + 1) + mB y r n - y * mB y (r + 1) n := by rw [mB]

theorem mC_zero (y : R) (n : ℕ) : mC y 0 n = (-1) ^ n := by rw [mC]

theorem mC_zero_right (y : R) (r : ℕ) : mC y r 0 = 1 := by
  cases r with
  | zero => rw [mC, pow_zero]
  | succ r => rw [mC]

theorem mC_succ (y : R) (r n : ℕ) :
    mC y (r + 1) (n + 1) = mC y r (n + 1) + y * mC y r n - mC y (r + 1) n := by rw [mC]

theorem map_mB {S : Type*} [CommRing S] (f : R →+* S) (y : R) (r n : ℕ) :
    f (mB y r n) = mB (f y) r n := by
  induction r generalizing n with
  | zero => simp [mB_zero]
  | succ r ih =>
    induction n with
    | zero => simp [mB_zero_right]
    | succ n ih' => simp [mB_succ, ih, ih']

theorem map_mC {S : Type*} [CommRing S] (f : R →+* S) (y : R) (r n : ℕ) :
    f (mC y r n) = mC (f y) r n := by
  induction r generalizing n with
  | zero => simp [mC_zero]
  | succ r ih =>
    induction n with
    | zero => simp [mC_zero_right]
    | succ n ih' => simp [mC_succ, ih, ih']

end Nc.Cross
