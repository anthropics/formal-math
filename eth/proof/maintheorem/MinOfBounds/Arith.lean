/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MinOfBounds.Defs
import VariableBound.Paper.Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Corollary 11 from Theorem A (c) and Theorem D (b): the arithmetic

This file proves the sentence of the proof of Corollary 11 that reads: «This multiplies the number
of operations of the faster one by a constant; as km/√(log m) and n·log log n/√(log n) are at least
2, this constant goes into C.» No machine and no formula occurs in it.

Write A for 2^{C₁·km/√(log m)} and B for 2^{C₂·k²·n·log log n/√(log n)}, both rounded down, T for
the smaller of A and B, and P for C₁·L₁^C₁ + L + 1. The number to be bounded is q·(min(A + C₁·L₁^C₁,
B) + L + 1)^q.
1. It is at most q·(T + P)^q, and (T + P)^q ≤ 2^q·T^q + 2^q·P^q (`add_pow_le`).
2. `exponential_part_le`: T is at most 2^{D·X}, where D is the larger of C₁ and C₂ and X the smaller
   of the two exponents (`min_time_le`). As X ≥ 2, the factor q·2^q is at most 2^{q·X}. So q·2^q·T^q
   is at most 2^{(q·D + q)·X}.
3. `polynomial_part_le`: as L₁ ≤ a·L^a and L ≥ 1, q·2^q·P^q is at most a constant times a power of
   L.
4. `overheadGoesIntoC`: C is the sum of the three constants that come up.

`bound_le_timeM` is the arithmetic of `MinOfBounds.BoundInMSuffices`: C·2^{C·km/√(log₂(m+2))} ≤
2^{3C·km/√(log m)} for k ≥ 1 and m ≥ 2. -/

public section

namespace MinOfBounds

open MainTheoremForms VariableBound.Paper

/-- (T + P)^q ≤ 2^q·T^q + 2^q·P^q for all natural numbers: the sum is at most twice the larger of
the two. -/
theorem add_pow_le (T P q : ℕ) : (T + P) ^ q ≤ 2 ^ q * T ^ q + 2 ^ q * P ^ q := by
  rcases le_total T P with h | h
  · calc (T + P) ^ q ≤ (2 * P) ^ q := Nat.pow_le_pow_left (by omega) q
      _ = 2 ^ q * P ^ q := mul_pow _ _ _
      _ ≤ _ := Nat.le_add_left _ _
  · calc (T + P) ^ q ≤ (2 * T) ^ q := Nat.pow_le_pow_left (by omega) q
      _ = 2 ^ q * T ^ q := mul_pow _ _ _
      _ ≤ _ := Nat.le_add_right _ _

/-- The smaller of the times 2^{C₁·km/√(log m)} and 2^{C₂·k²·n·log log n/√(log n)} is at most
2^{D·X}, where D is the larger of C₁ and C₂ and X is the smaller of the two exponents km/√(log m)
and k²·n·log log n/√(log n); for k ≥ 1, m ≥ 2 and n ≥ 4. -/
theorem min_time_le (C₁ C₂ : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max C₁ C₂ : ℕ) : ℝ) * min (expM k m) (expN k n)) := by
  have hM := two_le_expM hk hm
  have hN := two_le_expN hk hn
  rcases le_total (expM k m) (expN k n) with h | h
  · rw [min_eq_left h]
    calc ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (timeM C₁ k m : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ (2 : ℝ) ^ ((C₁ : ℝ) * expM k m) := Nat.floor_le (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left _ _) (by linarith))
  · rw [min_eq_right h]
    calc ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (timeN C₂ k n : ℝ) := by exact_mod_cast min_le_right _ _
      _ ≤ (2 : ℝ) ^ ((C₂ : ℝ) * expN k n) := Nat.floor_le (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right _ _) (by linarith))

/-- On real numbers: if T ≤ 2^{D·X} and X ≥ 2, then q·(2^q·T^q) ≤ 2^{(q·D + q)·X}. Here X ≥ 2 is
used: q·2^q ≤ 2^{2q} ≤ 2^{q·X}. -/
theorem factor_goes_into_exponent (q D T : ℕ) {X : ℝ} (hX : 2 ≤ X) (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * X)) :
    (q : ℝ) * ((2 : ℝ) ^ q * (T : ℝ) ^ q) ≤ (2 : ℝ) ^ (((q : ℝ) * D + q) * X) := by
  have h1 : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast Nat.lt_two_pow_self.le
  have h2 : (q : ℝ) * (2 : ℝ) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * X) := by
    calc (q : ℝ) * (2 : ℝ) ^ q ≤ (2 : ℝ) ^ q * (2 : ℝ) ^ q := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 : ℝ) ^ ((q : ℝ) * 2) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, Real.rpow_two]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg q))
  have h3 : (T : ℝ) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * ((D : ℝ) * X)) := by
    calc (T : ℝ) ^ q ≤ ((2 : ℝ) ^ ((D : ℝ) * X)) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg T) hT q
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
  calc (q : ℝ) * ((2 : ℝ) ^ q * (T : ℝ) ^ q) = (q : ℝ) * (2 : ℝ) ^ q * (T : ℝ) ^ q := by ring
    _ ≤ (2 : ℝ) ^ ((q : ℝ) * X) * (2 : ℝ) ^ ((q : ℝ) * ((D : ℝ) * X)) := mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring

/-- The exponential part: q·2^q·T^q, where T is the smaller of the two times with the constants C₁
and C₂, is at most the time of Corollary 11 with the constant q·max(C₁, C₂) + q; for k ≥ 1, m ≥ 2
and n ≥ 4. -/
theorem exponential_part_le (C₁ C₂ q : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q) ≤ timeCor (q * max C₁ C₂ + q) k m n := by
  rw [timeCor_eq]
  unfold timeMin
  refine Nat.le_floor ?_
  have h := factor_goes_into_exponent q (max C₁ C₂) _ (le_min (two_le_expM hk hm) (two_le_expN hk hn)) (min_time_le C₁ C₂ hk hm hn)
  have e : ((q * max C₁ C₂ + q : ℕ) : ℝ) = (q : ℝ) * ((max C₁ C₂ : ℕ) : ℝ) + q := by rw [Nat.cast_add, Nat.cast_mul]
  rw [e, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  exact h

/-- The polynomial part: for L ≥ 1 and L₁ ≤ a·L^a, q·2^q·(C₁·L₁^C₁ + L + 1)^q is at most
q·2^q·(C₁·a^C₁ + 2)^q times L^((a·C₁ + 1)·q). -/
theorem polynomial_part_le (C₁ q a : ℕ) {L L₁ : ℕ} (hL : 1 ≤ L) (h : L₁ ≤ a * L ^ a) :
    q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) ≤ q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q * L ^ ((a * C₁ + 1) * q) := by
  have h1 : L₁ ^ C₁ ≤ a ^ C₁ * L ^ (a * C₁) := (Nat.pow_le_pow_left h C₁).trans_eq (by rw [mul_pow, ← pow_mul])
  have h2 : L ^ (a * C₁) ≤ L ^ (a * C₁ + 1) := Nat.pow_le_pow_right hL (Nat.le_succ _)
  have h3 : L ≤ L ^ (a * C₁ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) L
  have h4 : 1 ≤ L ^ (a * C₁ + 1) := Nat.one_le_pow _ _ hL
  have h5 : C₁ * L₁ ^ C₁ + L + 1 ≤ (C₁ * a ^ C₁ + 2) * L ^ (a * C₁ + 1) := by
    calc C₁ * L₁ ^ C₁ + L + 1 ≤ C₁ * (a ^ C₁ * L ^ (a * C₁ + 1)) + L ^ (a * C₁ + 1) + L ^ (a * C₁ + 1) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))) h3) h4
      _ = _ := by ring
  calc q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) ≤ q * (2 ^ q * ((C₁ * a ^ C₁ + 2) * L ^ (a * C₁ + 1)) ^ q) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 q))
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      ring

/-- The time of Corollary 11 grows with the constant; for k ≥ 1, m ≥ 2 and n ≥ 4. -/
theorem timeCor_mono {C C' : ℕ} (h : C ≤ C') {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : timeCor C k m n ≤ timeCor C' k m n := by
  rw [timeCor_eq, timeCor_eq]
  exact timeMin_mono h hk hm hn

/-- «… as km/√(log m) and n·log log n/√(log n) are at least 2, this constant goes into C.» The
constant is C = (q·max(C₁, C₂) + q) + q·2^q·(C₁·a^C₁ + 2)^q + (a·C₁ + 1)·q. -/
theorem overheadGoesIntoC : OverheadGoesIntoC := by
  intro C₁ C₂ q a
  refine ⟨q * max C₁ C₂ + q + q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q + (a * C₁ + 1) * q, fun k m n L L₁ hk hm hn hL hL₁ => ?_⟩
  have h0 : min (timeM C₁ k m + C₁ * L₁ ^ C₁) (timeN C₂ k n) + L + 1 ≤ min (timeM C₁ k m) (timeN C₂ k n) + (C₁ * L₁ ^ C₁ + L + 1) := by omega
  calc q * (min (timeM C₁ k m + C₁ * L₁ ^ C₁) (timeN C₂ k n) + L + 1) ^ q
      ≤ q * (min (timeM C₁ k m) (timeN C₂ k n) + (C₁ * L₁ ^ C₁ + L + 1)) ^ q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h0 q)
    _ ≤ q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q + 2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) := Nat.mul_le_mul_left _ (add_pow_le _ _ q)
    _ = q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q) + q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) := Nat.mul_add _ _ _
    _ ≤ timeCor (q * max C₁ C₂ + q) k m n + q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q * L ^ ((a * C₁ + 1) * q) :=
        Nat.add_le_add (exponential_part_le C₁ C₂ q hk hm hn) (polynomial_part_le C₁ q a hL hL₁)
    _ ≤ _ := Nat.add_le_add (timeCor_mono (by omega) hk hm hn) (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hL (by omega)))

/-- The bound of `AppRunningTime.BoundInM` with the constant C, C·2^{C·km/√(log₂(m+2))} rounded
down, is at most 2^{3C·km/√(log m)} rounded down; for k ≥ 1 and m ≥ 2. The factor C in front goes
into the exponent because km/√(log m) is at least 2. -/
theorem bound_le_timeM (C : ℕ) {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : SatM.bound (SatM.rPow (1 / 2)) C k m ≤ timeM (3 * C) k m := by
  unfold SatM.bound timeM
  refine Nat.floor_le_floor ?_
  have e : (C : ℝ) * k * m * SatM.rPow (1 / 2) m = (C : ℝ) * ((k : ℝ) * m * SatM.rPow (1 / 2) m) := by ring
  have h2 := two_le_expM hk hm
  rw [e]
  exact absorb C ((shiftM_le k hm).trans (by linarith)) (by linarith)

end MinOfBounds
