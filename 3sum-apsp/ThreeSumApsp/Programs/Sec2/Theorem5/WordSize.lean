/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5
public import ThreeSumApsp.Sec2.Theorem5.WordSize

/-!
# Theorem 5 in the light language: the limits

Section 2.4.4, "Word size": all numbers that the algorithm forms have polynomially many values, so
they fit in a word; the same holds for the addresses.  This file has no program in it.  For L = 19m,
D = 4^m with m ≥ 1, N ≥ D^18 and w wanted positions with w · 2^m ≤ N² it shows:

* the input, the output and the work area together have at most N^4 cells (`cells_le_pow_four`);
* the powers b^{L+1} with b ≤ 10 are at most N³, and the square of the number of bands is at most
  N^4 (`pow_succ_le_cube`, `numBands_succ_sq_le`).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- The parameters of Theorem 5: L = 19m. -/
def thm5Par (m N : ℕ) : Par := ⟨19 * m, m, N⟩

section facts

variable {m N : ℕ}

/-- N ≥ 4^18. -/
theorem four_pow_eighteen_le (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) : 4 ^ 18 ≤ N :=
  (Nat.pow_le_pow_left (show 4 ≤ D m from by
    unfold D
    calc 4 = 4 ^ 1 := rfl
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm) 18).trans hN

/-- N ≥ 1. -/
theorem one_le_of_D_pow_le (hN : D m ^ 18 ≤ N) : 1 ≤ N :=
  (Nat.one_le_pow _ _ (Nat.pow_pos (by norm_num))).trans hN

/-- L + 2 ≤ N. -/
theorem levels_add_two_le (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) : 19 * m + 2 ≤ N := by
  have h1 : 19 * m + 1 < 2 ^ (19 * m + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (19 * m + 1) ≤ 2 ^ (36 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (36 * m) = D m ^ 18 := by
    unfold D
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]
    congr 1
    ring
  omega

/-- D ≤ N. -/
theorem D_le_of_D_pow_le (hN : D m ^ 18 ≤ N) : D m ≤ N :=
  (Nat.le_self_pow (by norm_num) _).trans hN

/-- 10^L ≤ N². -/
theorem ten_pow_levels_le_sq (hN : D m ^ 18 ≤ N) : 10 ^ (19 * m) ≤ N ^ 2 :=
  ten_pow_le_sq m N hN

/-- 7^L ≤ N². -/
theorem seven_pow_levels_le_sq (hN : D m ^ 18 ≤ N) : 7 ^ (19 * m) ≤ N ^ 2 :=
  (Nat.pow_le_pow_left (by norm_num) _).trans (ten_pow_levels_le_sq hN)

/-- K ≤ N. -/
theorem K_levels_le (hN : D m ^ 18 ≤ N) : K (19 * m) m ≤ N := K_le_of_D_pow_le m N hN

/-- K₀² ≤ N. -/
theorem K0_sq_levels_le (hN : D m ^ 18 ≤ N) : K0 (19 * m) m * K0 (19 * m) m ≤ N :=
  (Nat.sqrt_le _).trans (K_levels_le hN)

/-- D^{-1/18} ≤ 1. -/
theorem D_rpow_neg_le_one (m : ℕ) : (D m : ℝ) ^ (-(1 / 18 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.one_le_pow _ _ (by norm_num))
    (by norm_num)

/-- The encodings of all the row bands have at most 2 N² cells. -/
theorem numBands_mul_ten_pow_le (hN : D m ^ 18 ≤ N) : numBands (19 * m) m N * 10 ^ (19 * m) ≤ 2 * N
    ^ 2 := by
  have h := encodings_total_le m N hN
  have h2 : 4 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right (D_rpow_neg_le_one m)
      (show (0 : ℝ) ≤ 4 * (N : ℝ) ^ 2 by positivity)
    linarith
  have h3 : ((2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) ≤ ((4 * N ^ 2 : ℕ) : ℝ) := by
    push_cast at h ⊢
    linarith
  have h4 : 2 * numBands (19 * m) m N * 10 ^ (19 * m) ≤ 4 * N ^ 2 := by exact_mod_cast h3
  rw [Nat.mul_assoc] at h4
  omega

/-- There are at most 16 N² tiles. -/
theorem numBands_sq_le (hN : D m ^ 18 ≤ N) :
    numBands (19 * m) m N * numBands (19 * m) m N ≤ 16 * N ^ 2 := by
  have h := card_tiles_mul_N0_le (show m ≤ 19 * m by omega) N
  have hc : (tiles (19 * m) m N).card = numBands (19 * m) m N * numBands (19 * m) m N := by
    simp [tiles]
  have hp := padN_le_two_mul_of_D_pow_le m N hN
  have hp2 : padN (19 * m) m N ^ 2 ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left hp 2
  have h0 : (tiles (19 * m) m N).card ≤ (tiles (19 * m) m N).card * N0 (19 * m) m :=
    Nat.le_mul_of_pos_right _ (N0_pos _ _)
  rw [hc] at h0 h
  have e : (2 * N) ^ 2 = 4 * N ^ 2 := by ring
  omega

/-- There are at most 2N bands. -/
theorem numBands_le_two_mul (hN : D m ^ 18 ≤ N) : numBands (19 * m) m N ≤ 2 * N := by
  have hp := padN_le_two_mul_of_D_pow_le m N hN
  have hb : 0 < bandSize (19 * m) m := Nat.mul_pos (K0_pos (by omega)) (N0_pos _ _)
  exact (Nat.le_mul_of_pos_right _ hb).trans hp

/-- w ≤ N². -/
theorem le_sq_of_mul_two_pow_le {w : ℕ} (hw : w * 2 ^ m ≤ N ^ 2) : w ≤ N ^ 2 :=
  (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num))).trans hw

end facts

/-! ## The number of cells -/

/-- The work area, written out. -/
theorem cells5_eq (p : Par) (w : ℕ) :
    p.cells5 w = 32 + 4 * (p.L + 1) + (p.L + 2) + 140 + p.KK * p.L + 2 * p.N + p.N * p.Lo
      + p.D * p.m + 2 * (p.nB * p.T) + 2 * p.S7 + (6 * w + w * p.L + 2 * p.nT + 12)
      + p.L * (3 * w + 11) := by
  simp only [Par.cells5, Par.end5, Par.aSTK, Par.aSV, Par.aSC, Par.aSTART, Par.aCNT, Par.aPERM2,
    Par.aPERM, Par.aDGT, Par.aCODE, Par.aTID, Par.sharedEnd, Par.aZS, Par.aARR, Par.aENCB,
    Par.aENCA, Par.aDIG4, Par.aDIG3, Par.aBLOCK, Par.aBAND, Par.aMASK, Par.aPSI, Par.aPHI, Par.aPAS,
    Par.aP10, Par.aP7, Par.aP4, Par.aP3]
  ring

/-- The work area starts at the free pointer. -/
theorem end5_eq (p : Par) (fr w : ℕ) : p.end5 fr w = fr + p.cells5 w := by
  simp only [Par.cells5, Par.end5, Par.aSTK, Par.aSV, Par.aSC, Par.aSTART, Par.aCNT, Par.aPERM2,
    Par.aPERM, Par.aDGT, Par.aCODE, Par.aTID, Par.sharedEnd, Par.aZS, Par.aARR, Par.aENCB,
    Par.aENCA, Par.aDIG4, Par.aDIG3, Par.aBLOCK, Par.aBAND, Par.aMASK, Par.aPSI, Par.aPHI, Par.aPAS,
    Par.aP10, Par.aP7, Par.aP4, Par.aP3]
  ring

/-- **The space**: the input (3 + 2 N D + 2 w cells), the output (w cells) and the work area have at
most N^4 cells together. -/
theorem cells_le_pow_four {m N w : ℕ} (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) (hw : w * 2 ^ m ≤ N ^ 2) :
    3 + 2 * (N * D m) + 3 * w + (thm5Par m N).cells5 w ≤ N ^ 4 := by
  have h300 : 300 ≤ N := le_trans (by norm_num) (four_pow_eighteen_le hm hN)
  have hL := levels_add_two_le hm hN
  have hsq : 300 * N ≤ N * N := Nat.mul_le_mul_right N h300
  have hcube : 300 * (N * N) ≤ N * (N * N) := Nat.mul_le_mul_right (N * N) h300
  have hfourth : 300 * (N * (N * N)) ≤ N ^ 4 := by
    have e : N ^ 4 = N * (N * (N * N)) := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ h300
  have hsqN : N ^ 2 = N * N := sq N
  have hinput : N * D m ≤ N * N := Nat.mul_le_mul_left N (D_le_of_D_pow_le hN)
  have hmask : K0 (19 * m) m * K0 (19 * m) m * (19 * m) ≤ N * N :=
    Nat.mul_le_mul (K0_sq_levels_le hN) (by omega)
  have hdig3 : N * (19 * m - m) ≤ N * N := Nat.mul_le_mul_left N (by omega)
  have hdig4 : D m * m ≤ N * N := Nat.mul_le_mul (D_le_of_D_pow_le hN) (by omega)
  have henc := numBands_mul_ten_pow_le hN
  have harr := seven_pow_levels_le_sq hN
  have htiles := numBands_sq_le hN
  have hwanted := le_sq_of_mul_two_pow_le hw
  have hdigits : w * (19 * m) ≤ N * (N * N) := by
    calc w * (19 * m) ≤ N * N * N := Nat.mul_le_mul (by omega) (by omega)
      _ = N * (N * N) := by ring
  have hstack : 19 * m * (3 * w + 11) ≤ 3 * (N * (N * N)) + 11 * N := by
    calc 19 * m * (3 * w + 11) ≤ N * (3 * (N * N) + 11) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * (N * (N * N)) + 11 * N := by ring
  -- Each area has at most a few N³ cells, and 300 N³ ≤ N⁴.
  rw [cells5_eq]
  simp only [thm5Par, Par.KK, Par.K0, Par.Lo, Par.D, Par.nB, Par.T, Par.S7, Par.nT]
  omega

/-! ## The word -/

section word

variable {m N : ℕ}

/-- The powers of N increase. -/
theorem pow_le_pow_of_D_pow_le (hN : D m ^ 18 ≤ N) {a b : ℕ} (hab : a ≤ b) : N ^ a ≤ N ^ b :=
  Nat.pow_le_pow_right (one_le_of_D_pow_le hN) hab

/-- 10^{L+1} ≤ N³. -/
theorem ten_pow_succ_le_cube (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) : 10 ^ (19 * m + 1) ≤ N ^ 3 := by
  have h10 : 10 ≤ N := le_trans (by norm_num) (four_pow_eighteen_le hm hN)
  calc 10 ^ (19 * m + 1) = 10 ^ (19 * m) * 10 := pow_succ _ _
    _ ≤ N ^ 2 * N := Nat.mul_le_mul (ten_pow_levels_le_sq hN) h10
    _ = N ^ 3 := by ring

/-- b^{L+1} ≤ N³ for every base b ≤ 10. -/
theorem pow_succ_le_cube (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) {b : ℕ} (hb : b ≤ 10) :
    b ^ (19 * m + 1) ≤ N ^ 3 :=
  (Nat.pow_le_pow_left hb _).trans (ten_pow_succ_le_cube hm hN)

/-- (nB + 1)² ≤ N^4. -/
theorem numBands_succ_sq_le (hm : 1 ≤ m) (hN : D m ^ 18 ≤ N) :
    (numBands (19 * m) m N + 1) * (numBands (19 * m) m N + 1) ≤ N ^ 4 := by
  have h3 : 3 ≤ N := le_trans (by norm_num) (four_pow_eighteen_le hm hN)
  have h1 : numBands (19 * m) m N + 1 ≤ N * N := by
    have := numBands_le_two_mul hN
    have : 3 * N ≤ N * N := Nat.mul_le_mul_right N h3
    omega
  calc (numBands (19 * m) m N + 1) * (numBands (19 * m) m N + 1)
      ≤ N * N * (N * N) := Nat.mul_le_mul h1 h1
    _ = N ^ 4 := by ring

end word

end Light.Sec2
