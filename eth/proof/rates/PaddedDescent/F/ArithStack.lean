/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.LenList
public import PaddedDescent.Threshold
public import SparsifyWidthK.Interfaces
import SparsifyWidthK.Thresholds

/-! # The stack of the walk fits under the pad (the last part of `StAW`)

The depth-first walk through the sparsification tree for clauses of width k keeps a stack of
formulas; `stackLen k τ n m` bounds the length of the word of its state (stack and flag) when
the formula at the root has at most m clauses. Here: for τ = `tauOf (sOf n)`,
`sOf n` ≥ `s0K k` and m = `inLen k n` this is at most 2^(n/2^(sOf n) + 1), hence below the length of
the pad (`stackLen_le`). The degree of `stackLen` in n grows with k; it is
paid for because k ≤ sOf n is far below Y = `Ytop (sOf n)`: whatever is at most n^e with e ≤ Y is
below the pad (`le_pad_of_le_pow`). -/

public section

namespace PaddedDescent.F.Arith

open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)

/-! ### Polynomials in n are below the pad -/

/-- 9·size n + 30 ≤ n/2^(sOf n) when sOf n ≥ 1. -/
theorem nine_size_le {n : ℕ} (hs : 1 ≤ sOf n) : 9 * Nat.size n + 30 ≤ n / 2 ^ sOf n := by
  refine overhead_sOf_le_div (a := 0) (c := 48) hs (by norm_num) (by norm_num) ?_
  have := size_le_sqrt n
  rw [pow_zero]
  omega

/-- Whatever is at most 2^30·(2^size n)^9, for instance 2^30·n^9, is below the pad. -/
theorem le_pad_of_le {n W C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F)
    (hW : W ≤ 2 ^ (9 * Nat.size n + 30)) : W ≤ F := by
  refine hW.trans (le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hF)
  have := nine_size_le hs
  nlinarith

/-- e·size n ≤ n/2^(sOf n) for every e ≤ Y = Ytop (sOf n), when sOf n ≥ 1. -/
theorem mul_size_le {n e : ℕ} (hs : 1 ≤ sOf n) (he : e ≤ Ytop (sOf n)) : e * Nat.size n ≤ n / 2 ^ sOf n := by
  refine overhead_sOf_le_div (a := 1) (c := 2) hs (by norm_num) (by norm_num) ?_
  have h := size_le_sqrt n
  calc e * Nat.size n ≤ Ytop (sOf n) * (2 * Nat.sqrt n + 2) := Nat.mul_le_mul he h
    _ = 2 * Ytop (sOf n) ^ 1 * (Nat.sqrt n + 1) := by ring

/-- Whatever is at most (2^size n)^e with e ≤ Y = Ytop (sOf n), for instance n^e, is below the pad. -/
theorem le_pad_of_le_pow {n e W C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F)
    (he : e ≤ Ytop (sOf n)) (hW : W ≤ 2 ^ (e * Nat.size n)) : W ≤ F := by
  refine hW.trans (le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hF)
  exact (mul_size_le hs he).trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hC))

/-- 4β + 10s + 1000 < Y. -/
theorem betaOf_lt_Ytop (s : ℕ) : 4 * betaOf s + 10 * s + 1000 < Ytop s :=
  lt_of_lt_of_le Nat.lt_two_pow_self ((two_pow_betaOf_le_Ktop s).trans (Ktop_le_Ytop s))

/-- 2^(4β + 10s + 1000) ≤ n for s = sOf n ≥ 1. -/
theorem two_pow_betaOf_le {n : ℕ} (hs : 1 ≤ sOf n) : 2 ^ (4 * betaOf (sOf n) + 10 * sOf n + 1000) ≤ n := by
  have h3 := Ytop_sOf_pow_le (p := 1) (by norm_num) hs
  rw [pow_one] at h3
  exact ((two_pow_betaOf_le_Ktop _).trans (Ktop_le_Ytop _)).trans h3

/-- k·(3n + 5) + 10 ≤ a³ if n < a, k < a and 4 ≤ a. -/
theorem clause_word_le {k n a : ℕ} (hn : n < a) (hk : k < a) (ha : 4 ≤ a) : k * (3 * n + 5) + 10 ≤ a ^ 3 := by
  have h1 : 3 * n + 5 ≤ a * a := by nlinarith
  have h2 : 10 ≤ a * a := by nlinarith
  calc k * (3 * n + 5) + 10 ≤ k * (a * a) + a * a := Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
    _ = (k + 1) * (a * a) := by ring
    _ ≤ a * (a * a) := Nat.mul_le_mul_right _ hk
    _ = a ^ 3 := by ring

/-- `inLen k n` ≤ a^(k+4) if n < a and 2^(k+1) ≤ a. -/
theorem inLen_le_pow {k n a : ℕ} (hn : n < a) (hk : 2 ^ (k + 1) ≤ a) : inLen k n ≤ a ^ (k + 4) := by
  have hk1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have hk2 : 2 ^ k ≤ a := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hk
  have h1 : k * 2 ^ k + 1 ≤ a ^ 2 := by
    calc k * 2 ^ k + 1 ≤ k * a + a := Nat.add_le_add (Nat.mul_le_mul_left _ hk2) (by omega)
      _ = (k + 1) * a := by ring
      _ ≤ a * a := Nat.mul_le_mul_right _ (by omega)
      _ = a ^ 2 := by ring
  have h2 : (n + 2) ^ (k + 1) ≤ a ^ (k + 2) := by
    calc (n + 2) ^ (k + 1) ≤ (2 * a) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (k + 1) * a ^ (k + 1) := mul_pow _ _ _
      _ ≤ a * a ^ (k + 1) := Nat.mul_le_mul_right _ hk
      _ = a ^ (k + 2) := by ring
  calc inLen k n = (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := rfl
    _ ≤ a ^ 2 * a ^ (k + 2) := Nat.mul_le_mul h1 h2
    _ = a ^ (k + 4) := by ring

/-- With a = 2^z, n < a, bsum τ k ≤ a, 2^(k+1) ≤ a and 16 ≤ a: `stackLen k τ n (inLen k n)` ≤
a^(k+12). -/
theorem stackLen_le_two_pow {k z n τ : ℕ} (hn : n < 2 ^ z) (hB : bsum τ k ≤ 2 ^ z) (hk : 2 ^ (k + 1) ≤ 2 ^ z) (h8 : 16 ≤ 2 ^ z) :
    stackLen k τ n (inLen k n) ≤ 2 ^ ((k + 12) * z) := by
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ z := ⟨_, rfl⟩
  rw [← ha] at hn hB hk h8
  have hk1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have hk2 : 2 ^ k ≤ a := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hk
  have h1 : bsum τ k * n + 1 ≤ a ^ 2 := by
    calc bsum τ k * n + 1 ≤ a * n + a := Nat.add_le_add (Nat.mul_le_mul_right _ hB) (by omega)
      _ = a * (n + 1) := by ring
      _ ≤ a * a := Nat.mul_le_mul_left _ hn
      _ = a ^ 2 := by ring
  have h2 := inLen_le_pow hn hk
  have h3 := clause_word_le hn (show k < a by omega) (show 4 ≤ a by omega)
  have hp8 : 1 ≤ a ^ (k + 8) := Nat.one_le_pow _ _ (by omega)
  have hp11 : 1 ≤ a ^ (k + 11) := Nat.one_le_pow _ _ (by omega)
  have h4 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 4 ≤ a ^ (k + 9) := by
    calc 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 4 ≤ a * a ^ (k + 4) * a ^ 3 + 4 :=
          Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul hk2 h2) h3) 4
      _ = a ^ (k + 8) + 4 := by ring
      _ ≤ 8 * a ^ (k + 8) := by omega
      _ ≤ a * a ^ (k + 8) := Nat.mul_le_mul_right _ (by omega)
      _ = a ^ (k + 9) := by ring
  unfold stackLen
  calc (bsum τ k * n + 1) * (2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 4) + 8 ≤ a ^ 2 * a ^ (k + 9) + 8 :=
        Nat.add_le_add_right (Nat.mul_le_mul h1 h4) 8
    _ = a ^ (k + 11) + 8 := by ring
    _ ≤ 9 * a ^ (k + 11) := by omega
    _ ≤ a * a ^ (k + 11) := Nat.mul_le_mul_right _ (by omega)
    _ = a ^ (k + 12) := by ring
    _ = 2 ^ ((k + 12) * z) := by rw [ha, ← pow_mul, mul_comm]

/-- The last part of `StAW`: the stack of the walk for width k fits under the pad. -/
theorem stackLen_le {k n C₀ F : ℕ} (hk : 1 ≤ k) (hs : s0K k ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) :
    stackLen k (tauOf (sOf n)) n (inLen k n) ≤ F := by
  have hks := le_of_s0K_le hs
  have hs1 : 1 ≤ sOf n := hk.trans hks
  have hn := Nat.lt_size_self n
  have hbig := two_pow_betaOf_le hs1
  have hY := betaOf_lt_Ytop (sOf n)
  refine le_pad_of_le_pow hs1 hC hF (e := k + 12) (by omega) (stackLen_le_two_pow hn ?_ ?_ ?_)
  · exact ((bsum_le_two_pow_betaOf hs).trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans (hbig.trans hn.le)
  · exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hbig.trans hn.le)
  · exact (show 16 ≤ 2 ^ 4 by norm_num).trans ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hbig.trans hn.le))

end PaddedDescent.F.Arith
