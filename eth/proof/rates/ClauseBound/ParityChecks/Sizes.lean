/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs

/-! # The sizes of the networks of marks for the parity checks

Inequalities between natural numbers, with explicit numerals, for the bounds U and P of the networks
of marks on 7n variables (`UbOL_le`, `g_mul_PbOL_le`, `one_le_PbOL`) and for the numbers that go
into them
(`bitOL_le`, `colMax_le`, `rowMax_le`, `occOL_le`). L = ⌈log₂(2Δ)⌉ throughout. The auxiliary
statements are in the
namespace `ClauseBound.ParityChecks.Sizes`. -/

public section

namespace ClauseBound.ParityChecks

open PaddedDescent.F PaddedDescent.F.Mark

namespace Sizes

/-- 2Δ ≤ 2^L. -/
theorem two_mul_le (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _

/-- n ≤ 2^⌈log₂ n⌉. -/
theorem le_two_pow_clog (n : ℕ) : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) _

/-- g·⌈N/g⌉ ≤ N + g − 1. -/
theorem mul_qv_le (g N : ℕ) : g * qv g N ≤ N + g - 1 := Nat.mul_div_le _ _

end Sizes

open Sizes

variable {n Δ : ℕ}

theorem two_le_LD (hΔ : 2 ≤ Δ) : 2 ≤ LD Δ := by
  have h : Nat.clog 2 (2 ^ 2) ≤ Nat.clog 2 (2 * Δ) := Nat.clog_mono_right 2 (by omega)
  rwa [Nat.clog_pow 2 2 (by norm_num)] at h

theorem bitOL_le (hΔ : 2 ≤ Δ) : bitOL Δ ≤ 2 * LD Δ + 4 := by
  have _ := hΔ
  unfold bitOL blkOL
  refine Nat.clog_le_of_le_pow ?_
  have h1 := two_mul_le Δ
  generalize LD Δ = L at h1 ⊢
  have h2 : L < 2 ^ L := Nat.lt_two_pow_self
  have h3 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  calc 2 * Δ + 16 * Δ * L + 1 = 2 * Δ * (1 + 8 * L) + 1 := by ring
    _ ≤ 2 ^ L * (1 + 8 * L) + 2 ^ L * 1 := Nat.add_le_add (Nat.mul_le_mul_right _ h1) (by omega)
    _ = 2 ^ L * (8 * L + 2) := by ring
    _ ≤ 2 ^ L * (8 * 2 ^ L) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (2 * L + 3) := by ring
    _ ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem UbOL_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) (k K : ℕ) : UbOL k K n Δ ≤ 354 * k * n * LD Δ + 6 * (3 * K ^ 8) ^ 2 := by
  unfold UbOL Ub
  have hb := bitOL_le hΔ
  have hL := two_le_LD hΔ
  generalize bitOL Δ = b at hb ⊢
  generalize LD Δ = L at hb hL ⊢
  generalize 3 * K ^ 8 = g
  rw [Nat.add_sub_cancel]
  have h1 : 11 * n * (1 + b) ≤ 11 * n * (2 * L + 5) := Nat.mul_le_mul_left _ (by omega)
  have h2 : n * 2 ≤ n * L := Nat.mul_le_mul_left _ hL
  have h3 : 11 * n * (1 + b) + (7 * n + 1) ≤ 59 * (n * L) := by
    have e : 11 * n * (2 * L + 5) = 22 * (n * L) + 55 * n := by ring
    omega
  calc 2 * 3 * (k * (11 * n) * (1 + b) + k * (7 * n + 1) + g ^ 2) = 6 * (k * (11 * n * (1 + b) + (7 * n + 1))) + 6 * g ^ 2 := by ring
    _ ≤ 6 * (k * (59 * (n * L))) + 6 * g ^ 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)) _
    _ = 354 * k * n * L + 6 * g ^ 2 := by ring

theorem colMax_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : colMax n Δ ≤ 19 * LD Δ + Nat.clog 2 n + 6 := by
  have _ := hn
  have _ := hΔ
  unfold colMax
  have h1 : Nat.clog 2 (16 * Δ * n) ≤ 4 + LD Δ + Nat.clog 2 n := by
    refine Nat.clog_le_of_le_pow ?_
    have h2 : Δ ≤ 2 ^ LD Δ := by have := two_mul_le Δ; omega
    calc 16 * Δ * n ≤ 16 * 2 ^ LD Δ * 2 ^ Nat.clog 2 n := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (le_two_pow_clog n)
      _ = 2 ^ (4 + LD Δ + Nat.clog 2 n) := by ring
  omega

theorem rowMax_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : rowMax n Δ ≤ 3 * Δ * LD Δ + Nat.clog 2 n + 9 := by
  have _ := hn
  have _ := hΔ
  unfold rowMax
  have h1 : Nat.clog 2 (96 * n) ≤ 7 + Nat.clog 2 n := by
    refine Nat.clog_le_of_le_pow ?_
    calc 96 * n ≤ 128 * 2 ^ Nat.clog 2 n := Nat.mul_le_mul (by norm_num) (le_two_pow_clog n)
      _ = 2 ^ (7 + Nat.clog 2 n) := by ring
  omega

theorem occOL_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : occOL n Δ + 4 ≤ 19 * Δ * (LD Δ + Nat.clog 2 n + 1) := by
  unfold occOL
  have hc := colMax_le hn hΔ
  have hr := rowMax_le hn hΔ
  generalize colMax n Δ = cm at hc ⊢
  generalize rowMax n Δ = rm at hr ⊢
  generalize LD Δ = L at hc hr ⊢
  generalize Nat.clog 2 n = c at hc hr ⊢
  have e : 19 * Δ * (L + c + 1) = 19 * (Δ * L) + 19 * (Δ * c) + 19 * Δ := by ring
  have h1 : Δ * (2 + cm) ≤ Δ * (19 * L + c + 8) := Nat.mul_le_mul_left _ (by omega)
  have e1 : Δ * (19 * L + c + 8) = 19 * (Δ * L) + Δ * c + 8 * Δ := by ring
  have e2 : 3 * Δ * L = 3 * (Δ * L) := by ring
  have h2 : c ≤ Δ * c := Nat.le_mul_of_pos_left _ (by omega)
  rw [e]
  rcases le_total (Δ * (2 + cm)) rm with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

theorem g_mul_PbOL_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) (K : ℕ) : 3 * K ^ 8 * PbOL K n Δ ≤ 1330 * (n + K ^ 8) * Δ * LD Δ * (LD Δ + Nat.clog 2 n + 1) := by
  unfold PbOL Pb
  have hb := bitOL_le hΔ
  have hL := two_le_LD hΔ
  have ho := occOL_le hn hΔ
  have hq := mul_qv_le (3 * K ^ 8) (7 * n)
  have h1 : 2 * (2 + bitOL Δ) ≤ 10 * LD Δ := by omega
  have h2 : 3 * K ^ 8 * qv (3 * K ^ 8) (7 * n) ≤ 7 * (n + K ^ 8) := by omega
  calc 3 * K ^ 8 * (2 * (2 + bitOL Δ) * qv (3 * K ^ 8) (7 * n) * (occOL n Δ + 4))
      = 2 * (2 + bitOL Δ) * (3 * K ^ 8 * qv (3 * K ^ 8) (7 * n)) * (occOL n Δ + 4) := by ring
    _ ≤ 10 * LD Δ * (7 * (n + K ^ 8)) * (19 * Δ * (LD Δ + Nat.clog 2 n + 1)) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) ho
    _ = 1330 * (n + K ^ 8) * Δ * LD Δ * (LD Δ + Nat.clog 2 n + 1) := by ring

theorem one_le_PbOL (hn : 1 ≤ n) {K : ℕ} (hK : 1 ≤ K) : 1 ≤ PbOL K n Δ := by
  unfold PbOL Pb
  have hg : 0 < 3 * K ^ 8 := by positivity
  have h1 : 1 ≤ qv (3 * K ^ 8) (7 * n) := by
    unfold qv
    exact (Nat.one_le_div_iff hg).2 (by omega)
  have h2 : 1 ≤ 2 * (2 + bitOL Δ) := by omega
  have h3 : 1 ≤ occOL n Δ + 4 := by omega
  exact Nat.mul_pos (Nat.mul_pos h2 h1) h3

end ClauseBound.ParityChecks
