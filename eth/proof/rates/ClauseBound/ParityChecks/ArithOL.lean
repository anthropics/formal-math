/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
import ClauseBound.ParityChecks.Sizes
import ClauseBound.ParityChecks.ArithAux
import all ClauseBound.TopN.Arith
import all ClauseBound.TopN.ArithR
import ClauseBound.TopN.Budget
import ClauseBound.Alg.TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The exponent of the pad is O_k(e·n·(s+1))

`stArithO : StArithO`. The plan is that of proof/rates/ClauseBound/TopN/Arith.lean and ArithR.lean,
whose lemmas are used. Notation: K = K_l the number of nodes at the level picked for n, so that
K^17 ≤ n < K^(17·C₀); Y the number of binary digits of K; s the precision, β = `betaN k s`, b = β +
3, D = 2^β = Δ; W = b²·D·Y (`Wof`), which is at most A₁·K·e_l (`master`).
* The bound on the shared bits of a network is 354·k·n·(β+1) + 54·K^16: it is LINEAR in β. This
  gives the main term e_l·354·k·n·(β+1) = O_k(e_l·n·(s+1)).
* Every other part X of the exponent, except the term n/2^s (which is at most n·e, since 1/2^s ≤ e),
  satisfies K·X ≤ c·W·n in natural numbers (`lowerO`), so that X ≤ c·A₁·e_l·n.
* Of the five tests of the plan, the fourth (Δ ≤ (⌊log₂ n⌋ + 1)^c) never fails for c = `cO`
  (`D_le_log`). If another one fails, the exponent is n, and n ≤ A·n·e_l: if s < s0K k then e_l ≥
  2^(−s0K k);
  if 2^β > n + 1 or 2·(β+1) > n then n ≤ W ≤ A₁·K·e_l ≤ A₁·n·e_l; if n < n₀ then 1/e_l ≤ (log₂ K)^C₀
  ≤ n₀^C₀. -/

namespace ClauseBound.ParityChecks.ArithOL

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith

/-! ### Natural numbers -/

section nat

variable {k K n s C₀ : ℕ}

/-- 2 ≤ 2^β. -/
theorem two_le_D (k s : ℕ) : 2 ≤ 2 ^ betaN k s := by
  have := b_le_D k s
  omega

/-- The constant in g·P ≤ G·W·n. -/
def GO (C₀ : ℕ) : ℕ := 2660 * (1 + 17 * C₀)

/-- Ub ≤ 354·k·n·(β+1) + 54·K^16. -/
theorem UbO_le (hn : 1 ≤ n) : UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := by
  have h := UbOL_le hn (two_le_D k s) k K
  rw [LD_two_pow] at h
  calc UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 6 * (3 * K ^ 8) ^ 2 := h
    _ = 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := by ring

/-- g·P ≤ 1330·(2n)·D·(β+1)·(β + 2 + size n). -/
theorem gPO_le (hn : 1 ≤ n) (hK8 : K ^ 8 ≤ n) :
    3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ 1330 * (2 * n) * 2 ^ betaN k s * (betaN k s + 1) * (betaN k s + 2 + n.size) := by
  have h := g_mul_PbOL_le hn (two_le_D k s) K
  rw [LD_two_pow] at h
  refine h.trans ?_
  have h1 := clog_le_size n
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))) (by omega)

/-- g·P ≤ G·W·n. -/
theorem gPO_le_W (hK : 1 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ GO C₀ * (Wof k K s * n) := by
  have hKn : K ≤ n := by simpa using pow_le_n hK hn17 (j := 1) (by norm_num)
  have h := gPO_le (k := k) (s := s) (hK.trans hKn) (pow_le_n hK hn17 (by norm_num))
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK
  refine h.trans ?_
  unfold Wof GO
  generalize K.size = Y at hz hY
  generalize n.size = z at hz
  generalize 2 ^ betaN k s = D
  obtain ⟨b, hb⟩ : ∃ b, b = betaN k s + 3 := ⟨_, rfl⟩
  rw [← hb]
  have h1 : betaN k s + 1 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have h2 : betaN k s + 2 + z ≤ (1 + 17 * C₀) * (b * Y) := by
    have a1 : b ≤ b * Y := Nat.le_mul_of_pos_right _ hY
    have a2 : 17 * C₀ * Y ≤ 17 * C₀ * (b * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hb1)
    calc betaN k s + 2 + z ≤ b * Y + 17 * C₀ * (b * Y) := Nat.add_le_add ((by omega : betaN k s + 2 ≤ b).trans a1) (hz.trans a2)
      _ = (1 + 17 * C₀) * (b * Y) := by ring
  calc 1330 * (2 * n) * D * (betaN k s + 1) * (betaN k s + 2 + z) ≤ 1330 * (2 * n) * D * b * ((1 + 17 * C₀) * (b * Y)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = 2660 * (1 + 17 * C₀) * (b ^ 2 * D * Y * n) := by ring

/-- The argument of the logarithm in the bound of the solver: K·(λ + B) ≤ 2^(5·17·C₀·Y + 16). -/
theorem argO_le (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) (hD : 2 ^ betaN k s ≤ n + 1) :
    K * (lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) + bitsS K (3 * K ^ 8) (PbOL K n (2 ^ betaN k s)) 0)
      ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) := by
  have hK1 : 1 ≤ K := by omega
  have hn1 := succ_le_two_pow hlt
  have hz := size_n_le hlt
  obtain ⟨t, ht⟩ : ∃ t, t = 17 * C₀ * K.size := ⟨_, rfl⟩
  rw [← ht] at hn1 hz ⊢
  have hnt : n ≤ 2 ^ t := by omega
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have hKt : K ≤ 2 ^ t := hKn.trans hnt
  have hDt : 2 ^ betaN k s ≤ 2 ^ t := hD.trans hn1
  have hbt : betaN k s + 3 ≤ 2 ^ t := (b_le_D k s).trans hDt
  have hb1t : betaN k s + 1 ≤ 2 ^ t := by omega
  have hkt : k ≤ 2 ^ t := ((k_le_beta k s).trans (Nat.le_add_right _ 3)).trans hbt
  have hK16 : K ^ 16 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hK3 : K ^ 3 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hzt : n.size ≤ 2 ^ t := hz.trans Nat.lt_two_pow_self.le
  have u1 : 354 * k * n * (betaN k s + 1) ≤ 2 ^ (9 + t + t + t) := mul_le_pow (mul_le_pow (mul_le_pow (by norm_num) hkt) hnt) hb1t
  have u2 : 54 * K ^ 16 ≤ 2 ^ (6 + t) := mul_le_pow (by norm_num) hK16
  have hUb : UbOL k K n (2 ^ betaN k s) ≤ 2 ^ (3 * t + 10) := (UbO_le hn0).trans (add_le_pow u1 u2 (by omega) (by omega))
  have u3 : betaN k s + 2 + n.size ≤ 2 ^ (t + 1) := by rw [pow_succ]; omega
  have u4 : 2 * n ≤ 2 ^ (1 + t) := mul_le_pow (by norm_num) hnt
  have hgP : 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ 2 ^ (11 + (1 + t) + t + t + (t + 1)) :=
    (gPO_le hn0 (pow_le_n hK1 hn17 (by norm_num))).trans (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (by norm_num) u4) hDt) hb1t) u3)
  have hlam : lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) ≤ 2 ^ (4 * t + 14) := by
    have h1 := lamS_mul_le K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s))
    have h2 : lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) ≤
        lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) * K ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : K ^ 3 + K * UbOL k K n (2 ^ betaN k s) ≤ 2 ^ (4 * t + 11) := add_le_pow hK3 (mul_le_pow hKt hUb) (by omega) (by omega)
    exact (h2.trans h1).trans (add_le_pow h3 hgP (by omega) (by omega))
  have hB : bitsS K (3 * K ^ 8) (PbOL K n (2 ^ betaN k s)) 0 ≤ 2 ^ (11 + (1 + t) + t + t + (t + 1) + 1) := by
    have e : bitsS K (3 * K ^ 8) (PbOL K n (2 ^ betaN k s)) 0 = PbOL K n (2 ^ betaN k s) * (6 * K ^ 7) := by simp [bitsS, Arith.two_g_div hK1]
    have h7 : K ^ 7 ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
    rw [e, pow_succ]
    calc PbOL K n (2 ^ betaN k s) * (6 * K ^ 7) ≤ PbOL K n (2 ^ betaN k s) * (6 * K ^ 8) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h7)
      _ = 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) * 2 := by ring
      _ ≤ 2 ^ (11 + (1 + t) + t + t + (t + 1)) * 2 := Nat.mul_le_mul_right _ hgP
  have hsum := add_le_pow (r := 4 * t + 15) hlam hB (by omega) (by omega)
  exact (mul_le_pow hKt hsum).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The parts of lower order of the exponent, each multiplied by K. -/
theorem lowerO (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    K * (3 * K ^ 8 * K.size) ≤ 3 * (Wof k K s * n) ∧
    K * (PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GO C₀ * (Wof k K s * n) ∧
    K * ((K - 1) * lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s))) ≤ (55 + 354 * k + GO C₀) * (Wof k K s * n) ∧
    3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ GO C₀ * (Wof k K s * n) ∧
    K * (54 * K ^ 16) ≤ 54 * (Wof k K s * n) ∧
    K * K ^ 2 ≤ Wof k K s * n ∧
    K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (Wof k K s * n) ∧
    K * (3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1))) ≤ 27 * (4 + 17 * C₀) * (Wof k K s * n) ∧
    K * ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)) ≤ (17 + 51 * C₀) * (Wof k K s * n) := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨-, -, -, w4, w5, w6, -, w8⟩ := Wof_ge (k := k) (s := s) hK1
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK1
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have gP := gPO_le_W (k := k) (s := s) hK1 hn17 hlt
  have hUb := UbO_le (k := k) (K := K) (s := s) hn0
  have hkb : k ≤ betaN k s := k_le_beta k s
  have hsb := size_blk_le (betaN k s) n
  have hsm := size_mul_le (betaN k s) n
  obtain ⟨W, hW⟩ : ∃ W, W = Wof k K s := ⟨_, rfl⟩
  rw [← hW] at w4 w5 w6 w8 gP ⊢
  obtain ⟨b, hb⟩ : ∃ b, b = betaN k s + 3 := ⟨_, rfl⟩
  rw [← hb] at w4 w6
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = K.size := ⟨_, rfl⟩
  rw [← hYd] at w4 w5 hz hY ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = GO C₀ := ⟨_, rfl⟩
  rw [← hG] at gP ⊢
  have hb1 : 1 ≤ b := by omega
  have Wn : n ≤ W * n := Nat.le_mul_of_pos_left _ w8
  have K16 : K * K ^ 16 ≤ n := by rw [← pow_succ']; exact hn17
  have a1 : b ≤ b * Y := Nat.le_mul_of_pos_right _ hY
  have a2 : 17 * C₀ * Y ≤ 17 * C₀ * (b * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hb1)
  have UbW : UbOL k K n (2 ^ betaN k s) ≤ (354 * k + 54) * (W * n) := by
    have c1 : 354 * k * n * (betaN k s + 1) ≤ 354 * k * (W * n) := by
      calc 354 * k * n * (betaN k s + 1) = 354 * k * ((betaN k s + 1) * n) := by ring
        _ ≤ 354 * k * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ((by omega : betaN k s + 1 ≤ b).trans w6))
    have c2 : 54 * K ^ 16 ≤ 54 * (W * n) := Nat.mul_le_mul_left _ ((pow_le_n hK1 hn17 (by norm_num)).trans Wn)
    calc UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := hUb
      _ ≤ 354 * k * (W * n) + 54 * (W * n) := Nat.add_le_add c1 c2
      _ = (354 * k + 54) * (W * n) := by ring
  refine ⟨?_, ?_, ?_, gP, ?_, ?_, ?_, ?_, ?_⟩
  · calc K * (3 * K ^ 8 * Y) = 3 * (Y * K ^ 9) := by ring
      _ ≤ 3 * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul w5 (pow_le_n hK1 hn17 (by norm_num)))
  · have h1 : K * (2 * (3 * K ^ 8) / K + 1) ≤ 3 * (3 * K ^ 8) := by
      rw [Arith.two_g_div hK1]
      have h7 : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
      have e : K * (6 * K ^ 7 + 1) = 6 * K ^ 8 + K := by ring
      omega
    calc K * (PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1)) = PbOL K n (2 ^ betaN k s) * (K * (2 * (3 * K ^ 8) / K + 1)) := by ring
      _ ≤ PbOL K n (2 ^ betaN k s) * (3 * (3 * K ^ 8)) := Nat.mul_le_mul_left _ h1
      _ = 3 * (3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := by ring
      _ ≤ 3 * (G * (W * n)) := Nat.mul_le_mul_left _ gP
      _ = 3 * G * (W * n) := by ring
  · have h1 := lamS_mul_le K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s))
    generalize lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) = lam at h1 ⊢
    have h2 : K * (K ^ 2 * lam) ≤ K * (K ^ 2 + UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := by
      have : 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ K * (3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := Nat.le_mul_of_pos_left _ hK1
      calc K * (K ^ 2 * lam) = lam * K ^ 3 := by ring
        _ ≤ K ^ 3 + K * UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) := h1
        _ ≤ K ^ 3 + K * UbOL k K n (2 ^ betaN k s) + K * (3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := Nat.add_le_add_left this _
        _ = K * (K ^ 2 + UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := by ring
    have h3 := Nat.le_of_mul_le_mul_left h2 hK1
    have h4 : K ^ 2 ≤ W * n := (pow_le_n hK1 hn17 (by norm_num)).trans Wn
    calc K * ((K - 1) * lam) ≤ K * (K * lam) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      _ = K ^ 2 * lam := by ring
      _ ≤ K ^ 2 + UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) := h3
      _ ≤ W * n + (354 * k + 54) * (W * n) + G * (W * n) := Nat.add_le_add (Nat.add_le_add h4 UbW) gP
      _ = (55 + 354 * k + G) * (W * n) := by ring
  · calc K * (54 * K ^ 16) = 54 * (K * K ^ 16) := by ring
      _ ≤ 54 * (W * n) := Nat.mul_le_mul_left _ (K16.trans Wn)
  · calc K * K ^ 2 = K ^ 3 := by ring
      _ ≤ n := pow_le_n hK1 hn17 (by norm_num)
      _ ≤ W * n := Wn
  · have h1 : 5 * (17 * C₀ * Y) + 16 ≤ (85 * C₀ + 16) * W := by
      calc 5 * (17 * C₀ * Y) + 16 ≤ 85 * C₀ * Y + 16 * Y := by nlinarith
        _ = (85 * C₀ + 16) * Y := by ring
        _ ≤ (85 * C₀ + 16) * W := Nat.mul_le_mul_left _ w5
    calc K * (C₀ * K ^ 2 * (5 * (17 * C₀ * Y) + 16)) = C₀ * ((5 * (17 * C₀ * Y) + 16) * K ^ 3) := by ring
      _ ≤ C₀ * ((85 * C₀ + 16) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (pow_le_n hK1 hn17 (by norm_num)))
      _ = C₀ * (85 * C₀ + 16) * (W * n) := by ring
  · have h2 : Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) ≤ (4 + 17 * C₀) * W := by
      calc Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) ≤ 2 * betaN k s + n.size + 10 := hsb
        _ ≤ 4 * (b * Y) + 17 * C₀ * (b * Y) := by omega
        _ = (4 + 17 * C₀) * (b * Y) := by ring
        _ ≤ (4 + 17 * C₀) * W := Nat.mul_le_mul_left _ w4
    calc K * (3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)))
        = 27 * (Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) * K ^ 17) := by ring
      _ ≤ 27 * ((4 + 17 * C₀) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 hn17)
      _ = 27 * (4 + 17 * C₀) * (W * n) := by ring
  · have h1 : (3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) ≤ (17 + 51 * C₀) * (b * Y) := by
      have c1 : (k + 9) * n.size ≤ 3 * b * (17 * C₀ * Y) := Nat.mul_le_mul (by omega) hz
      have e1 : (k + 3) * n.size + 6 * n.size = (k + 9) * n.size := by ring
      have c2 : 4 * betaN k s + 5 * k + 24 ≤ 17 * b := by omega
      calc (3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)
          ≤ (4 * betaN k s + 5 * k + 24) + (k + 9) * n.size := by omega
        _ ≤ 17 * b + 3 * b * (17 * C₀ * Y) := Nat.add_le_add c2 c1
        _ ≤ 17 * (b * Y) + 3 * b * (17 * C₀ * Y) := Nat.add_le_add_right (Nat.mul_le_mul_left _ a1) _
        _ = (17 + 51 * C₀) * (b * Y) := by ring
    calc K * ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size))
        ≤ n * ((17 + 51 * C₀) * (b * Y)) := Nat.mul_le_mul hKn h1
      _ = (17 + 51 * C₀) * (b * Y * n) := by ring
      _ ≤ (17 + 51 * C₀) * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ w4)

end nat

/-! ### Real numbers -/

/-- The inequalities of `lowerO` between real numbers. -/
theorem lowerOR {k K n s C₀ : ℕ} (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * GO C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) : ℕ) : ℝ) ≤
      ((55 + 354 * k + GO C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    ((3 * K ^ 8 * PbOL K n (2 ^ betaN k s) : ℕ) : ℝ) ≤ (GO C₀ : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((54 * K ^ 16 : ℕ) : ℝ) ≤ 54 * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (K : ℝ) ^ 2 ≤ ((Wof k K s : ℕ) : ℝ) * n ∧
    (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) : ℕ) : ℝ) ≤ ((27 * (4 + 17 * C₀) : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ) ≤
      ((17 + 51 * C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := lowerO (k := k) (s := s) (C₀ := C₀) hK hn17 hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast o1
  · exact_mod_cast o2
  · exact_mod_cast o3
  · exact_mod_cast o4
  · exact_mod_cast o5
  · exact_mod_cast o6
  · exact_mod_cast o7
  · exact_mod_cast o8
  · exact_mod_cast o9

/-- The estimate of the exponent, between real numbers: the parts T1, T2, T3, R1, Rx of lower order
and the exponent nd of the solver; M is the main part of the bound on the shared bits. -/
theorem real_coreM {Kr e n W A C₀ M T1 T2 T3 R1 Rx gP U36 Ubr Lc Lg lam nd c1 c2 c3 c4 c5 c7 c8 c9 : ℝ}
    (hKr : 0 < Kr) (he0 : 0 < e) (he1 : e ≤ 1) (hn0 : 0 ≤ n) (hC0 : 0 ≤ C₀) (hgP0 : 0 ≤ gP) (hU36 : 0 ≤ U36)
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) (h9 : 0 ≤ c9) (hM : W ≤ A * Kr * e)
    (r1 : Kr * T1 ≤ c1 * (W * n)) (r2 : Kr * T2 ≤ c2 * (W * n)) (r3 : Kr * T3 ≤ c3 * (W * n)) (r4 : gP ≤ c4 * (W * n))
    (r5 : Kr * U36 ≤ c5 * (W * n)) (r6 : Kr * Kr ^ 2 ≤ W * n) (r7 : Kr * (C₀ * Kr ^ 2 * Lc) ≤ c7 * (W * n)) (r8 : Kr * R1 ≤ c8 * (W * n))
    (r9 : Kr * Rx ≤ c9 * (W * n)) (rU : Ubr ≤ M + U36) (rL : lam * Kr ^ 3 ≤ Kr ^ 3 + Kr * Ubr + gP)
    (hr : nd ≤ e * Kr ^ 2 * lam + C₀ * Kr ^ 2 * Lg) (hlog : Lg ≤ Lc) :
    T1 + T2 + T3 + nd + R1 + Rx ≤ e * M + (c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9) * A * (n * e) := by
  have e1 : Kr * (gP / Kr) = gP := by field_simp
  have hl2 : Kr ^ 2 * lam ≤ Kr ^ 2 + Ubr + gP / Kr := by
    have g1 : Kr * (Kr ^ 2 * lam) ≤ Kr * (Kr ^ 2 + Ubr + gP / Kr) := by
      calc Kr * (Kr ^ 2 * lam) = lam * Kr ^ 3 := by ring
        _ ≤ Kr ^ 3 + Kr * Ubr + gP := rL
        _ = Kr * (Kr ^ 2 + Ubr + gP / Kr) := by rw [mul_add, mul_add, e1]; ring
    exact le_of_mul_le_mul_left g1 hKr
  have hgK0 : 0 ≤ gP / Kr := div_nonneg hgP0 hKr.le
  have hK2 : 0 ≤ Kr ^ 2 := by positivity
  have hnd : nd ≤ e * M + (Kr ^ 2 + U36 + gP / Kr + C₀ * Kr ^ 2 * Lc) := by
    have a1 : e * Kr ^ 2 * lam ≤ e * (Kr ^ 2 + (M + U36) + gP / Kr) := by
      calc e * Kr ^ 2 * lam = e * (Kr ^ 2 * lam) := by ring
        _ ≤ e * (Kr ^ 2 + Ubr + gP / Kr) := mul_le_mul_of_nonneg_left hl2 he0.le
        _ ≤ e * (Kr ^ 2 + (M + U36) + gP / Kr) := mul_le_mul_of_nonneg_left (by linarith) he0.le
    have a2 : e * (Kr ^ 2 + U36 + gP / Kr) ≤ 1 * (Kr ^ 2 + U36 + gP / Kr) := mul_le_mul_of_nonneg_right he1 (by linarith)
    have a3 : C₀ * Kr ^ 2 * Lg ≤ C₀ * Kr ^ 2 * Lc := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC0 hK2)
    have e2 : e * (Kr ^ 2 + (M + U36) + gP / Kr) = e * M + e * (Kr ^ 2 + U36 + gP / Kr) := by ring
    linarith
  obtain ⟨X, hX⟩ : ∃ X, X = T1 + T2 + T3 + (Kr ^ 2 + U36 + gP / Kr + C₀ * Kr ^ 2 * Lc) + R1 + Rx := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9 := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hcc]; linarith
  have hKX : Kr * X ≤ cc * (W * n) := by
    have e3 : Kr * X = Kr * T1 + Kr * T2 + Kr * T3 + (Kr * Kr ^ 2 + Kr * U36 + Kr * (gP / Kr) + Kr * (C₀ * Kr ^ 2 * Lc)) + Kr * R1 + Kr * Rx := by
      rw [hX]; ring
    have e4 : cc * (W * n) = c1 * (W * n) + c2 * (W * n) + c3 * (W * n) + c4 * (W * n) + c5 * (W * n) + W * n + c7 * (W * n) + c8 * (W * n) + c9 * (W * n) := by
      rw [hcc]; ring
    rw [e3, e4, e1]
    linarith
  have hXle : X ≤ cc * A * (n * e) := by
    have g1 : Kr * X ≤ Kr * (cc * A * (n * e)) := by
      calc Kr * X ≤ cc * (W * n) := hKX
        _ ≤ cc * (A * Kr * e * n) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hn0) hcc0
        _ = Kr * (cc * A * (n * e)) := by ring
    exact le_of_mul_le_mul_left g1 hKr
  rw [← hcc]
  rw [hX] at hXle
  linarith

/-- The main term and the rest, in terms of n·e·(s+1). -/
theorem real_finalO {e n k b ck q cA Z R3 N : ℝ} (he0 : 0 ≤ e) (hn0 : 0 ≤ n) (hk0 : 0 ≤ k) (hq : 1 ≤ q) (hcA : 0 ≤ cA)
    (rb : b ≤ ck * q) (hZ : Z ≤ e * (354 * k * n * b) + cA * (n * e)) (hR3 : R3 ≤ n * e) (hN : N ≤ Z + R3) :
    N ≤ (354 * k * ck + cA + 1) * n * e * q := by
  have hne : 0 ≤ n * e := mul_nonneg hn0 he0
  have hne2 : n * e ≤ n * e * q := le_mul_of_one_le_right hne hq
  have hmain : e * (354 * k * n * b) ≤ (354 * k * ck) * (n * e * q) := by
    calc e * (354 * k * n * b) = 354 * k * (n * e) * b := by ring
      _ ≤ 354 * k * (n * e) * (ck * q) := mul_le_mul_of_nonneg_left rb (mul_nonneg (mul_nonneg (by norm_num) hk0) hne)
      _ = (354 * k * ck) * (n * e * q) := by ring
  have h2 := mul_le_mul_of_nonneg_left hne2 hcA
  have e1 : (354 * k * ck + cA + 1) * n * e * q = (354 * k * ck) * (n * e * q) + cA * (n * e * q) + n * e * q := by ring
  rw [e1]
  linarith

/-- The sum of the constants of the parts of lower order. -/
def ccO (k C₀ : ℕ) : ℕ := 3 + 3 * GO C₀ + (55 + 354 * k + GO C₀) + GO C₀ + 54 + 1 + C₀ * (85 * C₀ + 16) + 27 * (4 + 17 * C₀) + (17 + 51 * C₀)

/-- The exponent as a sum of its parts. -/
theorem needO_le_sum {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {k n s : ℕ} (hD : 2 ^ betaN k s ≤ n + 1) :
    needO S k i n s ≤ 3 * S.K i ^ 8 * (S.K i).size + PbOL (S.K i) n (2 ^ betaN k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) +
      ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)) + n / 2 ^ s := by
  have hblock : blockN k n s = 2 ^ betaN k s := min_eq_left hD
  unfold needO needNet restO
  rw [hblock]
  generalize S.need _ = nd
  generalize 3 * S.K i ^ 8 * (S.K i).size = x1
  generalize PbOL (S.K i) n (2 ^ betaN k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) = x2
  generalize (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) = x3
  generalize 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) = x4
  generalize (k + 3) * n.size = x5
  generalize n / 2 ^ s = x6
  generalize Nat.size (2 ^ betaN k s * n) = x7
  omega

/-- The exponent `needO` is at most (354k·c_k + cc·A₁ + 1)·n·e·(s+1). -/
theorem needO_le {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n s A₁ : ℕ} (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (hD : 2 ^ betaN k s ≤ n + 1) (he0 : 0 < e) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e)
    (hM : ((Wof k (S.K i) s : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needO S k i n s : ℝ) ≤ ((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1) := by
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn1 : 1 ≤ n := hK1.trans hKn
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := lowerOR (k := k) (s := s) (C₀ := C₀) hK hn17 hlt
  have harg := argO_le (k := k) (s := s) (C₀ := C₀) hK hn17 hlt hD
  have hlam1 := one_le_lamS hK1 (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))
  have hlamK := lamS_mul_le (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))
  have hUb := UbO_le (k := k) (K := S.K i) (s := s) hn1
  have hB1 : 1 ≤ bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 := by
    have e1 : bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 = PbOL (S.K i) n (2 ^ betaN k s) * (6 * S.K i ^ 7) := by
      simp [bitsS, Arith.two_g_div hK1]
    rw [e1]
    exact Nat.mul_pos (one_le_PbOL hn1 hK1) (by positivity)
  have hr := hrate _ _ hlam1 hB1
  have hsum := needO_le_sum S i hD
  have hlog : Real.logb 2 ((S.K i : ℝ) * ((lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) : ℝ) +
      (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 : ℝ))) ≤ ((5 * (17 * C₀ * (S.K i).size) + 16 : ℕ) : ℝ) := by
    have h := logb_le_of_le_pow _ _ (Nat.mul_pos hK1 (Nat.add_pos_left hlam1 _)) harg
    push_cast at h ⊢
    exact h
  generalize S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0) ()) = nd at hr hsum
  generalize bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0 = Bt at hr hlog
  generalize lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) = lam at hr hlog hsum r3 hlamK
  have rU : ((UbOL k (S.K i) n (2 ^ betaN k s) : ℕ) : ℝ) ≤ 354 * (k : ℝ) * n * ((betaN k s + 1 : ℕ) : ℝ) + ((54 * S.K i ^ 16 : ℕ) : ℝ) := by exact_mod_cast hUb
  have rL : (lam : ℝ) * (S.K i : ℝ) ^ 3 ≤ (S.K i : ℝ) ^ 3 + (S.K i : ℝ) * ((UbOL k (S.K i) n (2 ^ betaN k s) : ℕ) : ℝ) +
      ((3 * S.K i ^ 8 * PbOL (S.K i) n (2 ^ betaN k s) : ℕ) : ℝ) := by
    exact_mod_cast hlamK
  have rS : (needO S k i n s : ℝ) ≤ (((3 * S.K i ^ 8 * (S.K i).size : ℕ) : ℝ) + ((PbOL (S.K i) n (2 ^ betaN k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) : ℕ) : ℝ) +
      (((S.K i - 1) * lam : ℕ) : ℝ) + (nd : ℝ) + ((3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) : ℕ) : ℝ) +
      (((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ)) + ((n / 2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have rb : ((betaN k s + 1 : ℕ) : ℝ) ≤ (ckN k : ℝ) * ((s : ℝ) + 1) := by
    have : betaN k s + 1 ≤ ckN k * (s + 1) := (by omega : betaN k s + 1 ≤ betaN k s + 3).trans (b_le_lin k s)
    exact_mod_cast this
  have rdiv : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) * e := by
    have h1 : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ s : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : (n : ℝ) / ((2 ^ s : ℕ) : ℝ) = (n : ℝ) * (1 / (2 : ℝ) ^ s) := by push_cast; ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
  have hKr : (0 : ℝ) < (S.K i : ℝ) := by exact_mod_cast hK1
  have core := real_coreM (A := (A₁ : ℝ)) hKr he0 he1 (Nat.cast_nonneg n) (Nat.cast_nonneg C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hM r1 r2 r3 r4 r5 r6 r7 r8 r9 rU rL hr hlog
  have ecc : (3 + ((3 * GO C₀ : ℕ) : ℝ) + ((55 + 354 * k + GO C₀ : ℕ) : ℝ) + (GO C₀ : ℝ) + 54 + 1 + ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) + ((27 * (4 + 17 * C₀) : ℕ) : ℝ) +
      ((17 + 51 * C₀ : ℕ) : ℝ)) * (A₁ : ℝ) = ((ccO k C₀ * A₁ : ℕ) : ℝ) := by
    unfold ccO; push_cast; ring
  rw [ecc] at core
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have fin := real_finalO (ck := (ckN k : ℝ)) (q := (s : ℝ) + 1) he0.le (Nat.cast_nonneg n) (Nat.cast_nonneg k) hq (Nat.cast_nonneg _) rb core rdiv rS
  have efin : ((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) = 354 * (k : ℝ) * (ckN k : ℝ) + ((ccO k C₀ * A₁ : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [efin]
  exact fin

/-! ### The plan -/

/-- The exponent of a plan, or else n, is at most n; and at most `needO` if the five tests are
passed. -/
theorem planAtO_getD_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (c n₀ k n : ℕ) (i : Idx) (s : ℕ) :
    (planAtO S c n₀ k n i s).getD n ≤ n ∧
      ((s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n) →
        (planAtO S c n₀ k n i s).getD n ≤ needO S k i n s) := by
  unfold planAtO needNetC needO needNet
  set x : Idx × U × U := (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (blockN k n s)) 0) ()) with hx
  set a := max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PbOL (S.K i) n (blockN k n s) * (2 * (3 * S.K i ^ 8) / S.K i + 1))
  set d := (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s))
  set r := restO k (S.K i) n s
  by_cases hc : s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n
  · rw [if_pos hc]
    cases h : S.needC (List.replicate n (), x) with
    | none =>
      refine ⟨by simp, fun _ => ?_⟩
      simp only [Option.map_none, Option.bind_none, Option.getD_none]
      by_contra hlt
      have h1 : S.need x ≤ (List.replicate n ()).length := by
        have : S.need x ≤ max a (max d (S.need x)) := (le_max_right _ _).trans (le_max_right _ _)
        simp only [List.length_replicate]
        omega
      rw [hS.needC_some _ x h1] at h
      cases h
    | some v =>
      have hv := hS.needC_eq _ x v h
      subst hv
      simp only [Option.map_some, Option.bind_some]
      split_ifs with h1
      · exact ⟨by simpa using h1, fun _ => by simp⟩
      · exact ⟨by simp, fun _ => by simpa using (not_le.1 h1).le⟩
  · rw [if_neg hc]
    exact ⟨by simp, fun h1 => absurd h1 hc⟩

/-! ### The tests of the plan -/

/-- The exponent c of the fourth test. -/
def cO (k C C₀ : ℕ) : ℕ := Nat.size (a0 k C) + 4 * cK k * C * C₀

/-- The fourth test never fails: Δ = 2^β ≤ (⌊log₂ n⌋ + 1)^c. -/
theorem D_le_log {K n s C C₀ k : ℕ} {e : ℝ} (hK : 2 ≤ K) (hKn : K ≤ n) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C) :
    2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ cO k C C₀ := by
  have hD := D_le (k := k) hK he h2
  have hy : Real.logb 2 K ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) :=
    logb_le_of_le_pow K (Nat.log 2 n + 1) (by omega) (hKn.trans (Nat.lt_pow_succ_log_self (by norm_num) n).le)
  have hy0 : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ K))
  have hL : 2 ≤ Nat.log 2 n + 1 := by
    have := Nat.log_pos (b := 2) (by norm_num) (hK.trans hKn)
    omega
  have ha : a0 k C ≤ (Nat.log 2 n + 1) ^ Nat.size (a0 k C) := (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_left hL _)
  have har : (a0 k C : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ Nat.size (a0 k C) := by exact_mod_cast ha
  have hfin : ((2 ^ betaN k s : ℕ) : ℝ) ≤ (((Nat.log 2 n + 1) ^ cO k C C₀ : ℕ) : ℝ) := by
    calc ((2 ^ betaN k s : ℕ) : ℝ) ≤ (a0 k C : ℝ) * Real.logb 2 K ^ (4 * cK k * C * C₀) := hD
      _ ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ Nat.size (a0 k C) * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (4 * cK k * C * C₀) :=
          mul_le_mul har (pow_le_pow_left₀ hy0 hy _) (pow_nonneg hy0 _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (((Nat.log 2 n + 1) ^ cO k C C₀ : ℕ) : ℝ) := by rw [← pow_add, cO]; push_cast; rfl
  exact_mod_cast hfin

/-- If n ≤ W, then n ≤ A₁·(n·e), by the master inequality. -/
theorem le_of_W {k K n s A₁ : ℕ} {e : ℝ} (hKn : K ≤ n) (he0 : 0 ≤ e) (hnW : n ≤ Wof k K s)
    (hM : ((Wof k K s : ℕ) : ℝ) ≤ (A₁ : ℝ) * K * e) : (n : ℝ) ≤ (A₁ : ℝ) * ((n : ℝ) * e) := by
  have hKr : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
  calc (n : ℝ) ≤ ((Wof k K s : ℕ) : ℝ) := by exact_mod_cast hnW
    _ ≤ (A₁ : ℝ) * K * e := hM
    _ ≤ (A₁ : ℝ) * n * e := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKr (Nat.cast_nonneg _)) he0
    _ = (A₁ : ℝ) * ((n : ℝ) * e) := by ring

/-- If n < n₀, then n ≤ n₀^C₀·(n·e), because 1/e ≤ (log₂ K)^C₀ and K ≤ n. -/
theorem le_of_lt_n0 {K n n₀ C₀ : ℕ} {e : ℝ} (hK : 2 ≤ K) (hKn : K ≤ n) (hn : n < n₀) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) :
    (n : ℝ) ≤ ((n₀ ^ C₀ : ℕ) : ℝ) * ((n : ℝ) * e) := by
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hyK : Real.logb 2 K ≤ (K : ℝ) := logb_le_of_le_pow K K (by omega) Nat.lt_two_pow_self.le
  have hKn0 : (K : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast (hKn.trans hn.le)
  generalize Real.logb 2 K = y at he hy1 hyK
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have hpow : y ^ C₀ ≤ (n₀ : ℝ) ^ C₀ := pow_le_pow_left₀ hy0.le (hyK.trans hKn0) _
  have h3 : (1 : ℝ) ≤ (n₀ : ℝ) ^ C₀ * e := by
    have := mul_le_mul_of_nonneg_left hpow he0.le
    linarith
  push_cast
  calc (n : ℝ) = n * 1 := (mul_one _).symm
    _ ≤ n * ((n₀ : ℝ) ^ C₀ * e) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
    _ = (n₀ : ℝ) ^ C₀ * ((n : ℝ) * e) := by ring

/-- The cases together. -/
theorem combineO {p n e q B c A d : ℝ} (hn : 0 ≤ n) (he : 0 ≤ e) (hq : 1 ≤ q) (hB : 0 ≤ B) (hc : 0 ≤ c) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (h : p ≤ B * n * e * q ∨ p ≤ c * (n * e) ∨ p ≤ A * (n * e) ∨ p ≤ d * (n * e)) : p ≤ (B + c + A + d) * n * e * q := by
  have hne : 0 ≤ n * e := mul_nonneg hn he
  have hbase : n * e ≤ n * e * q := le_mul_of_one_le_right hne hq
  have hT : 0 ≤ n * e * q := hne.trans hbase
  have t1 : 0 ≤ B * (n * e * q) := mul_nonneg hB hT
  have t2 : 0 ≤ c * (n * e * q) := mul_nonneg hc hT
  have t3 : 0 ≤ A * (n * e * q) := mul_nonneg hA hT
  have t4 : 0 ≤ d * (n * e * q) := mul_nonneg hd hT
  have e1 : (B + c + A + d) * n * e * q = B * (n * e * q) + c * (n * e * q) + A * (n * e * q) + d * (n * e * q) := by ring
  have e2 : B * n * e * q = B * (n * e * q) := by ring
  rw [e1]
  rcases h with h | h | h | h
  · rw [e2] at h; linarith
  · have := mul_le_mul_of_nonneg_left hbase hc; linarith
  · have := mul_le_mul_of_nonneg_left hbase hA; linarith
  · have := mul_le_mul_of_nonneg_left hbase hd; linarith

/-- The statement at one level: K the number of nodes, K^17 ≤ n < K^(17·C₀). -/
theorem planAtO_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (i : Idx) {e : ℝ} {C C₀ k n n₀ s A₁ : ℕ} (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e) (heK : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C)
    (hM : ((Wof k (S.K i) s : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤
      (((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) + ((2 ^ s0K k : ℕ) : ℝ) + (A₁ : ℝ) + ((n₀ ^ C₀ : ℕ) : ℝ)) * n * e * ((s : ℝ) + 1) := by
  obtain ⟨p1, p2⟩ := planAtO_getD_le hS (cO k C C₀) n₀ k n i s
  have pn : (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast p1
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) hs
  have hq : (1 : ℝ) ≤ (s : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  obtain ⟨w1, -, -, -, -, -, w7, -⟩ := Wof_ge (k := k) (s := s) hK1
  refine combineO (Nat.cast_nonneg n) he0.le hq (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
  by_cases c1 : s0K k ≤ s
  · by_cases c2 : 2 ^ betaN k s ≤ n + 1
    · by_cases c3 : n₀ ≤ n
      · by_cases c5 : 2 * LD (2 ^ betaN k s) ≤ n
        · have h3 : (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤ (needO S k i n s : ℝ) := by
            exact_mod_cast p2 ⟨c1, c2, c3, D_le_log hK hKn heK h2, c5⟩
          exact Or.inl (h3.trans (needO_le S i hK hn17 hlt c2 he0 he1 hs hM hrate))
        · rw [LD_two_pow] at c5
          have hD2 := two_le_D k s
          have h4 : 2 * (betaN k s + 1) ≤ (betaN k s + 3) * 2 ^ betaN k s := by
            calc 2 * (betaN k s + 1) = (betaN k s + 1) * 2 := by ring
              _ ≤ (betaN k s + 3) * 2 ^ betaN k s := Nat.mul_le_mul (by omega) hD2
          exact Or.inr (Or.inr (Or.inl (pn.trans (le_of_W hKn he0.le (by omega) hM))))
      · exact Or.inr (Or.inr (Or.inr (pn.trans (le_of_lt_n0 hK hKn (not_le.1 c3) heK))))
    · exact Or.inr (Or.inr (Or.inl (pn.trans (le_of_W hKn he0.le (by omega) hM))))
  · exact Or.inr (Or.inl (pn.trans (le_of_small (not_le.1 c1).le hs)))

/-! ### The statement -/

/-- For c = `cO k C C₀` and every n₀: with l the level picked for n and s = s(l), the exponent of
the pad is at most A·n·e_l·(s+1). -/
public theorem stArithO : StArithO := by
  intro Idx _ S e C₀ Q hS slU C k hk h1 h2
  refine ⟨cO k C C₀, fun n₀ => ⟨(354 * k * ckN k + ccO k C₀ * A1 k C C₀ + 1) + 2 ^ s0K k + A1 k C C₀ + n₀ ^ C₀, fun n hn => ?_⟩⟩
  obtain ⟨hr1, hr2⟩ := root17_spec n
  have hK0 : S.K (Q.idx 0) ≤ (root17 n).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
    exact absurd (h'.trans hn) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root17 n)
  have hidx := Q.pick_idx (root17 n)
  have hu := eq_replicate (Q.pick (root17 n)).1
  obtain ⟨l, hl⟩ : ∃ l, l = (Q.pick (root17 n)).1.length := ⟨_, rfl⟩
  rw [← hl] at hu hidx hmax ⊢
  rw [hidx] at hle ⊢
  rw [hu]
  have g1 := h1 l
  have g2 := h2 l
  obtain ⟨s, hs⟩ : ∃ s, s = (slU (List.replicate l ())).length := ⟨_, rfl⟩
  rw [← hs] at g1 g2 ⊢
  have hK2 := Q.K_two l
  have hn17 : S.K (Q.idx l) ^ 17 ≤ n := (Nat.pow_le_pow_left hle 17).trans hr1
  have hlt : n < S.K (Q.idx l) ^ (17 * C₀) := by
    calc n < ((root17 n).length + 1) ^ 17 := hr2
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 17 := Nat.pow_le_pow_left ((Nat.succ_le_of_lt hmax).trans (Q.K_le _)) 17
      _ = S.K (Q.idx l) ^ (17 * C₀) := by rw [← pow_mul, mul_comm]
  have hM := master (k := k) hK2 (Q.e_ge l) g2
  have h := planAtO_le hS (Q.idx l) (k := k) (s := s) (n₀ := n₀) hK2 hn17 hlt (Q.e_le l) g1 (Q.e_ge l) g2 hM (Q.rate l)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]
  exact h

end ClauseBound.ParityChecks.ArithOL
