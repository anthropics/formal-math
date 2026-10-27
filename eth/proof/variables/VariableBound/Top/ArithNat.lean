/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.ArithDefs
import UniformInK.Top.ArithNat
import ClauseBound.ParityChecks.ArithAux
import all ClauseBound.TopN.Arith
import ClauseBound.TopN.Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Step 4, the arithmetic of the exponent: natural numbers, for an arbitrary β

The bounds of Step 4 in natural numbers, derived from `Net.StBounds` (the bounds of Step 3 on the
total U and on g·P, in closed form), which is a hypothesis here. The same kind of arithmetic as in
proof/sparsification/UniformInK/Top/ArithNat.lean, whose lemmas `two_le_D` and `WofU_ge` are used.
β is any natural number, under some of the hypotheses 1 ≤ β, k ≤ β, β + 3 ≤ 2^β. Notation as in
proof/variables/VariableBound/Top/ArithDefs.lean: Δ = D = 2^β, b = β + 3, g = 3K⁸, Y = size K, W =
b²·D·Y. -/

public section

namespace VariableBound.ArithNat

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net

variable {β k K n C₀ : ℕ}

/-- The bound of Step 3 on the total U, in closed form, for Δ = 2^β: U ≤ 140·k·n·(β+1) + 18·K^16,
for β ≥ 1 and n ≥ 1, given `Net.StBounds`. -/
theorem UbD_le (hB : StBounds) (hβ : 1 ≤ β) (hn : 1 ≤ n) : UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16 := by
  have h := (hB k K n (2 ^ β) hn (two_le_D hβ)).1
  rw [LD_two_pow] at h
  calc UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 2 * (3 * K ^ 8) ^ 2 := h
    _ = 140 * k * n * (β + 1) + 18 * K ^ 16 := by ring

/-- The bound of Step 3 on g·P, in closed form, for Δ = 2^β: g·P ≤ n·2^β·(842·(β+3) + 4·size n), for
β ≥ 1, n ≥ 1 and g = 3K⁸ ≤ n, given `Net.StBounds`. -/
theorem gPD_le (hB : StBounds) (hβ : 1 ≤ β) (hn : 1 ≤ n) (hg : 3 * K ^ 8 ≤ n) :
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ n * 2 ^ β * (842 * (β + 3) + 4 * n.size) := by
  have h := (hB 0 K n (2 ^ β) hn (two_le_D hβ)).2
  unfold tbMax sbMax at h
  rw [LD_two_pow] at h
  refine h.trans ?_
  have hc : Nat.clog 2 (2 ^ β * n) ≤ β + n.size := (clog_le_size _).trans (size_mul_le β n)
  have hD : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  generalize Nat.clog 2 (2 ^ β * n) = c at hc
  generalize 3 * K ^ 8 = g at hg
  generalize n.size = z at hc
  generalize 2 ^ β = D at hD
  have h1 : 1 + D * (c + 33 * (β + 1) + 1 + 3) ≤ D * (34 * β + z + 38) := by
    calc 1 + D * (c + 33 * (β + 1) + 1 + 3) ≤ D + D * (34 * β + z + 37) := Nat.add_le_add hD (Nat.mul_le_mul_left _ (by omega))
      _ = D * (34 * β + z + 38) := by ring
  calc 2 * (n + g) * (1 + D * (c + 33 * (β + 1) + 1 + 3)) + 2 * (10 * n + g) * (32 * D * (β + 1)) + g
      ≤ 4 * n * (D * (34 * β + z + 38)) + 22 * n * (32 * D * (β + 1)) + n * D :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul (by omega) h1) (Nat.mul_le_mul_right _ (by omega))) (hg.trans (Nat.le_mul_of_pos_right _ hD))
    _ = n * D * (840 * β + 4 * z + 857) := by ring
    _ ≤ n * D * (842 * (β + 3) + 4 * z) := Nat.mul_le_mul_left _ (by omega)

/-- Step 4, «g ≤ n»: 3K⁸ ≤ n, for 2 ≤ K and K^17 ≤ n. -/
theorem g_le_n (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) : 3 * K ^ 8 ≤ n := by
  have h4 : 3 ≤ K ^ 2 := by nlinarith
  calc 3 * K ^ 8 ≤ K ^ 2 * K ^ 8 := Nat.mul_le_mul_right _ h4
    _ = K ^ 10 := by ring
    _ ≤ n := pow_le_n (by omega) hn17 (by norm_num)

/-- g·P ≤ G·W·n, where G = `GD C₀`, for β ≥ 1, 2 ≤ K and K^17 ≤ n < K^(17·C₀). -/
theorem gPD_le_W (hB : StBounds) (hβ : 1 ≤ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) := by
  have hK1 : 1 ≤ K := by omega
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have h := gPD_le hB hβ (hK1.trans hKn) (g_le_n hK hn17)
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK1
  refine h.trans ?_
  unfold WofU GD
  generalize K.size = Y at hz hY
  generalize n.size = z at hz
  generalize 2 ^ β = D
  have hb1 : 1 ≤ β + 3 := by omega
  generalize β + 3 = b at hb1
  have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
  have a1 : b ≤ b ^ 2 * Y := hbb.trans (Nat.le_mul_of_pos_right _ hY)
  have a2 : Y ≤ b ^ 2 * Y := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hb1)
  have h2 : 842 * b + 4 * z ≤ (842 + 68 * C₀) * (b ^ 2 * Y) := by
    calc 842 * b + 4 * z ≤ 842 * (b ^ 2 * Y) + 4 * (17 * C₀ * (b ^ 2 * Y)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ a1) (Nat.mul_le_mul_left _ (hz.trans (Nat.mul_le_mul_left _ a2)))
      _ = (842 + 68 * C₀) * (b ^ 2 * Y) := by ring
  calc n * D * (842 * b + 4 * z) ≤ n * D * ((842 + 68 * C₀) * (b ^ 2 * Y)) := Nat.mul_le_mul_left _ h2
    _ = (842 + 68 * C₀) * (b ^ 2 * D * Y * n) := by ring

/-- The bound B' = `bitsS` for the bit length of the entries of the rebalanced instance, for g = 3K⁸
and K ≥ 1: B' = P·6K⁷ + B·(6K⁸ + 36K^15). The paper's B' is ⌈2gP/K⌉ + g²·B = 6K⁷·P + 9K^16·B. -/
theorem bitsS_eq (hK : 1 ≤ K) (P B : ℕ) : bitsS K (3 * K ^ 8) P B = P * (6 * K ^ 7) + B * (6 * K ^ 8 + 36 * K ^ 15) := by
  unfold bitsS
  rw [Arith.two_g_div hK]
  ring

/-- Step 4, «the numbers L and B' are polynomial in n»: K·(λ + B') ≤ 2^(5·17·C₀·Y + 16), for k ≤ β,
β + 3 ≤ 2^β ≤ n + 1, 2 ≤ K and K^17 ≤ n < K^(17·C₀). -/
theorem argD_le (hB : StBounds) (hkβ : k ≤ β) (hbD : β + 3 ≤ 2 ^ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) (hD : 2 ^ β ≤ n + 1) :
    K * (lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) + bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n))
      ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) := by
  have hβ : 1 ≤ β := by
    rcases Nat.eq_zero_or_pos β with h | h
    · subst h; omega
    · exact h
  have hK1 : 1 ≤ K := by omega
  have hn1 := succ_le_two_pow hlt
  have hz := size_n_le hlt
  obtain ⟨t, ht⟩ : ∃ t, t = 17 * C₀ * K.size := ⟨_, rfl⟩
  rw [← ht] at hn1 hz ⊢
  have hnt : n ≤ 2 ^ t := by omega
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have hKt : K ≤ 2 ^ t := hKn.trans hnt
  have hDt : 2 ^ β ≤ 2 ^ t := hD.trans hn1
  have hbt : β + 3 ≤ 2 ^ t := hbD.trans hDt
  have hb1t : β + 1 ≤ 2 ^ t := by omega
  have hkt : k ≤ 2 ^ t := by omega
  have hk1t : k + 1 ≤ 2 ^ t := by omega
  have hK16 : K ^ 16 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hK15 : K ^ 15 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hK3 : K ^ 3 ≤ 2 ^ t := (pow_le_n hK1 hn17 (by norm_num)).trans hnt
  have hzt : n.size ≤ 2 ^ t := hz.trans Nat.lt_two_pow_self.le
  have u1 : 140 * k * n * (β + 1) ≤ 2 ^ (8 + t + t + t) := mul_le_pow (mul_le_pow (mul_le_pow (by norm_num) hkt) hnt) hb1t
  have u2 : 18 * K ^ 16 ≤ 2 ^ (5 + t) := mul_le_pow (by norm_num) hK16
  have hUb : UbD k K n (2 ^ β) ≤ 2 ^ (3 * t + 9) := (UbD_le hB hβ hn0).trans (add_le_pow u1 u2 (by omega) (by omega))
  have v1 : 842 * (β + 3) ≤ 2 ^ (10 + t) := mul_le_pow (by norm_num) hbt
  have v2 : 4 * n.size ≤ 2 ^ (2 + t) := mul_le_pow (by norm_num) hzt
  have hgP : 3 * K ^ 8 * PbD K n (2 ^ β) ≤ 2 ^ (t + t + (t + 11)) :=
    (gPD_le hB hβ hn0 (g_le_n hK hn17)).trans (mul_le_pow (mul_le_pow hnt hDt) (add_le_pow v1 v2 (by omega) (by omega)))
  have hlam : lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) ≤ 2 ^ (4 * t + 12) := by
    have h1 := lamS_mul_le K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))
    have h2 : lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) ≤
        lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) * K ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : K ^ 3 + K * UbD k K n (2 ^ β) ≤ 2 ^ (4 * t + 10) := add_le_pow hK3 (mul_le_pow hKt hUb) (by omega) (by omega)
    exact (h2.trans h1).trans (add_le_pow h3 hgP (by omega) (by omega))
  have hBt : bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n) ≤ 2 ^ (3 * t + 13) := by
    rw [bitsS_eq hK1]
    have h7 : K ^ 7 ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
    have h8 : K ^ 8 ≤ K ^ 15 := Nat.pow_le_pow_right hK1 (by norm_num)
    have p1 : PbD K n (2 ^ β) * (6 * K ^ 7) ≤ 2 ^ (t + t + (t + 11) + 1) := by
      rw [pow_succ]
      calc PbD K n (2 ^ β) * (6 * K ^ 7) ≤ PbD K n (2 ^ β) * (6 * K ^ 8) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h7)
        _ = 3 * K ^ 8 * PbD K n (2 ^ β) * 2 := by ring
        _ ≤ 2 ^ (t + t + (t + 11)) * 2 := Nat.mul_le_mul_right _ hgP
    have p2 : BbD k n ≤ 2 ^ (2 * t + 5) := by
      unfold BbD BD
      exact add_le_pow (q := 0) (mul_le_pow hk1t (mul_le_pow (p := 4) (by norm_num) hnt)) (by norm_num) (by omega) (by omega)
    have p3 : 6 * K ^ 8 + 36 * K ^ 15 ≤ 2 ^ (6 + t) :=
      (by omega : 6 * K ^ 8 + 36 * K ^ 15 ≤ 42 * K ^ 15).trans (mul_le_pow (by norm_num) hK15)
    exact add_le_pow p1 (mul_le_pow p2 p3) (by omega) (by omega)
  have hsum := add_le_pow (r := 4 * t + 14) hlam hBt (by omega) (by omega)
  exact (mul_le_pow hKt hsum).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The bit length of the bound for the number of objects, for Δ = 2^β: at most 2β + size n + 10. -/
theorem size_objMax_le (β n : ℕ) : Nat.size (objMax n (2 ^ β)) ≤ 2 * β + n.size + 10 := by
  rw [Nat.size_le]
  unfold objMax sbMax
  rw [LD_two_pow]
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h2 : n ≤ 2 ^ n.size := (Nat.lt_size_self n).le
  have h3 : 320 * (β + 1) + 1 ≤ 2 ^ (9 + β) := by rw [pow_add]; omega
  calc 10 * n * (32 * 2 ^ β * (β + 1)) + 2 ^ β * n = n * 2 ^ β * (320 * (β + 1) + 1) := by ring
    _ ≤ 2 ^ (n.size + β + (9 + β)) := mul_le_pow (mul_le_pow h2 le_rfl) h3
    _ < 2 ^ (2 * β + n.size + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The bit length of the bound for the list of checks, for Δ = 2^β: at most 3β + 2·size n + 17. -/
theorem size_lists_le (β n : ℕ) : Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) ≤ 3 * β + 2 * n.size + 17 := by
  rw [Nat.size_le]
  unfold sbMax
  rw [LD_two_pow]
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h2 : n + 1 ≤ 2 ^ n.size := Nat.lt_size_self n
  have h3 : 10 * n + 1 ≤ 2 ^ (4 + n.size) := by rw [pow_add]; omega
  have h4 : 32 * 2 ^ β * (β + 1) + 1 ≤ 2 ^ (6 + β + β) := by
    have a1 : 32 * 2 ^ β * (β + 1) ≤ 2 ^ (5 + β + β) := mul_le_pow (mul_le_pow (by norm_num) le_rfl) h1
    exact add_le_pow (q := 0) a1 (by norm_num) (by omega) (by omega)
  have h5 : Nat.size (2 ^ β * n) + 2 ≤ 2 ^ (β + n.size + 2) := (Nat.add_le_add_right (size_mul_le β n) 2).trans Nat.lt_two_pow_self.le
  have h6 : 8 * (10 * n + 1) * (32 * 2 ^ β * (β + 1) + 1) * (Nat.size (2 ^ β * n) + 2) ≤ 2 ^ (3 + (4 + n.size) + (6 + β + β) + (β + n.size + 2)) :=
    mul_le_pow (mul_le_pow (mul_le_pow (by norm_num) h3) h4) h5
  calc 8 * (10 * n + 1) * (32 * 2 ^ β * (β + 1) + 1) * (Nat.size (2 ^ β * n) + 2) + 8 ≤ 2 ^ (3 * β + 2 * n.size + 16) :=
        add_le_pow (q := 3) h6 (by norm_num) (by omega) (by omega)
    _ < 2 ^ (3 * β + 2 * n.size + 17) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Step 4, «all these are o(en)», first half: the parts of lower order of the exponent, each
multiplied by K, are at most a number times W·n; the number depends on C₀ only, except 19 + 140·k +
G, where G = `GD C₀`, for the part
(K − 1)·λ; for 1 ≤ β, k ≤ β, 2 ≤ K and K^17 ≤ n < K^(17·C₀), given `Net.StBounds`. -/
theorem lowerD (hB : StBounds) (hβ : 1 ≤ β) (hkb : k ≤ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    K * (3 * K ^ 8 * K.size) ≤ 3 * (WofU β K * n) ∧
    K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GD C₀ * (WofU β K * n) ∧
    K * ((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))) ≤ (19 + 140 * k + GD C₀) * (WofU β K * n) ∧
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) ∧
    K * (18 * K ^ 16) ≤ 18 * (WofU β K * n) ∧
    K * K ^ 2 ≤ WofU β K * n ∧
    K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (WofU β K * n) ∧
    K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) ≤ 18 * (4 + 17 * C₀) * (WofU β K * n) ∧
    K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤
      (10 + 34 * C₀) * (WofU β K * n) := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨-, -, -, w4, w5, w6, -, w8⟩ := WofU_ge (β := β) hK1
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK1
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have gP := gPD_le_W (C₀ := C₀) hB hβ hK hn17 hlt
  have hUb := UbD_le (k := k) (K := K) hB hβ hn0
  have hso := size_objMax_le β n
  have hsl := size_lists_le β n
  obtain ⟨W, hW⟩ : ∃ W, W = WofU β K := ⟨_, rfl⟩
  rw [← hW] at w4 w5 w6 w8 gP ⊢
  obtain ⟨b, hb⟩ : ∃ b, b = β + 3 := ⟨_, rfl⟩
  rw [← hb] at w4 w6
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = K.size := ⟨_, rfl⟩
  rw [← hYd] at w4 w5 hz hY ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = GD C₀ := ⟨_, rfl⟩
  rw [← hG] at gP ⊢
  have hb1 : 1 ≤ b := by omega
  have Wn : n ≤ W * n := Nat.le_mul_of_pos_left _ w8
  have K16 : K * K ^ 16 ≤ n := by rw [← pow_succ']; exact hn17
  have a1 : b ≤ b * Y := Nat.le_mul_of_pos_right _ hY
  have a2 : 17 * C₀ * Y ≤ 17 * C₀ * (b * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hb1)
  have UbW : UbD k K n (2 ^ β) ≤ (140 * k + 18) * (W * n) := by
    have c1 : 140 * k * n * (β + 1) ≤ 140 * k * (W * n) := by
      calc 140 * k * n * (β + 1) = 140 * k * ((β + 1) * n) := by ring
        _ ≤ 140 * k * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ((by omega : β + 1 ≤ b).trans w6))
    have c2 : 18 * K ^ 16 ≤ 18 * (W * n) := Nat.mul_le_mul_left _ ((pow_le_n hK1 hn17 (by norm_num)).trans Wn)
    calc UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16 := hUb
      _ ≤ 140 * k * (W * n) + 18 * (W * n) := Nat.add_le_add c1 c2
      _ = (140 * k + 18) * (W * n) := by ring
  refine ⟨?_, ?_, ?_, gP, ?_, ?_, ?_, ?_, ?_⟩
  · calc K * (3 * K ^ 8 * Y) = 3 * (Y * K ^ 9) := by ring
      _ ≤ 3 * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul w5 (pow_le_n hK1 hn17 (by norm_num)))
  · have h1 : K * (2 * (3 * K ^ 8) / K + 1) ≤ 3 * (3 * K ^ 8) := by
      rw [Arith.two_g_div hK1]
      have h7 : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
      have e : K * (6 * K ^ 7 + 1) = 6 * K ^ 8 + K := by ring
      omega
    calc K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) = PbD K n (2 ^ β) * (K * (2 * (3 * K ^ 8) / K + 1)) := by ring
      _ ≤ PbD K n (2 ^ β) * (3 * (3 * K ^ 8)) := Nat.mul_le_mul_left _ h1
      _ = 3 * (3 * K ^ 8 * PbD K n (2 ^ β)) := by ring
      _ ≤ 3 * (G * (W * n)) := Nat.mul_le_mul_left _ gP
      _ = 3 * G * (W * n) := by ring
  · have h1 := lamS_mul_le K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))
    generalize lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) = lam at h1 ⊢
    have h2 : K * (K ^ 2 * lam) ≤ K * (K ^ 2 + UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β)) := by
      have : 3 * K ^ 8 * PbD K n (2 ^ β) ≤ K * (3 * K ^ 8 * PbD K n (2 ^ β)) := Nat.le_mul_of_pos_left _ hK1
      calc K * (K ^ 2 * lam) = lam * K ^ 3 := by ring
        _ ≤ K ^ 3 + K * UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β) := h1
        _ ≤ K ^ 3 + K * UbD k K n (2 ^ β) + K * (3 * K ^ 8 * PbD K n (2 ^ β)) := Nat.add_le_add_left this _
        _ = K * (K ^ 2 + UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β)) := by ring
    have h3 := Nat.le_of_mul_le_mul_left h2 hK1
    have h4 : K ^ 2 ≤ W * n := (pow_le_n hK1 hn17 (by norm_num)).trans Wn
    calc K * ((K - 1) * lam) ≤ K * (K * lam) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      _ = K ^ 2 * lam := by ring
      _ ≤ K ^ 2 + UbD k K n (2 ^ β) + 3 * K ^ 8 * PbD K n (2 ^ β) := h3
      _ ≤ W * n + (140 * k + 18) * (W * n) + G * (W * n) := Nat.add_le_add (Nat.add_le_add h4 UbW) gP
      _ = (19 + 140 * k + G) * (W * n) := by ring
  · calc K * (18 * K ^ 16) = 18 * (K * K ^ 16) := by ring
      _ ≤ 18 * (W * n) := Nat.mul_le_mul_left _ (K16.trans Wn)
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
  · have h2 : Nat.size (objMax n (2 ^ β)) ≤ (4 + 17 * C₀) * W := by
      calc Nat.size (objMax n (2 ^ β)) ≤ 2 * β + n.size + 10 := hso
        _ ≤ 4 * (b * Y) + 17 * C₀ * (b * Y) := by omega
        _ = (4 + 17 * C₀) * (b * Y) := by ring
        _ ≤ (4 + 17 * C₀) * W := Nat.mul_le_mul_left _ w4
    calc K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) = 18 * (Nat.size (objMax n (2 ^ β)) * K ^ 17) := by ring
      _ ≤ 18 * ((4 + 17 * C₀) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 hn17)
      _ = 18 * (4 + 17 * C₀) * (W * n) := by ring
  · generalize Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) = sl at hsl ⊢
    have h1 : sl + 2 + (β + 5 * k + 10 + (k + 3) * n.size) ≤ (10 + 34 * C₀) * (b * Y) := by
      have c1 : (k + 5) * n.size ≤ 2 * b * (17 * C₀ * Y) := Nat.mul_le_mul (by omega) hz
      have e1 : (k + 3) * n.size + 2 * n.size = (k + 5) * n.size := by ring
      have c2 : 4 * β + 5 * k + 29 ≤ 10 * b := by omega
      calc sl + 2 + (β + 5 * k + 10 + (k + 3) * n.size) ≤ (4 * β + 5 * k + 29) + (k + 5) * n.size := by omega
        _ ≤ 10 * b + 2 * b * (17 * C₀ * Y) := Nat.add_le_add c2 c1
        _ ≤ 10 * (b * Y) + 2 * b * (17 * C₀ * Y) := Nat.add_le_add_right (Nat.mul_le_mul_left _ a1) _
        _ = (10 + 34 * C₀) * (b * Y) := by ring
    calc K * (sl + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤ n * ((10 + 34 * C₀) * (b * Y)) := Nat.mul_le_mul hKn h1
      _ = (10 + 34 * C₀) * (b * Y * n) := by ring
      _ ≤ (10 + 34 * C₀) * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ w4)

end VariableBound.ArithNat

namespace VariableBound

/-- The bound of Step 3 on the total U, for Δ = 2^β, from the bounds in closed form. -/
theorem stUbD (hB : Net.StBounds) : StUbD := fun _ _ _ _ hβ hn => ArithNat.UbD_le hB hβ hn

/-- Step 4, «the numbers L and B' are polynomial in n», from the bounds in closed form. -/
theorem stArgD (hB : Net.StBounds) : StArgD := fun _ _ _ _ _ hkβ hbD hK hn17 hlt hD => ArithNat.argD_le hB hkβ hbD hK hn17 hlt hD

/-- Step 4, «all these are o(en)», first half, from the bounds in closed form. -/
theorem stLowerD (hB : Net.StBounds) : StLowerD := fun _ _ _ _ _ hβ hkβ hK hn17 hlt => ArithNat.lowerD hB hβ hkβ hK hn17 hlt

end VariableBound
