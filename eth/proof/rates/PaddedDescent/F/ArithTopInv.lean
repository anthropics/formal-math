/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.ArithGlob
public import PaddedDescent.F.ArithTop
public import PaddedDescent.F.ArithWalk

/-! # The invariant at the top, and the budgets of the top

The invariant of the descent holds at the top level for the network of marks; the fixed numbers X,
Z, Qm, Wm, L of `PaddedDescent/F/ArithGlob.lean` satisfy what the
invariant needs of them; all overheads together are below n/2^s; the enumerations of the rebalancing
at the top (colourings, states, labels, indices of a table) and the rounds of the walk fit under a
pad
of length 2^(8·X); the number of layers is large enough. Everywhere s is the precision, n the number
of variables, and the only hypothesis that ties them is
Y⁶ ≤ n for Y = `Ytop s`. No programs occur here. -/

@[expose] public section

namespace PaddedDescent.F.Arith

open PaddedDescent PaddedDescent.F

/-! ### K_t, g_t and Y -/

/-- 1 ≤ K_t. -/
theorem one_le_Ktop (s : ℕ) : 1 ≤ Ktop s := Kseq_pos _

/-- 1 ≤ Y. -/
theorem one_le_Ytop (s : ℕ) : 1 ≤ Ytop s := Ytop_pos s

/-- K_t ≤ `gtop` = 3·K_t⁸. -/
theorem Ktop_le_gtop (s : ℕ) : Ktop s ≤ gtop s := by
  have h : Ktop s ≤ Ktop s ^ 8 := Nat.le_self_pow (by norm_num) _
  rw [gtop_eq]; omega

/-- `gtop` is positive. -/
theorem gtop_pos (s : ℕ) : 0 < gtop s := lt_of_lt_of_le (Kseq_pos _) (Ktop_le_gtop s)

/-- `gtop` is at most its square Y. -/
theorem gtop_le_Ytop (s : ℕ) : gtop s ≤ Ytop s := by
  rw [Ytop_eq_sq]
  exact Nat.le_self_pow (by norm_num) _

/-- 100·K_t⁴ ≤ Y. -/
theorem hundred_Ktop_pow_four_le (s : ℕ) : 100 * Ktop s ^ 4 ≤ Ytop s :=
  mul_Ktop_pow_le_Ytop (C := 100) (e := 4) (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 7 ≤ 500)))
    (by norm_num) s

/-- 100·K_t² ≤ Y. -/
theorem hundred_Ktop_sq_le (s : ℕ) : 100 * Ktop s ^ 2 ≤ Ytop s :=
  le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_Ktop s) (by norm_num))) (hundred_Ktop_pow_four_le s)

/-- 100 ≤ Y. -/
theorem Ytop_ge (s : ℕ) : 100 ≤ Ytop s := by
  have h := hundred_Ktop_sq_le s
  have h1 : 1 ≤ Ktop s ^ 2 := Nat.one_le_pow _ _ (one_le_Ktop s)
  omega

/-- Y² ≤ n follows from Y⁶ ≤ n. -/
theorem Ytop_sq_le {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : Ytop s ^ 2 ≤ n :=
  le_trans (Nat.pow_le_pow_right (one_le_Ytop s) (by norm_num)) hY

/-- 100·Y ≤ n follows from Y⁶ ≤ n. -/
theorem hundred_Ytop_le {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : 100 * Ytop s ≤ n := by
  have h1 := Ytop_sq_le hY
  have h2 : 100 * Ytop s ≤ Ytop s * Ytop s := Nat.mul_le_mul_right _ (Ytop_ge s)
  have h3 : Ytop s * Ytop s = Ytop s ^ 2 := by ring
  omega

/-! ### The bounds Ub and Pb of the network of marks -/

/-- s + 8 ≤ 8·2^s. -/
theorem lin_le_two_pow (s : ℕ) : s + 8 ≤ 8 * 2 ^ s := by
  have h : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  omega

/-- 4·(s + 8)⁶ ≤ 2^(6s+20). -/
theorem coeff_le (s : ℕ) : 4 * (s + 8) ^ 6 ≤ 2 ^ (6 * s + 20) := by
  calc 4 * (s + 8) ^ 6 ≤ 4 * (8 * 2 ^ s) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lin_le_two_pow s) 6)
    _ = 2 ^ (6 * s + 20) := by rw [mul_pow, ← pow_mul, pow_add, Nat.mul_comm s 6]; norm_num; ring

/-- 8·(s + 8)³ + 1 ≤ Y. -/
theorem cube_le_Ytop (s : ℕ) : 8 * (s + 8) ^ 3 + 1 ≤ Ytop s := by
  have h1 : 1 ≤ 2 ^ (3 * s) := Nat.one_le_two_pow
  calc 8 * (s + 8) ^ 3 + 1 ≤ 8 * (8 * 2 ^ s) ^ 3 + 1 := by gcongr; exact lin_le_two_pow s
    _ = 2 ^ 12 * 2 ^ (3 * s) + 1 := by rw [mul_pow, ← pow_mul, Nat.mul_comm s 3]; norm_num; ring
    _ ≤ 2 ^ 13 * 2 ^ (3 * s) := by omega
    _ = 2 ^ (13 + 3 * s) := by rw [← pow_add]
    _ ≤ 2 ^ (52 * s + 694) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Ytop s := Ytop_lower s

/-- Ub ≤ 4·(s + 8)⁶·n + 8·(s + 8)²·Y, for every width k ≤ s. -/
theorem Ubof_le {k s : ℕ} (hk : k ≤ s) (n : ℕ) : Ubof k s n ≤ 4 * (s + 8) ^ 6 * n + 8 * (s + 8) ^ 2 * Ytop s := by
  have h1 := cube_le_Ytop s
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Ytop s := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = s + 8 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = betaOf s := ⟨_, rfl⟩
  have hβx : β + 3 ≤ x ^ 2 := by rw [hβ, hx, betaOf]; nlinarith
  have hkx : k - 1 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  rw [← hY, ← hx] at h1 ⊢
  have e : Ubof k s n = 2 * (2 * β + 6) * ((k - 1) * (n + 2) * (1 + β) + (k - 1) * (n + 1) + Y) := by
    unfold Ubof Ub layersOf
    rw [← hβ, hY, Ytop_eq_sq]
  rw [e]
  have a1 : 2 * β + 6 ≤ 2 * x ^ 2 := by omega
  have a2 : 1 + β ≤ x ^ 2 := by omega
  have a3 : (k - 1) * (n + 2) * (1 + β) + (k - 1) * (n + 1) + Y ≤ x * (n + 2) * (x ^ 2 - 1) + x * (n + 1) + Y := by
    have : 1 + β ≤ x ^ 2 - 1 := by omega
    gcongr
  have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx1
  obtain ⟨q, hq⟩ : ∃ q, x ^ 2 = q + 1 := ⟨x ^ 2 - 1, by omega⟩
  have a4 : x * (n + 2) * (x ^ 2 - 1) + x * (n + 1) + Y ≤ x ^ 3 * n + (2 * x ^ 3 + Y) := by
    have e3 : x ^ 3 = x * (q + 1) := by rw [← hq]; ring
    rw [hq, Nat.add_sub_cancel, e3]
    nlinarith
  have a5 : 2 * x ^ 3 + Y ≤ 2 * Y := by omega
  have hx36 : x ^ 5 ≤ x ^ 6 := Nat.pow_le_pow_right hx1 (by norm_num)
  calc 2 * (2 * β + 6) * ((k - 1) * (n + 2) * (1 + β) + (k - 1) * (n + 1) + Y)
      ≤ 2 * (2 * x ^ 2) * (x ^ 3 * n + 2 * Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) (a3.trans (a4.trans (Nat.add_le_add_left a5 _)))
    _ = 4 * x ^ 5 * n + 8 * x ^ 2 * Y := by ring
    _ ≤ 4 * x ^ 6 * n + 8 * x ^ 2 * Y := by gcongr

/-- 4·(s + 8)⁶·2^s ≤ K_t. -/
theorem coeff_le_Ktop (s : ℕ) : 4 * (s + 8) ^ 6 * 2 ^ s ≤ Ktop s := by
  calc 4 * (s + 8) ^ 6 * 2 ^ s ≤ 2 ^ (6 * s + 20) * 2 ^ s := Nat.mul_le_mul_right _ (coeff_le s)
    _ = 2 ^ (6 * s + 20 + s) := by rw [← pow_add]
    _ ≤ 2 ^ (52 * s + 692) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Ktop s := Ktop_lower s

/-- 16·(β + 2)·(Δ + 4)·2^s ≤ K_t, with β = `betaOf s`, for every Δ ≤ 2^β. -/
theorem size_coeff_le_Ktop {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) : 16 * (2 + betaOf s) * (Δ + 4) * 2 ^ s ≤ Ktop s := by
  obtain ⟨β, hβ⟩ : ∃ β, β = betaOf s := ⟨_, rfl⟩
  have h0 := two_pow_betaOf_le_Ktop s
  rw [← hβ] at hΔ h0 ⊢
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h3 : 2 + β ≤ 2 * 2 ^ β := by omega
  have h4 : Δ + 4 ≤ 8 * 2 ^ β := by omega
  calc 16 * (2 + β) * (Δ + 4) * 2 ^ s ≤ 16 * (2 * 2 ^ β) * (8 * 2 ^ β) * 2 ^ s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h4)
    _ = 2 ^ (8 + β + β + s) := by rw [pow_add, pow_add, pow_add]; norm_num; ring
    _ ≤ 2 ^ (4 * β + 10 * s + 1000) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Ktop s := h0

/-! ### What the invariant needs of the fixed numbers -/

/-- 25·K_t² ≤ 2·Z. -/
theorem Zof_ge (s : ℕ) : 25 * Kseq (depthOf s) ^ 2 ≤ 2 * Zof s := by
  have h : 100 * Kseq (depthOf s) ^ 2 ≤ Ytop s := hundred_Ktop_sq_le s
  have h2 : Ytop s ≤ Ytop s ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold Zof
  omega

/-- Z ≤ Qm. -/
theorem Zof_le_Qmof (k s n : ℕ) : Zof s ≤ Qmof k s n := by
  unfold Qmof
  omega

/-- K_t² + 8·(s + 8)²·Y ≤ Z. -/
theorem rest_le_Zof (s : ℕ) : Ktop s ^ 2 + 8 * (s + 8) ^ 2 * Ytop s ≤ Zof s := by
  have h1 := cube_le_Ytop s
  have h2 := hundred_Ktop_sq_le s
  have h0 : (s + 8) ^ 2 ≤ (s + 8) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : (8 * (s + 8) ^ 2 + 1) * Ytop s ≤ Ytop s * Ytop s := Nat.mul_le_mul_right _ (by omega)
  have e1 : (8 * (s + 8) ^ 2 + 1) * Ytop s = 8 * (s + 8) ^ 2 * Ytop s + Ytop s := by ring
  have e2 : Ytop s * Ytop s = Ytop s ^ 2 := by ring
  unfold Zof
  omega

/-- Qm + 1 ≤ 2^L. -/
theorem Qmof_lt {k s n : ℕ} (hk : k ≤ s) (hY : Ytop s ^ 6 ≤ n) : Qmof k s n + 1 ≤ 2 ^ Lof s n := by
  have h1 := Ubof_le hk n
  have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h3 := Ytop_sq_le hY
  have h4 := rest_le_Zof s
  have h5 : Xof s n ≤ n + 1 := Nat.add_le_add_right (Nat.div_le_self _ _) 1
  have a1 := coeff_le s
  have a2 : 4 * (s + 8) ^ 6 * n ≤ 2 ^ (6 * s + 20) * 2 ^ Nat.size n := Nat.mul_le_mul a1 h2.le
  have a3 : 4 * 2 ^ Nat.size n ≤ 2 ^ (6 * s + 20) * 2 ^ Nat.size n :=
    Nat.mul_le_mul_right _ (le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have e2 : 2 ^ Lof s n = 16 * (2 ^ (6 * s + 20) * 2 ^ Nat.size n) := by
    rw [Lof, show 6 * s + 24 + Nat.size n = 4 + (6 * s + 20 + Nat.size n) by ring, pow_add, pow_add]; norm_num
  rw [e2]
  unfold Qmof
  unfold Zof at h4 ⊢
  omega

/-- n < 2^L. -/
theorem lt_two_pow_Lof (s n : ℕ) : n < 2 ^ Lof s n :=
  lt_of_lt_of_le (Nat.lt_size_self n) (Nat.pow_le_pow_right (by norm_num) (by unfold Lof; omega))

/-- The polynomial factor in the length of an instance is at most 2^(2L). -/
theorem poly_le {k s n : ℕ} (hk : k ≤ s) (hY : Ytop s ^ 6 ≤ n) :
    Kseq (depthOf s) * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10 ≤ 2 ^ (2 * Lof s n) := by
  have hK : Kseq (depthOf s) = Ktop s := rfl
  rw [hK]
  have h1 := Qmof_lt hk hY
  have h2 := hundred_Ktop_pow_four_le s
  have h3 := hundred_Ytop_le hY
  have h4 := lt_two_pow_Lof s n
  have h5 : Ktop s ≤ Ktop s ^ 4 := Nat.le_self_pow (by norm_num) _
  have h6 : 1 ≤ Ktop s ^ 4 := Nat.one_le_pow _ _ (one_le_Ktop s)
  have a1 : 51 * Ktop s ^ 4 + 14 * Ktop s + 14 ≤ 2 ^ Lof s n := by omega
  have a2 : Ktop s * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10
      ≤ (51 * Ktop s ^ 4 + 14 * Ktop s + 14) * (Qmof k s n + 1) := by
    unfold Wmof
    nlinarith [Nat.zero_le (Ktop s ^ 4), Nat.zero_le (Ktop s * Qmof k s n)]
  calc Ktop s * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10
      ≤ (51 * Ktop s ^ 4 + 14 * Ktop s + 14) * (Qmof k s n + 1) := a2
    _ ≤ 2 ^ Lof s n * 2 ^ Lof s n := Nat.mul_le_mul a1 h1
    _ = 2 ^ (2 * Lof s n) := by rw [← pow_add]; congr 1; ring

/-! ### All overheads together are below n/2^s -/

/-- L ≤ 2·Y·(⌊√n⌋+1). -/
theorem Lof_le (s n : ℕ) : Lof s n ≤ 2 * Ytop s * (Nat.sqrt n + 1) := by
  have h1 := size_le_sqrt n
  have h2 := lin_lt_Ytop s
  have h3 : 2 * (Nat.sqrt n + 1) ≤ Ytop s * (Nat.sqrt n + 1) := Nat.mul_le_mul_right _ (by omega)
  have h4 : Ytop s ≤ Ytop s * (Nat.sqrt n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e : 2 * Ytop s * (Nat.sqrt n + 1) = 2 * (Ytop s * (Nat.sqrt n + 1)) := by ring
  rw [e]
  unfold Lof
  omega

/-- The sum of all overheads: 5·Z + L·(2·K_t² + 2) + 1 + K_t ≤ ⌊n/2^s⌋. -/
theorem small {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) :
    5 * Zof s + Lof s n * (2 * Ktop s ^ 2 + 2) + 1 + Ktop s ≤ n / 2 ^ s := by
  refine overhead_le_div (c := 68) (a := 2)
    (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 7 ≤ 500))) hY ?_
  have h1 := Lof_le s n
  have h2 := hundred_Ktop_sq_le s
  have h3 : 1 ≤ Ktop s ^ 2 := Nat.one_le_pow _ _ (one_le_Ktop s)
  have h4 : Ktop s ≤ Ktop s ^ 2 := Nat.le_self_pow (by norm_num) _
  have h5 : 2 * Ktop s ^ 2 + 2 ≤ Ytop s := by omega
  have h6 : Lof s n * (2 * Ktop s ^ 2 + 2) ≤ 2 * Ytop s * (Nat.sqrt n + 1) * Ytop s := Nat.mul_le_mul h1 h5
  have e6 : 2 * Ytop s * (Nat.sqrt n + 1) * Ytop s = 2 * (Ytop s ^ 2 * (Nat.sqrt n + 1)) := by ring
  have h7' : Ytop s ^ 2 ≤ Ytop s ^ 2 * (Nat.sqrt n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : Ytop s ≤ Ytop s ^ 2 * (Nat.sqrt n + 1) := le_trans (Nat.le_self_pow (by norm_num) _) h7'
  have e8 : 68 * Ytop s ^ 2 * (Nat.sqrt n + 1) = 68 * (Ytop s ^ 2 * (Nat.sqrt n + 1)) := by ring
  rw [e8]
  unfold Zof
  omega

/-- One inequality that dominates the exponents of all budgets. -/
theorem exponents_le {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) :
    4 * (Xof s n + Zof s) + (Lof s n * (2 * Kseq (depthOf s) ^ 2) + (Xof s n + Zof s) + 2 * Lof s n + 1) + Kseq (depthOf s)
      ≤ 8 * Xof s n := by
  have h : 5 * Zof s + Lof s n * (2 * Kseq (depthOf s) ^ 2 + 2) + 1 + Kseq (depthOf s) ≤ n / 2 ^ s := small hY
  have e : Lof s n * (2 * Kseq (depthOf s) ^ 2 + 2) = Lof s n * (2 * Kseq (depthOf s) ^ 2) + 2 * Lof s n := by ring
  rw [e] at h
  unfold Xof
  omega

/-- 65·Y ≤ X. -/
theorem Ytop_le_Xof {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : 65 * Ytop s ≤ Xof s n := by
  have h := small hY
  have h2 : 65 * Ytop s ≤ Ytop s * Ytop s := Nat.mul_le_mul_right _ (le_trans (by norm_num) (Ytop_ge s))
  have e : Ytop s * Ytop s = Ytop s ^ 2 := by ring
  unfold Zof at h
  unfold Xof
  omega

/-! ### The invariant at the top -/

/-- 4·g·Pb ≤ K_t·X, for g = `gtop s`. -/
theorem four_mul_Pbof_le {Δ s n : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) : 4 * (gtop s * Pbof Δ s n) ≤ Ktop s * Xof s n := by
  have hg := gtop_pos s
  have h1 : gtop s * Mark.qv (gtop s) n ≤ n + gtop s := by
    have := Nat.mul_div_le (n + gtop s - 1) (gtop s)
    unfold Mark.qv
    omega
  have h2 := size_coeff_le_Ktop hΔ
  have h3 : n ≤ 2 ^ s * Xof s n := (lt_two_pow_mul_div_add_one n s).le
  have h4 := Ytop_le_Xof hY
  have h5 := gtop_le_Ytop s
  obtain ⟨c, hc⟩ : ∃ c, c = 8 * (2 + betaOf s) * (Δ + 4) := ⟨_, rfl⟩
  have h2' : 2 * c * 2 ^ s ≤ Ktop s := by rw [hc]; calc _ = 16 * (2 + betaOf s) * (Δ + 4) * 2 ^ s := by ring
    _ ≤ Ktop s := h2
  have h6 : 2 * c ≤ Ktop s := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h2'
  have e : 4 * (gtop s * Pbof Δ s n) = c * (gtop s * Mark.qv (gtop s) n) := by
    rw [hc]; unfold Pbof Pb; ring
  have hX : Xof s n = n / 2 ^ s + 1 := rfl
  rw [e]
  have b1 : c * (gtop s * Mark.qv (gtop s) n) ≤ c * (2 ^ s * Xof s n) + c * gtop s := by
    calc c * (gtop s * Mark.qv (gtop s) n) ≤ c * (n + gtop s) := Nat.mul_le_mul_left _ h1
      _ ≤ c * (2 ^ s * Xof s n + gtop s) := Nat.mul_le_mul_left _ (by omega)
      _ = c * (2 ^ s * Xof s n) + c * gtop s := by ring
  have b2 : 2 * (c * (2 ^ s * Xof s n)) ≤ Ktop s * Xof s n := by
    calc 2 * (c * (2 ^ s * Xof s n)) = 2 * c * 2 ^ s * Xof s n := by ring
      _ ≤ Ktop s * Xof s n := Nat.mul_le_mul_right _ h2'
  have b3 : 2 * (c * gtop s) ≤ Ktop s * Xof s n := by
    calc 2 * (c * gtop s) = 2 * c * gtop s := by ring
      _ ≤ Ktop s * Xof s n := Nat.mul_le_mul h6 (by omega)
  omega

/-- The invariant holds at the top level, for the instance that the rebalancing makes of a network
of marks. -/
theorem inv_at_top {k Δ s n : ℕ} (hk : k ≤ s) (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) :
    Inv (depthOf s) (Xof s n) (Zof s) (Qmof k s n) (Wmof k s n) (Lof s n) (depthOf s)
      (lamG (Kseq (depthOf s)) (3 * Kseq (depthOf s) ^ 8) (Ubof k s n) (Pbof Δ s n))
      (Pbof Δ s n * (2 * (3 * Kseq (depthOf s) ^ 8) / Kseq (depthOf s))) 1 := by
  have hK : Kseq (depthOf s) = Ktop s := rfl
  rw [hK, ← gtop_eq]
  have k1 := one_le_Ktop s
  have hP := four_mul_Pbof_le hΔ hY
  have q1 := four_sq_mul_lamG_le (Ub := Ubof k s n) k1 hP
  have q2 := rest_le_Zof s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hK]
    refine inv_top k1 hP (Ubof_le hk n) (lt_two_pow_mul_div_add_one n s).le ?_ q2
    have h := decay (C := 8) (by norm_num) s
    calc 8963 ^ depthOf s * (2 * (4 * (s + 8) ^ 6) * 2 ^ s) = 8963 ^ depthOf s * (8 * (s + 8) ^ 6 * 2 ^ s) := by ring
      _ ≤ 10000 ^ depthOf s := h
  · rw [hK]
    unfold Qmof
    omega
  · rw [hK]
    have b3 : Pbof Δ s n * (2 * gtop s / Ktop s) ≤ Qmof k s n := by
      have := mul_div_le k1 hP
      unfold Qmof
      omega
    have b4 := Nat.mul_le_mul_right (Ktop s ^ 3) b3
    unfold Wmof
    nlinarith
  · rw [one_mul]

/-! ### The budgets at the top, and the rounds of the walk -/

section budgets

variable {k Δ s n F : ℕ}

/-- A power of two with exponent at most 8·X is at most the length F of the pad, if 2^(8·X) ≤ F. -/
theorem two_pow_le_of_le {e : ℕ} (hF : 2 ^ (8 * Xof s n) ≤ F) (he : e ≤ 8 * Xof s n) : 2 ^ e ≤ F :=
  le_trans (Nat.pow_le_pow_right (by norm_num) he) hF

/-- Field col of NetFits: the colourings at the top. -/
theorem top_col (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    Kseq (depthOf s) ^ (3 * Kseq (depthOf s) ^ 8) ≤ F := by
  have h1 : Ktop s ^ gtop s ≤ 2 ^ (gtop s * gtop s) := pow_le_two_pow_sq (Ktop_le_gtop s)
  have e : gtop s * gtop s = Ytop s := by rw [Ytop_eq_sq]; ring
  rw [e] at h1
  have h2 := Ytop_le_Xof hY
  exact le_trans h1 (two_pow_le_of_le hF (by omega))

/-- Field st of NetFits: the states of a class at the top. -/
theorem top_st (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 ^ (Pbof Δ s n * (2 * (3 * Kseq (depthOf s) ^ 8) / Kseq (depthOf s))) ≤ F := by
  have h1 : Pbof Δ s n * (2 * gtop s / Ktop s) ≤ Xof s n := mul_div_le (one_le_Ktop s) (four_mul_Pbof_le hΔ hY)
  exact two_pow_le_of_le hF (le_trans h1 (by omega))

/-- Field lab of NetFits: the labels inside a class at the top. -/
theorem top_lab (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) : 2 ^ Pbof Δ s n ≤ F := by
  have h1 : Pbof Δ s n ≤ Xof s n := size_le (gtop_pos s) (Ktop_le_gtop s) (four_mul_Pbof_le hΔ hY)
  exact two_pow_le_of_le hF (le_trans h1 (by omega))

/-- Field tab of NetFits: the indices of a table at the top. -/
theorem top_tab (hk : k ≤ s) (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 ^ ((Kseq (depthOf s) - 1) * lamG (Kseq (depthOf s)) (3 * Kseq (depthOf s) ^ 8) (Ubof k s n) (Pbof Δ s n)) ≤ F := by
  have hU : Ubof k s n ≤ Ktop s * Xof s n + 8 * (s + 8) ^ 2 * Ytop s := by
    refine le_trans (Ubof_le hk n) (Nat.add_le_add_right ?_ _)
    calc 4 * (s + 8) ^ 6 * n ≤ 4 * (s + 8) ^ 6 * (2 ^ s * Xof s n) :=
          Nat.mul_le_mul_left _ (lt_two_pow_mul_div_add_one n s).le
      _ = 4 * (s + 8) ^ 6 * 2 ^ s * Xof s n := by ring
      _ ≤ Ktop s * Xof s n := Nat.mul_le_mul_right _ (coeff_le_Ktop s)
  have h1 : (Ktop s - 1) * lamG (Ktop s) (gtop s) (Ubof k s n) (Pbof Δ s n) ≤ Ktop s + 2 * Xof s n + 8 * (s + 8) ^ 2 * Ytop s :=
    mul_lamG_le (one_le_Ktop s) (four_mul_Pbof_le hΔ hY) hU
  have h2 := small hY
  have h3 := rest_le_Zof s
  have hX : Xof s n = n / 2 ^ s + 1 := rfl
  exact two_pow_le_of_le hF (le_trans h1 (by omega))

/-- Conjunct 3 of StAW: the rounds of the walk. -/
theorem top_rounds (hs : s0K k ≤ s) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j) ≤ F + 1 := by
  have h1 : ∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j ≤ 2 ^ Xof s n :=
    sum_choose_le_two_pow hs n
  have h0 : 1 ≤ Xof s n := Nat.le_add_left 1 _
  have h2 : 2 ^ (Xof s n + 1) ≤ F := two_pow_le_of_le hF (by omega)
  rw [pow_succ] at h2
  omega

end budgets

/-! ### The layers -/

/-- Field last of MarkFits: after `layersOf s` divisions, each of which keeps at most two thirds of
the clauses, fewer than n + 2 clauses are left. -/
theorem layers_last {Δ s n : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (hn : 6 ≤ n) :
    2 ^ layersOf s * (Δ * n) + 5 * 3 ^ layersOf s ≤ 3 ^ layersOf s * (n + 2) := by
  obtain ⟨h, hh⟩ : ∃ h, h = betaOf s + 2 := ⟨_, rfl⟩
  have e : layersOf s = 2 * h := by rw [hh, layersOf]; ring
  have e2 : (2 : ℕ) ^ (2 * h) = 4 ^ h := by rw [pow_mul]; norm_num
  have e3 : (3 : ℕ) ^ (2 * h) = 9 ^ h := by rw [pow_mul]; norm_num
  have h2 : 2 * Δ ≤ 2 ^ h := by
    rw [hh, pow_add]; omega
  have h3 : 4 ^ h * 2 ^ h ≤ 9 ^ h := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) h
  have h4 : 2 * (4 ^ h * Δ) ≤ 9 ^ h := by
    calc 2 * (4 ^ h * Δ) = 4 ^ h * (2 * Δ) := by ring
      _ ≤ 4 ^ h * 2 ^ h := Nat.mul_le_mul_left _ h2
      _ ≤ 9 ^ h := h3
  rw [e, e2, e3]
  obtain ⟨A, hA⟩ : ∃ A, A = 9 ^ h := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = 4 ^ h * Δ := ⟨_, rfl⟩
  have e4 : 4 ^ h * (Δ * n) = D * n := by rw [hD]; ring
  rw [e4, ← hA]
  rw [← hD, ← hA] at h4
  nlinarith

/-- Field m_le of MarkFits: the number of clauses is at most 2^β·(n + 1). -/
theorem clauses_le {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (n : ℕ) : Δ * n ≤ 2 ^ betaOf s * (n + 1) :=
  Nat.mul_le_mul hΔ (Nat.le_succ n)

end PaddedDescent.F.Arith
