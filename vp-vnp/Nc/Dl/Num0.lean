/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Does

/-!
# Inequalities between the numbers of one cut
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

/-- The numbers of one cut. `m` bounds all polylogarithmic factors and constants, `X` everything that depends on `K`
only (and on `U0`). -/
structure CutNums (v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ) : Prop where
  v_pos : 1 ≤ v
  m_ge : 10000 ≤ m
  m_le : m ≤ v
  k_pos : 2 ≤ k
  kK : k ≤ K
  vK : v ^ 300 ≤ K
  KT : K * T ≤ τ * m
  ℓeq : ℓ = s / K + 1
  ub_pos : 1 ≤ ub
  ub_le : ub ≤ T + 1
  lhub : lh * ub ≤ m * T
  Lc_le : Lc + 1 ≤ m
  c_le : 4 * c + 8 ≤ m
  K_X : K ≤ X
  X_ge : 1 ≤ X
  ιb_le : ιb * k ≤ m * K
  ιbX : ιb ≤ X
  bd_le : bd * ub * v ^ 300 ≤ τ * m ^ 2
  ev_le : ev * ub * k ≤ τ * m ^ 2
  mm_le : mm ≤ k * m
  mmX : mm ≤ X
  small : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ

namespace CutNums

variable {v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ} (h : CutNums v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm)

include h

theorem m_pos : 1 ≤ m := le_trans (by norm_num) h.m_ge

theorem Xpow {a b : ℕ} (hab : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right h.X_ge hab

theorem mpow {a b : ℕ} (hab : a ≤ b) : m ^ a ≤ m ^ b := Nat.pow_le_pow_right h.m_pos hab

/-- Small things are small. -/
theorem X6 : X ^ 6 * m ^ 20 ≤ τ / v ^ 300 := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos h.v_pos)]
  exact h.small

theorem X6' : X ^ 6 * m ^ 20 ≤ τ / v ^ 256 :=
  h.X6.trans (Nat.div_le_div_left (Nat.pow_le_pow_right h.v_pos (by norm_num)) (Nat.pow_pos h.v_pos))

theorem X6t : X ^ 6 * m ^ 20 ≤ τ := h.X6.trans (Nat.div_le_self _ _)

theorem Xm_le {a b : ℕ} (ha : a ≤ 6) (hb : b ≤ 20) : X ^ a * m ^ b ≤ X ^ 6 * m ^ 20 :=
  Nat.mul_le_mul (h.Xpow ha) (h.mpow hb)

/-- The boundary of a group, in bits. -/
theorem bdub : bd * ub ≤ τ / v ^ 256 := by
  have hm := h.m_pos
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos h.v_pos)]
  have h1 : bd * ub * v ^ 300 ≤ τ * m ^ 5 := h.bd_le.trans (Nat.mul_le_mul_left _ (h.mpow (by norm_num)))
  have h2 : bd * ub * v ^ 256 * m ^ 5 ≤ τ * m ^ 5 := by
    calc bd * ub * v ^ 256 * m ^ 5 ≤ bd * ub * v ^ 256 * v ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.m_le 5)
      _ = bd * ub * v ^ 261 := by rw [Nat.mul_assoc, ← pow_add]
      _ ≤ bd * ub * v ^ 300 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h.v_pos (by norm_num))
      _ ≤ τ * m ^ 5 := h1
  exact Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hm)

/-- **Time of the pieces.** -/
theorem time {κ : ℕ} (hκ : κ ≤ m) : κ * (2 * (Lc + 1) * (T + ub + 2) + ιb * T + 1000 * (ev + ιb * lh) * (ub + Lc + 1) +
    X ^ 4 * 1000 * (Lc + 1)) ≤ τ * m ^ 10 / k := by
  have hm := h.m_pos
  have hk := h.k_pos
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hXk : ∀ a b, a ≤ 5 → b ≤ 20 → X ^ a * m ^ b * k ≤ τ := by
    intro a b ha hb
    calc X ^ a * m ^ b * k ≤ X ^ a * m ^ b * X := Nat.mul_le_mul_left _ (h.kK.trans h.K_X)
      _ = X ^ (a + 1) * m ^ b := by rw [pow_succ]; ring
      _ ≤ X ^ 6 * m ^ 20 := h.Xm_le (by omega) hb
      _ ≤ τ := h.X6t
  have hTk : T * k ≤ τ * m := by
    calc T * k ≤ T * K := Nat.mul_le_mul_left _ h.kK
      _ = K * T := Nat.mul_comm _ _
      _ ≤ τ * m := h.KT
  have A1 : 2 * (Lc + 1) * (T + ub + 2) * k ≤ τ * m ^ 3 := by
    have e1 : k ≤ τ := by
      have := hXk 0 0 (by norm_num) (by norm_num)
      simpa using this
    calc 2 * (Lc + 1) * (T + ub + 2) * k ≤ 2 * m * (T + (T + 1) + 2) * k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h.Lc_le) (by have := h.ub_le; omega))
      _ = 2 * m * (2 * (T * k) + 3 * k) := by ring
      _ ≤ 2 * m * (2 * (τ * m) + 3 * (τ * m)) := Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hTk)
          (Nat.mul_le_mul_left _ (e1.trans (Nat.le_mul_of_pos_right _ hm))))
      _ = τ * m ^ 2 * 10 := by ring
      _ ≤ τ * m ^ 2 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
      _ = τ * m ^ 3 := by ring
  have A2 : ιb * T * k ≤ τ * m ^ 3 := by
    calc ιb * T * k = ιb * k * T := by ring
      _ ≤ m * K * T := Nat.mul_le_mul_right _ h.ιb_le
      _ = m * (K * T) := by ring
      _ ≤ m * (τ * m) := Nat.mul_le_mul_left _ h.KT
      _ = τ * m ^ 2 := by ring
      _ ≤ τ * m ^ 3 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have hu : ub + m ≤ ub * (m * 2) := by
    have h1 : ub ≤ ub * m := Nat.le_mul_of_pos_right _ hm
    have h2 : m ≤ ub * m := Nat.le_mul_of_pos_left _ h.ub_pos
    have e : ub * (m * 2) = ub * m + ub * m := by ring
    omega
  have hev : ev * k * (ub + m) ≤ τ * m ^ 6 := by
    calc ev * k * (ub + m) ≤ ev * k * (ub * (m * 2)) := Nat.mul_le_mul_left _ hu
      _ = ev * ub * k * (m * 2) := by ring
      _ ≤ τ * m ^ 2 * (m * m) := Nat.mul_le_mul h.ev_le (Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge))
      _ = τ * m ^ 4 := by ring
      _ ≤ τ * m ^ 6 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have hιb : ιb * lh * k * (ub + m) ≤ τ * m ^ 6 := by
    calc ιb * lh * k * (ub + m) ≤ ιb * lh * k * (ub * (m * 2)) := Nat.mul_le_mul_left _ hu
      _ = ιb * k * (lh * ub) * (m * 2) := by ring
      _ ≤ m * K * (m * T) * (m * m) :=
          Nat.mul_le_mul (Nat.mul_le_mul h.ιb_le h.lhub) (Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge))
      _ = m ^ 4 * (K * T) := by ring
      _ ≤ m ^ 4 * (τ * m) := Nat.mul_le_mul_left _ h.KT
      _ = τ * m ^ 5 := by ring
      _ ≤ τ * m ^ 6 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have A3 : 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ τ * m ^ 7 := by
    have hL := h.Lc_le
    calc 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ 1000 * (ev + ιb * lh) * (ub + m) * k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 1000 * (ev * k * (ub + m) + ιb * lh * k * (ub + m)) := by ring
      _ ≤ 1000 * (τ * m ^ 6 + τ * m ^ 6) := Nat.mul_le_mul_left _ (Nat.add_le_add hev hιb)
      _ = τ * m ^ 6 * 2000 := by ring
      _ ≤ τ * m ^ 6 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
      _ = τ * m ^ 7 := by ring
  have A4 : X ^ 4 * 1000 * (Lc + 1) * k ≤ τ := by
    calc X ^ 4 * 1000 * (Lc + 1) * k ≤ X ^ 4 * m * m * k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)) h.Lc_le)
      _ = X ^ 4 * m ^ 2 * k := by ring
      _ ≤ τ := hXk 4 2 (by norm_num) (by norm_num)
  calc κ * (2 * (Lc + 1) * (T + ub + 2) + ιb * T + 1000 * (ev + ιb * lh) * (ub + Lc + 1) + X ^ 4 * 1000 * (Lc + 1)) * k
      = κ * (2 * (Lc + 1) * (T + ub + 2) * k + ιb * T * k + 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k +
        X ^ 4 * 1000 * (Lc + 1) * k) := by ring
    _ ≤ m * (τ * m ^ 3 + τ * m ^ 3 + τ * m ^ 7 + τ) := Nat.mul_le_mul hκ
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add A1 A2) A3) A4)
    _ ≤ m * (τ * m ^ 7 + τ * m ^ 7 + τ * m ^ 7 + τ * m ^ 7) := by
        refine Nat.mul_le_mul_left _ ?_
        have e1 : τ * m ^ 3 ≤ τ * m ^ 7 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
        have e2 : τ ≤ τ * m ^ 7 := Nat.le_mul_of_pos_right _ (Nat.pow_pos hm)
        omega
    _ = τ * m ^ 8 * 4 := by ring
    _ ≤ τ * m ^ 8 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
    _ = τ * m ^ 9 := by ring
    _ ≤ τ * m ^ 10 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))

/-- **Size of the pieces.** -/
theorem size : X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)) ≤ (s / k + τ / v ^ 256) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have B1 : ιb * ℓ ≤ m * (s / k) + m + X := by
    have h1 : ιb * (s / K) ≤ m * (s / k) + m := by
      have h2 : ιb * (s / K) * k ≤ m * s := by
        calc ιb * (s / K) * k = ιb * k * (s / K) := by ring
          _ ≤ m * K * (s / K) := Nat.mul_le_mul_right _ h.ιb_le
          _ = m * (K * (s / K)) := by ring
          _ ≤ m * s := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
      have h3 : s ≤ (s / k + 1) * k := by
        have := Nat.div_add_mod s k
        have h4 := Nat.mod_lt s (show 0 < k by omega)
        rw [add_mul, one_mul, Nat.mul_comm (s / k)]
        omega
      have h4 : ιb * (s / K) * k ≤ (m * (s / k) + m) * k := by
        calc ιb * (s / K) * k ≤ m * s := h2
          _ ≤ m * ((s / k + 1) * k) := Nat.mul_le_mul_left _ h3
          _ = (m * (s / k) + m) * k := by ring
      exact Nat.le_of_mul_le_mul_right h4 (by omega)
    have h2 := h.ιbX
    rw [h.ℓeq, Nat.mul_add, Nat.mul_one]
    omega
  have hX : 1 ≤ X := h.X_ge
  have S1 : X + 1 + 200 * X ^ 3 * Lc + (m + X) * m ≤ τ / v ^ 256 := by
    refine le_trans ?_ h.X6'
    have hL := h.Lc_le
    have e1 : X ≤ X ^ 3 * m ^ 2 := by
      calc X = X ^ 1 * 1 := by rw [pow_one, mul_one]
        _ ≤ X ^ 3 * m ^ 2 := Nat.mul_le_mul (h.Xpow (by norm_num)) (Nat.pow_pos hm)
    have e2 : 1 ≤ X ^ 3 * m ^ 2 := Nat.mul_pos (Nat.pow_pos hX) (Nat.pow_pos hm)
    have e3 : 200 * X ^ 3 * Lc ≤ X ^ 3 * m ^ 2 := by
      calc 200 * X ^ 3 * Lc ≤ m * X ^ 3 * m :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (le_trans (by norm_num) h.m_ge)) (by omega)
        _ = X ^ 3 * m ^ 2 := by ring
    have e4 : m * m ≤ X ^ 3 * m ^ 2 := by
      calc m * m = 1 * m ^ 2 := by ring
        _ ≤ X ^ 3 * m ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_pos hX)
    have e5 : X * m ≤ X ^ 3 * m ^ 2 := by
      calc X * m = X ^ 1 * m ^ 1 := by rw [pow_one, pow_one]
        _ ≤ X ^ 3 * m ^ 2 := Nat.mul_le_mul (h.Xpow (by norm_num)) (h.mpow (by norm_num))
    calc X + 1 + 200 * X ^ 3 * Lc + (m + X) * m = X + 1 + 200 * X ^ 3 * Lc + (m * m + X * m) := by ring
      _ ≤ X ^ 3 * m ^ 2 * 5 := by omega
      _ ≤ X ^ 3 * m ^ 2 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
      _ = X ^ 3 * m ^ 3 := by ring
      _ ≤ X ^ 6 * m ^ 20 := h.Xm_le (by norm_num) (by norm_num)
  have S2 : bd * (4 * ub) ≤ 4 * (τ / v ^ 256) := by
    have := h.bdub
    calc bd * (4 * ub) = 4 * (bd * ub) := by ring
      _ ≤ 4 * (τ / v ^ 256) := Nat.mul_le_mul_left _ this
  have S3 : ιb * ℓ * (4 * c + 2) ≤ m ^ 2 * (s / k) + (m + X) * m := by
    calc ιb * ℓ * (4 * c + 2) ≤ (m * (s / k) + m + X) * m := Nat.mul_le_mul B1 (by have := h.c_le; omega)
      _ = m ^ 2 * (s / k) + (m + X) * m := by ring
  have hm10 : m ^ 2 ≤ m ^ 10 := h.mpow (by norm_num)
  have h5 : 5 ≤ m ^ 10 := le_trans (le_trans (by norm_num) h.m_ge) (Nat.le_self_pow (by norm_num) m)
  calc X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)) ≤ m ^ 2 * (s / k) + 5 * (τ / v ^ 256) := by omega
    _ ≤ m ^ 10 * (s / k) + m ^ 10 * (τ / v ^ 256) := Nat.add_le_add (Nat.mul_le_mul_right _ hm10) (Nat.mul_le_mul_right _ h5)
    _ = (s / k + τ / v ^ 256) * m ^ 10 := by ring

/-- **Time of the dealing program.** -/
theorem deal : dealB Lc X K mm ub (mm * bd) (4 * (X * X) + 10 * X) s ≤ (s + τ * k / v ^ 256) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have hX : 1 ≤ X := h.X_ge
  have hL := h.Lc_le
  have hm1 := h.m_ge
  -- the units of the boundaries
  have D1 : mm * bd * ((ub + 1) * (60 * Lc + 100)) ≤ τ * k / v ^ 256 * m ^ 3 := by
    have h1 : mm * (bd * ub) ≤ m * (τ * k / v ^ 256) := by
      calc mm * (bd * ub) ≤ k * m * (τ / v ^ 256) := Nat.mul_le_mul h.mm_le h.bdub
        _ = m * (k * (τ / v ^ 256)) := by ring
        _ ≤ m * (τ * k / v ^ 256) := Nat.mul_le_mul_left _ (by
            rw [Nat.mul_comm τ k]
            exact Nat.mul_div_le_mul_div_assoc _ _ _)
    calc mm * bd * ((ub + 1) * (60 * Lc + 100)) ≤ mm * bd * ((ub + ub) * (100 * m)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.add_le_add_left h.ub_pos _) (by omega))
      _ = mm * (bd * ub) * (200 * m) := by ring
      _ ≤ m * (τ * k / v ^ 256) * (m * m) := Nat.mul_le_mul h1 (Nat.mul_le_mul_right _ (le_trans (by norm_num) hm1))
      _ = τ * k / v ^ 256 * m ^ 3 := by ring
  -- small things
  have D2 : (K * (60 * Lc + 100) + K * (60 * Lc + 130) + (4 * (X * X) + 10 * X) * (stepB Lc X + 30) + X * (90 * Lc + 230) +
      mm * (tmB' Lc X + 60) + 300) ≤ τ * k / v ^ 256 := by
    have hsm : X ^ 4 * m ^ 4 ≤ τ * k / v ^ 256 := by
      refine (h.Xm_le (by norm_num) (by norm_num)).trans (h.X6'.trans ?_)
      exact Nat.div_le_div_right (Nat.le_mul_of_pos_right _ (by omega))
    refine le_trans ?_ hsm
    have hK := h.K_X
    have x1 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
    have x2 : X ^ 2 ≤ X ^ 4 := h.Xpow (by norm_num)
    have x3 : X ^ 3 ≤ X ^ 4 := h.Xpow (by norm_num)
    have L1 : 60 * Lc + 100 ≤ 100 * m := by omega
    have f1 : K * (60 * Lc + 100) ≤ X ^ 4 * (100 * m) := Nat.mul_le_mul (hK.trans x1) L1
    have f2 : K * (60 * Lc + 130) ≤ X ^ 4 * (130 * m) := Nat.mul_le_mul (hK.trans x1) (by omega)
    have st : stepB Lc X + 30 ≤ X * (1000 * m) := by
      have e1 : 60 * Lc ≤ X * (60 * m) := by
        calc 60 * Lc ≤ 1 * (60 * m) := by omega
          _ ≤ X * (60 * m) := Nat.mul_le_mul_right _ hX
      have e2 : 20 * X ≤ X * (20 * m) := by nlinarith
      have e3 : X * (4 * (60 * Lc + 80)) ≤ X * (320 * m) := Nat.mul_le_mul_left _ (by omega)
      have e4 : 180 * Lc ≤ X * (180 * m) := by
        calc 180 * Lc ≤ 1 * (180 * m) := by omega
          _ ≤ X * (180 * m) := Nat.mul_le_mul_right _ hX
      have e5 : 230 ≤ X * (230 * m) := by
        calc 230 ≤ 1 * (230 * m) := by omega
          _ ≤ X * (230 * m) := Nat.mul_le_mul_right _ hX
      have e6 : X * (1000 * m) = X * (60 * m) + X * (20 * m) + X * (320 * m) + X * (180 * m) + X * (230 * m) + X * (190 * m) := by
        ring
      unfold stepB
      omega
    have f3 : (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ X ^ 4 * (14000 * m) := by
      have e1 : 4 * (X * X) + 10 * X ≤ 14 * X ^ 2 := by nlinarith
      calc (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ 14 * X ^ 2 * (X * (1000 * m)) := Nat.mul_le_mul e1 st
        _ = X ^ 3 * (14000 * m) := by ring
        _ ≤ X ^ 4 * (14000 * m) := Nat.mul_le_mul_right _ x3
    have f4 : X * (90 * Lc + 230) ≤ X ^ 4 * (230 * m) := Nat.mul_le_mul x1 (by omega)
    have tb : tmB' Lc X + 60 ≤ X ^ 3 * (20000 * m) := by
      have y1 : X ^ 2 ≤ X ^ 3 := h.Xpow (by norm_num)
      have y2 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
      have y3 : 1 ≤ X ^ 3 := Nat.pow_pos hX
      have g1 : X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) ≤ X ^ 3 * (3000 * m) := by
        calc X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000)
            ≤ X * (3 * (X * (150 * m)) + X * (360 * m) + X * (62 * m) + X * (2000 * m)) := by
              refine Nat.mul_le_mul_left _ ?_
              have e1 : 3 * (X * (30 * Lc + 150)) ≤ 3 * (X * (150 * m)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
              have e2 : 360 * Lc ≤ X * (360 * m) := by
                calc 360 * Lc ≤ 1 * (360 * m) := by omega
                  _ ≤ X * (360 * m) := Nat.mul_le_mul_right _ hX
              have e3 : 62 * X ≤ X * (62 * m) := by nlinarith
              have e4 : 2000 ≤ X * (2000 * m) := by
                calc 2000 ≤ 1 * (2000 * m) := by omega
                  _ ≤ X * (2000 * m) := Nat.mul_le_mul_right _ hX
              omega
          _ = X ^ 2 * (2872 * m) := by ring
          _ ≤ X ^ 3 * (3000 * m) := Nat.mul_le_mul y1 (by omega)
      have g2 : X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) ≤ X ^ 3 * (4000 * m) := by
        calc X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500)
            ≤ X * (X * (X * (700 * m) + X * (120 * m)) + X * (X * (150 * m)) + X * (X * (300 * m)) + X * (X * (1500 * m))) := by
              refine Nat.mul_le_mul_left _ ?_
              have e0 : 1 ≤ X * X := Nat.mul_pos hX hX
              have e1 : X * (X * (270 * Lc + 700) + 120) ≤ X * (X * (700 * m) + X * (120 * m)) := by
                refine Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) ?_)
                calc 120 ≤ 1 * (120 * m) := by omega
                  _ ≤ X * (120 * m) := Nat.mul_le_mul_right _ hX
              have e2 : X * (30 * Lc + 150) ≤ X * (X * (150 * m)) := Nat.mul_le_mul_left _ (by
                calc 30 * Lc + 150 ≤ 1 * (150 * m) := by omega
                  _ ≤ X * (150 * m) := Nat.mul_le_mul_right _ hX)
              have e3 : 300 * Lc ≤ X * (X * (300 * m)) := by
                calc 300 * Lc ≤ 1 * (300 * m) := by omega
                  _ ≤ X * X * (300 * m) := Nat.mul_le_mul_right _ e0
                  _ = X * (X * (300 * m)) := by ring
              have e4 : 1500 ≤ X * (X * (1500 * m)) := by
                calc 1500 ≤ 1 * (1500 * m) := by omega
                  _ ≤ X * X * (1500 * m) := Nat.mul_le_mul_right _ e0
                  _ = X * (X * (1500 * m)) := by ring
              linarith
          _ = X ^ 3 * (2770 * m) := by ring
          _ ≤ X ^ 3 * (4000 * m) := Nat.mul_le_mul_left _ (by omega)
      have g3 : X * (2000 * Lc + 5000) ≤ X ^ 3 * (5000 * m) := Nat.mul_le_mul y2 (by omega)
      have g4 : 1060 ≤ X ^ 3 * (1060 * m) := by
        calc 1060 ≤ 1 * (1060 * m) := by omega
          _ ≤ X ^ 3 * (1060 * m) := Nat.mul_le_mul_right _ y3
      have g5 : X ^ 3 * (20000 * m) = X ^ 3 * (3000 * m) + X ^ 3 * (4000 * m) + X ^ 3 * (5000 * m) + X ^ 3 * (1060 * m) +
          X ^ 3 * (6940 * m) := by ring
      unfold tmB'
      linarith
    have f5 : mm * (tmB' Lc X + 60) ≤ X ^ 4 * (20000 * m) := by
      calc mm * (tmB' Lc X + 60) ≤ X * (X ^ 3 * (20000 * m)) := Nat.mul_le_mul h.mmX tb
        _ = X ^ 4 * (20000 * m) := by ring
    have f6 : 300 ≤ X ^ 4 * (300 * m) := by
      calc 300 ≤ 1 * (300 * m) := by omega
        _ ≤ X ^ 4 * (300 * m) := Nat.mul_le_mul_right _ (Nat.pow_pos hX)
    have f7 : X ^ 4 * (100 * m) + X ^ 4 * (130 * m) + X ^ 4 * (14000 * m) + X ^ 4 * (230 * m) + X ^ 4 * (20000 * m) +
        X ^ 4 * (300 * m) = X ^ 4 * (34760 * m) := by ring
    have f8 : X ^ 4 * (34760 * m) ≤ X ^ 4 * m ^ 4 := by
      refine Nat.mul_le_mul_left _ ?_
      calc 34760 * m ≤ m * m * m * m := by nlinarith [Nat.mul_le_mul hm1 hm1, Nat.mul_pos hm hm]
        _ = m ^ 4 := by ring
    omega
  have D3 : 60 * s + s * (60 * Lc + 100) ≤ s * (200 * m) := by
    calc 60 * s + s * (60 * Lc + 100) = s * (60 * Lc + 160) := by ring
      _ ≤ s * (200 * m) := Nat.mul_le_mul_left _ (by omega)
  have e10 : s * (200 * m) ≤ s * m ^ 10 := Nat.mul_le_mul_left _ (by
    calc 200 * m ≤ m * m := Nat.mul_le_mul_right _ (le_trans (by norm_num) hm1)
      _ = m ^ 2 := by ring
      _ ≤ m ^ 10 := h.mpow (by norm_num))
  have e11 : τ * k / v ^ 256 * m ^ 3 + τ * k / v ^ 256 ≤ τ * k / v ^ 256 * m ^ 10 := by
    calc τ * k / v ^ 256 * m ^ 3 + τ * k / v ^ 256 ≤ τ * k / v ^ 256 * m ^ 3 + τ * k / v ^ 256 * m ^ 3 :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.pow_pos hm)) _
      _ = τ * k / v ^ 256 * m ^ 3 * 2 := by ring
      _ ≤ τ * k / v ^ 256 * m ^ 3 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) hm1)
      _ = τ * k / v ^ 256 * m ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have e12 : (s + K) * (60 * Lc + 100) = s * (60 * Lc + 100) + K * (60 * Lc + 100) := by ring
  have e13 : (s + τ * k / v ^ 256) * m ^ 10 = s * m ^ 10 + τ * k / v ^ 256 * m ^ 10 := by ring
  unfold dealB
  omega

end CutNums

end Nc.Dl
