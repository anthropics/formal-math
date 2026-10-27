/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Seq
public import PaddedDescent.F.ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The invariant of the descent through the levels

An instance at level j has K_j nodes, labels of at most Λ bits and entries of at most B bits, and
the work list has at most cnt members. This file
states four inequalities (`Inv`) between these numbers and a few numbers that stay fixed during the
descent, proves that one level preserves them,
and derives from them the exponents of all the budgets of one level. No programs occur here. It is
groundwork for a rate theorem on top of the Lean
proof in this development that 3-SAT is decided in time O(2^{δn}) for every δ > 0 (which follows
from Theorem 2 of the paper). -/

@[expose] public section

namespace PaddedDescent.F.Arith

open Groundwork.Prog (nRect)

/-- The four inequalities at level j. The numbers t (top level), X, Z, Qm, Wm, L stay fixed. With Q =
K_j²·Λ:
`geo`: Q ≤ (10000/8963)^j·X + Z; `crude`: Q ≤ Qm; `bits`: (B + 16·Qm)·K_j³ ≤ Wm; `count`:
cnt·2^(2·L·K_j²) ≤ 2^(2·L·K_t²). -/
structure Inv (t X Z Qm Wm L j lam B cnt : ℕ) : Prop where
  geo : 8963 ^ j * (Kseq j ^ 2 * lam) ≤ 10000 ^ j * X + 8963 ^ j * Z
  crude : Kseq j ^ 2 * lam ≤ Qm
  bits : B * Kseq j ^ 3 + 16 * Qm * Kseq j ^ 3 ≤ Wm
  count : cnt * 2 ^ (L * (2 * Kseq j ^ 2)) ≤ 2 ^ (L * (2 * Kseq t ^ 2))

/-- K_{j+1}² = g_j⁴. -/
theorem Kseq_succ_sq (j : ℕ) : Kseq (j + 1) ^ 2 = gseq j ^ 4 := by
  rw [Kseq_succ_eq_sq]; ring

/-- K_{j+1}³ = (g_j·g_j)³. -/
theorem Kseq_succ_cube (j : ℕ) : Kseq (j + 1) ^ 3 = (gseq j * gseq j) ^ 3 := by
  rw [Kseq_succ_eq_mul]

/-- K_i ≤ K_j for i ≤ j. -/
theorem Kseq_mono {i j : ℕ} (h : i ≤ j) : Kseq i ≤ Kseq j := Kseq_strictMono.monotone h

/-- 10000^(j+1) ≤ 8963^(j+1)·K_j. -/
theorem pow_succ_le_mul_Kseq (j : ℕ) : 10000 ^ (j + 1) ≤ 8963 ^ (j + 1) * Kseq j := by
  calc 10000 ^ (j + 1) = 10000 ^ j * 10000 := pow_succ _ _
    _ ≤ (8963 * 4) ^ j * (8963 * 256) := Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) j) (by norm_num)
    _ = 8963 ^ (j + 1) * (256 * 4 ^ j) := by rw [mul_pow]; ring
    _ ≤ 8963 ^ (j + 1) * Kseq j := Nat.mul_le_mul_left _ (Kseq_lower j)

/-- 10000^j ≤ 8963^j·K_j. -/
theorem pow_le_mul_Kseq (j : ℕ) : 10000 ^ j ≤ 8963 ^ j * Kseq j := by
  calc 10000 ^ j ≤ (8963 * 4) ^ j * 256 :=
        le_trans (Nat.pow_le_pow_left (by norm_num) j) (Nat.le_mul_of_pos_right _ (by norm_num))
    _ = 8963 ^ j * (256 * 4 ^ j) := by rw [mul_pow]; ring
    _ ≤ 8963 ^ j * Kseq j := Nat.mul_le_mul_left _ (Kseq_lower j)

variable {t X Z Qm Wm L j lam B cnt : ℕ}

/-- The arithmetic of `Inv.step`, line `geo`, with plain variables (a = 8963^j, b = 10000^j, q' =
K²Λ', q = g⁴Λ, G = g⁴). -/
theorem geo_step {a b q' q G X Z : ℕ} (O1 : 10000 * q' ≤ 8963 * q + 10000 * G) (hG : 10000 * G ≤ 1037 * Z)
    (h1 : a * 8963 * q ≤ b * 10000 * X + a * 8963 * Z) : a * q' ≤ b * X + a * Z := by
  have a1 := Nat.mul_le_mul_left a O1
  have a2 := Nat.mul_le_mul_left a hG
  nlinarith

/-- The arithmetic of `Inv.step`, line `bits`, with plain variables (K3 = K³, G6 = (g·g)³, G3 = g³,
q = g⁴Λ). -/
theorem bits_step {B B' K3 G6 G3 q Qm Wm : ℕ} (O2 : B' ≤ 6 * (G3 * B) + 8 * q) (O8a : 6 * G3 * K3 ≤ G6)
    (O8b : 24 * K3 ≤ 16 * G6) (hq : q ≤ Qm) (h3 : B * G6 + 16 * Qm * G6 ≤ Wm) :
    B' * K3 + 16 * Qm * K3 ≤ Wm := by
  have b1 : B' * K3 ≤ (6 * (G3 * B) + 8 * q) * K3 := Nat.mul_le_mul_right _ O2
  have b2 : 6 * G3 * K3 * B ≤ G6 * B := Nat.mul_le_mul_right _ O8a
  have b3 : 8 * q * K3 ≤ 8 * Qm * K3 := Nat.mul_le_mul_right _ (by omega)
  have b4 : Qm * (24 * K3) ≤ Qm * (16 * G6) := Nat.mul_le_mul_left _ O8b
  nlinarith

/-- The arithmetic of `Inv.step`, line `count`, with plain variables. -/
theorem count_step {cnt lam Rr L K2 G T : ℕ} (c1 : lam + 1 ≤ 2 ^ L) (O5 : Rr ≤ G) (O8c : 2 * K2 ≤ G)
    (h4 : cnt * 2 ^ (L * (2 * G)) ≤ T) : cnt * (lam + 1) ^ Rr * 2 ^ (L * (2 * K2)) ≤ T := by
  have c2 : (lam + 1) ^ Rr ≤ 2 ^ (L * G) := by
    calc (lam + 1) ^ Rr ≤ (2 ^ L) ^ Rr := Nat.pow_le_pow_left c1 _
      _ ≤ (2 ^ L) ^ G := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) O5
      _ = 2 ^ (L * G) := by rw [← pow_mul]
  calc cnt * (lam + 1) ^ Rr * 2 ^ (L * (2 * K2)) ≤ cnt * 2 ^ (L * G) * 2 ^ (L * G) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ c2)
          (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ O8c))
    _ = cnt * 2 ^ (L * (2 * G)) := by rw [mul_assoc, ← pow_add]; congr 2; ring
    _ ≤ T := h4

/-- One level preserves the invariant. -/
theorem Inv.step (hZ : 25 * Kseq t ^ 2 ≤ 2 * Z) (hZQ : Z ≤ Qm) (hL : Qm + 1 ≤ 2 ^ L) (hj : j + 1 ≤ t)
    (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    Inv t X Z Qm Wm L j (lamNext (Kseq j) (gseq j) lam) (bNext (Kseq j) (gseq j) lam B)
      (cnt * (lam + 1) ^ nRect (gseq j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Kseq_succ_sq] at h1 h2 h4
  rw [Kseq_succ_cube] at h3
  have hK : 256 ≤ Kseq j := Kseq_ge j
  have hKg : Kseq j ≤ gseq j := Kseq_le_gseq j
  have h47 := two_pow_mul_Kseq_le_gseq j
  have hg2 : 2 * Kseq j ≤ gseq j := le_trans (Nat.mul_le_mul_right _ (by norm_num)) h47
  have hg20 : 2 ^ 20 ≤ gseq j :=
    le_trans (by norm_num : 2 ^ 20 ≤ 2 ^ 47 * 1) (le_trans (Nat.mul_le_mul_left _ (by omega : 1 ≤ Kseq j)) h47)
  have hG : gseq j ^ 4 ≤ Kseq t ^ 2 := by
    rw [← Kseq_succ_sq]; exact Nat.pow_le_pow_left (Kseq_mono hj) 2
  have O1 := lamNext_contract hKg hg20 lam
  have O2 := bNext_le' hK hKg lam B
  have O8a := six_cube_mul_cube_le hg2
  obtain ⟨O8b, O8c⟩ := pow_facts hg2
  have e4 : (gseq j * gseq j) ^ 2 = gseq j ^ 4 := by ring
  rw [e4] at O8c
  have hG1 : 1 ≤ gseq j ^ 4 := Nat.one_le_pow _ _ (by omega)
  have c1 : lam + 1 ≤ 2 ^ L := by
    have : lam ≤ gseq j ^ 4 * lam := Nat.le_mul_of_pos_left _ hG1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_succ, pow_succ] at h1
    exact geo_step O1 (by omega) h1
  · omega
  · exact bits_step O2 O8a O8b h2 h3
  · exact count_step c1 (nRect_le _) O8c h4

/-- From the invariant at level j: K_j·Λ ≤ X + Z. -/
theorem Inv.mul_le (h : Inv t X Z Qm Wm L j lam B cnt) : Kseq j * lam ≤ X + Z := by
  have h1 := h.geo
  have h2 := pow_le_mul_Kseq j
  have hK : 0 < Kseq j := Kseq_pos j
  have hp : 0 < 8963 ^ j * Kseq j := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hp
  calc 8963 ^ j * Kseq j * (Kseq j * lam) = 8963 ^ j * (Kseq j ^ 2 * lam) := by ring
    _ ≤ 10000 ^ j * X + 8963 ^ j * Z := h1
    _ ≤ 8963 ^ j * Kseq j * X + 8963 ^ j * Kseq j * Z :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h2) (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hK))
    _ = 8963 ^ j * Kseq j * (X + Z) := by ring

/-- From the invariant at level j+1: g_j⁴·Λ ≤ K_j·(X + Z). -/
theorem Inv.succ_le (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) : gseq j ^ 4 * lam ≤ Kseq j * (X + Z) := by
  have h1 := h.geo
  rw [Kseq_succ_sq] at h1
  have h2 := pow_succ_le_mul_Kseq j
  have hK : 0 < Kseq j := Kseq_pos j
  have hp : 0 < 8963 ^ (j + 1) := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hp
  calc 8963 ^ (j + 1) * (gseq j ^ 4 * lam) ≤ 10000 ^ (j + 1) * X + 8963 ^ (j + 1) * Z := h1
    _ ≤ 8963 ^ (j + 1) * Kseq j * X + 8963 ^ (j + 1) * Kseq j * Z :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h2) (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hK))
    _ = 8963 ^ (j + 1) * (Kseq j * (X + Z)) := by ring

/-- The exponent of the settings of one group of the grouping, which has at most 2g/K nodes (as in
the proof of Lemma 1): Pn·(2g/K) ≤ 4·(X + Z). -/
theorem Inv.st_le (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    Pn (gseq j) lam * (2 * gseq j / Kseq j) ≤ 4 * (X + Z) := by
  have hK : 0 < Kseq j := Kseq_pos j
  refine Nat.le_of_mul_le_mul_left ?_ hK
  calc Kseq j * (Pn (gseq j) lam * (2 * gseq j / Kseq j)) ≤ 4 * (gseq j ^ 4 * lam) := mul_Pn_mul_le _ _ _
    _ ≤ 4 * (Kseq j * (X + Z)) := Nat.mul_le_mul_left _ h.succ_le
    _ = Kseq j * (4 * (X + Z)) := by ring

/-- The exponent of the labels of one node inside a group: Pn ≤ 2·(X + Z). -/
theorem Inv.lab_le (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) : Pn (gseq j) lam ≤ 2 * (X + Z) := by
  have hg : 0 < gseq j := lt_of_lt_of_le (Kseq_pos j) (Kseq_le_gseq j)
  refine Nat.le_of_mul_le_mul_left ?_ hg
  calc gseq j * Pn (gseq j) lam = 2 * (gseq j ^ 4 * lam) := mul_Pn_eq _ _
    _ ≤ 2 * (Kseq j * (X + Z)) := Nat.mul_le_mul_left _ h.succ_le
    _ ≤ 2 * (gseq j * (X + Z)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Kseq_le_gseq j))
    _ = gseq j * (2 * (X + Z)) := by ring

/-- The patterns of one instance: (Λ+1)^nRect g ≤ 2^(L·K_t²). -/
theorem Inv.pat_le (hL : Qm + 1 ≤ 2 ^ L) (hj : j + 1 ≤ t) (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    (lam + 1) ^ nRect (gseq j) ≤ 2 ^ (L * Kseq t ^ 2) := by
  have h2 := h.crude
  have hK1 : 1 ≤ Kseq (j + 1) ^ 2 := Nat.one_le_pow _ _ (Kseq_pos _)
  have c1 : lam + 1 ≤ 2 ^ L := by
    have : lam ≤ Kseq (j + 1) ^ 2 * lam := Nat.le_mul_of_pos_left _ hK1
    omega
  have hG : gseq j ^ 4 ≤ Kseq t ^ 2 := by
    rw [← Kseq_succ_sq]; exact Nat.pow_le_pow_left (Kseq_mono hj) 2
  calc (lam + 1) ^ nRect (gseq j) ≤ (2 ^ L) ^ nRect (gseq j) := Nat.pow_le_pow_left c1 _
    _ ≤ (2 ^ L) ^ (Kseq t ^ 2) :=
        Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) ((nRect_le _).trans hG)
    _ = 2 ^ (L * Kseq t ^ 2) := by rw [← pow_mul]

/-- The groupings of the g nodes into K groups, functions [g] → [K] as in the proof of Lemma 1: K^g
≤ 2^(K_t). -/
theorem col_le (hj : j + 1 ≤ t) : Kseq j ^ gseq j ≤ 2 ^ Kseq t := by
  calc Kseq j ^ gseq j ≤ 2 ^ (gseq j * gseq j) := pow_le_two_pow_sq (Kseq_le_gseq j)
    _ = 2 ^ Kseq (j + 1) := by rw [Kseq_succ_eq_mul]
    _ ≤ 2 ^ Kseq t := Nat.pow_le_pow_right (by norm_num) (Kseq_mono hj)

/-- The work list at level j: cnt·instLen K_j Λ B + 2 ≤ 2^(2·L·K_t² + X + Z + Lw + 1). -/
theorem Inv.work_le {Lw : ℕ} (hLw : Kseq t * (3 * Wm + 14) + 4 * Qm + 10 ≤ 2 ^ Lw) (hj : j ≤ t)
    (h : Inv t X Z Qm Wm L j lam B cnt) :
    cnt * instLen (Kseq j) lam B + 2 ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw + 1) := by
  have hK1 : 1 ≤ Kseq j ^ 2 := Nat.one_le_pow _ _ (Kseq_pos _)
  have w1 : cnt ≤ 2 ^ (L * (2 * Kseq t ^ 2)) :=
    le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h.count
  have w2 : (Kseq j - 1) * lam ≤ X + Z := le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) h.mul_le
  have w3 : B ≤ Wm := by
    have : B ≤ B * Kseq j ^ 3 := Nat.le_mul_of_pos_right _ (Nat.pow_pos (Kseq_pos _))
    have := h.bits
    omega
  have w4 : lam ≤ Qm := le_trans (Nat.le_mul_of_pos_left _ hK1) h.crude
  have w5 : Kseq j * (3 * B + 14) + 4 * lam + 10 ≤ 2 ^ Lw := by
    have : Kseq j * (3 * B + 14) ≤ Kseq t * (3 * Wm + 14) := Nat.mul_le_mul (Kseq_mono hj) (by omega)
    omega
  have w6 : cnt * instLen (Kseq j) lam B ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := by
    calc cnt * instLen (Kseq j) lam B
        ≤ 2 ^ (L * (2 * Kseq t ^ 2)) * (2 ^ (X + Z) * 2 ^ Lw) :=
          Nat.mul_le_mul w1 ((instLen_le _ _ _).trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) w2) w5))
      _ = 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := by rw [pow_add, pow_add]; ring
  have w7 : 2 ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := by
    have : 2 ^ 1 ≤ 2 ^ Lw := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      by_contra hc
      have : Lw = 0 := by omega
      subst this
      omega
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ Lw := this
      _ ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

/-- The brute force at the bottom: K₀(K₀−1)/2·Λ ≤ X + Z. -/
theorem Inv.bottom_le (h : Inv t X Z Qm Wm L 0 lam B cnt) : Kseq 0 * (Kseq 0 - 1) / 2 * lam ≤ X + Z := by
  have h1 := h.geo
  simp only [pow_zero, one_mul] at h1
  refine le_trans (Nat.mul_le_mul_right _ ?_) h1
  calc Kseq 0 * (Kseq 0 - 1) / 2 ≤ Kseq 0 * (Kseq 0 - 1) := Nat.div_le_self _ _
    _ ≤ Kseq 0 * Kseq 0 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = Kseq 0 ^ 2 := by ring

end PaddedDescent.F.Arith
