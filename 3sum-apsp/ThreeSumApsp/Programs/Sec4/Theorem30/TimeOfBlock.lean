/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Time

/-!
# Theorem 30 in the light language: the two routines against the expressions (8) and L ∑ α_d

Pure arithmetic, continued. Every summand of the time of the shared stage and of the length of the
shared block is at most a constant times `10^L`, or `N (L + 1)`, or the work for the bands
(`sharedShape_le`, `sharedEnd_sub_le`), and these three are within (8). With the tiles of the
previous file this gives the three bounds that leave these two files: the preprocessing takes
`O((8))` steps (`exists_tPreCore_le`), the block has `O((8))` cells (`exists_top_sub_le`), and a
query takes `O(L ∑_{d ≤ t} α_d)` steps (`exists_tQueryAt_le`).  The offline form uses them
elsewhere: its expression (9) is (8) plus |W| times the cost of a query (`Theorem30.cost9_eq`, with
the mathematics of Theorem 30), and `exists_tWantedCore_le`, beside the offline statement, puts the
two bounds together.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The shared stage, in natural numbers -/

/-- `(L + 1)² ≤ 10^L`. -/
theorem succ_sq_le_ten_pow (L : ℕ) : (L + 1) ^ 2 ≤ 10 ^ L := by
  have hfour : (L + 1) ^ 2 ≤ 4 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      calc (L + 1 + 1) ^ 2 ≤ 4 * (L + 1) ^ 2 := by
            rw [show (L + 1 + 1) ^ 2 = L * L + 4 * L + 4 by ring,
              show 4 * (L + 1) ^ 2 = 4 * (L * L) + 8 * L + 4 by ring]
            omega
        _ ≤ 4 * 4 ^ L := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (L + 1) := by ring
  exact hfour.trans (Nat.pow_le_pow_left (by norm_num) L)

/-- The facts about the sizes that the two estimates below use; T is `10^L` and S7 is `7^L`. -/
private structure SizeFacts (L m K KK N0 D S7 T : ℕ) : Prop where
  sq : (L + 1) ^ 2 ≤ T
  KL : K * L ≤ T
  KND : K * N0 * D ≤ S7
  LS : L * S7 ≤ 2 * T
  ST : S7 ≤ T
  KK_le : KK ≤ K
  K_pos : 1 ≤ K
  N0_pos : 1 ≤ N0
  D_pos : 1 ≤ D
  L_pos : 1 ≤ L
  mL : m ≤ L

private theorem sizeFacts (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    SizeFacts p.L p.m p.K p.KK p.N0 p.D p.S7 p.T :=
  ⟨succ_sq_le_ten_pow p.L, Theorem30.subsets p.L p.m, Theorem30.K_mul_N0_mul_D_le p.L p.m,
    Theorem30.form_array p.L, Nat.pow_le_pow_left (by norm_num) p.L, Nat.sqrt_le _,
    Nat.choose_pos hmL, Nat.one_le_pow _ _ (by norm_num), Nat.one_le_pow _ _ (by norm_num), hL1,
    hmL⟩

/-- The time of the shared stage: a part of order `10^L`, a part of order `N L`, and a part for each
band. -/
theorem sharedShape_le (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) : Sec2.sharedShape p
    ≤ 11 * 10 ^ p.L + (p.N + 1) * (p.L + 1) + p.nB * (3 * (10 ^ p.L + p.L * 7 ^ p.L)) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hsqrt : Nat.sqrt p.K ≤ p.K := Nat.sqrt_le_self _
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  unfold Sec2.sharedShape Sec2.bandArrayShape
  change _ ≤ 11 * p.T + (p.N + 1) * (p.L + 1) + p.nB * (3 * (p.T + p.L * p.S7))
  generalize p.T = T at *
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.N0 = N0 at *
  generalize p.D = D at *
  generalize p.nB = nB at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have hLT : L + 1 ≤ T := (Nat.le_self_pow (by norm_num) _).trans sq
  have hKT : K ≤ T := le_trans (Nat.le_mul_of_pos_right _ L1) KL
  have hDS : D ≤ S7 := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos K1 N1)) KND
  have hentries : KK * N0 * D ≤ S7 :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ KKle)) KND
  have hSL : S7 ≤ L * S7 := Nat.le_mul_of_pos_left _ L1
  -- the summands, one after the other
  have htable : (KK + 1) * (L + 1) ≤ K * L + K + L + 1 :=
    (Nat.mul_le_mul_right _ (by omega) : _ ≤ (K + 1) * (L + 1)).trans (le_of_eq (by ring))
  have hdig4 : (D + 1) * (m + 1) ≤ L * S7 + S7 + L + 1 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ (S7 + 1) * (L + 1)).trans (le_of_eq (by ring))
  have harray : (KK * N0 * D + 1) * (L + 1) ≤ L * S7 + S7 + L + 1 :=
    (Nat.mul_le_mul_right _ (by omega) : _ ≤ (S7 + 1) * (L + 1)).trans (le_of_eq (by ring))
  have hdig3 : (N + 1) * (Lo + 1) ≤ (N + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have hbands : nB * (T + (S7 + (KK * N0 * D + 1) * (L + 1))) ≤ nB * (3 * (T + L * S7)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- The length of the shared block. -/
theorem sharedEnd_sub_le (p : Sec2.Par) (b0 : ℕ) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    p.sharedEnd b0 - b0 ≤ 190 * 10 ^ p.L + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * 10 ^ p.L) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  change _ ≤ 190 * p.T + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * p.T)
  generalize p.T = T at *
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.N0 = N0 at *
  generalize p.D = D at *
  generalize p.nB = nB at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have hLT : L + 1 ≤ T := (Nat.le_self_pow (by norm_num) _).trans sq
  have hDS : D ≤ S7 := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos K1 N1)) KND
  have hmask : KK * L ≤ K * L := Nat.mul_le_mul_right _ KKle
  have hdig3 : N * Lo ≤ N * L := Nat.mul_le_mul_left _ hLo
  have hdig4 : D * m ≤ L * S7 := (Nat.mul_le_mul hDS mL).trans (le_of_eq (Nat.mul_comm _ _))
  rw [Nat.mul_add_one N L]
  omega

/-! ## Within (8) -/

/-- `N (L + 1)` is within three times (8), because `√K N₀ ≤ 7^L` and `(L + 1) 7^L ≤ 3 · 10^L`. -/
theorem N_mul_le_cost8 {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ 3 * cost8 p.L p.m t p.N := by
  have hpos := sqrtKN0_pos h.m_le
  have hfirst := cost8_first_term_nonneg t p.N h.L_ge
  have hKN : (K p.L p.m : ℝ) * (N0 p.L p.m : ℝ) ≤ (7 : ℝ) ^ p.L := by
    exact_mod_cast le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num)))
      (Theorem30.K_mul_N0_mul_D_le p.L p.m)
  have htile : sqrtKN0 p.L p.m ≤ (7 : ℝ) ^ p.L := (sqrtKN0_le h.m_le).trans hKN
  have hseven : ((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L ≤ 3 * (10 : ℝ) ^ p.L := by
    have harray := Theorem30.form_array p.L
    have hpow : 7 ^ p.L ≤ 10 ^ p.L := Nat.pow_le_pow_left (by norm_num) p.L
    exact_mod_cast (by rw [Nat.add_one_mul]; omega : (p.L + 1) * 7 ^ p.L ≤ 3 * 10 ^ p.L)
  -- N (L + 1) √K N₀ ≤ N (L + 1) 7^L ≤ 3 N 10^L, which is 3 √K N₀ times the last term of (8)
  have hlast : (p.N : ℝ) * ((p.L : ℝ) + 1)
      ≤ 3 * ((p.N : ℝ) * (10 : ℝ) ^ p.L / sqrtKN0 p.L p.m) := by
    rw [← mul_div_assoc, le_div_iff₀ hpos]
    calc (p.N : ℝ) * ((p.L : ℝ) + 1) * sqrtKN0 p.L p.m
        ≤ (p.N : ℝ) * ((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L :=
          mul_le_mul_of_nonneg_left htile (by positivity)
      _ = (p.N : ℝ) * (((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L) := by ring
      _ ≤ (p.N : ℝ) * (3 * (10 : ℝ) ^ p.L) := mul_le_mul_of_nonneg_left hseven (Nat.cast_nonneg _)
      _ = 3 * ((p.N : ℝ) * (10 : ℝ) ^ p.L) := by ring
  rw [cost8_eq]
  linarith

/-- `N 4^m` is within (8): it is at most the last term, because `√K N₀ 4^m ≤ K N₀ 4^m ≤ 7^L ≤ 10^L`.
-/
theorem N_mul_pow_le_cost8 {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8 p.L p.m t p.N := by
  have hfirst := cost8_first_term_nonneg t p.N h.L_ge
  have hKND : K p.L p.m * N0 p.L p.m * 4 ^ p.m ≤ 10 ^ p.L :=
    (Theorem30.K_mul_N0_mul_D_le p.L p.m).trans (Nat.pow_le_pow_left (by norm_num) _)
  have hlast : (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ (p.N : ℝ) * (10 : ℝ) ^ p.L / sqrtKN0 p.L p.m := by
    rw [le_div_iff₀ (sqrtKN0_pos h.m_le), mul_assoc]
    gcongr
    calc (4 : ℝ) ^ p.m * sqrtKN0 p.L p.m
        ≤ (4 : ℝ) ^ p.m * ((K p.L p.m : ℝ) * (N0 p.L p.m : ℝ)) := by
          gcongr
          exact sqrtKN0_le h.m_le
      _ = ((K p.L p.m * N0 p.L p.m * 4 ^ p.m : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ (10 : ℝ) ^ p.L := by exact_mod_cast hKND
  rw [cost8_eq]
  linarith

theorem within8_N_mul : Within8 fun p _ => p.N * (p.L + 1) :=
  ⟨3, by norm_num, fun p t h => by
    push_cast
    exact N_mul_le_cost8 h⟩

/-- The three quantities that bound the shared stage, together. -/
private theorem within8_shared :
    Within8 fun p _ => 10 ^ p.L + p.N * (p.L + 1) + p.nB * (10 ^ p.L + p.L * 7 ^ p.L) :=
  (within8_ten_pow.add within8_N_mul).add within8_bands

/-- **The shared stage** runs within (8). -/
theorem within8_sharedShape : Within8 fun p _ => Sec2.sharedShape p := by
  refine (within8_shared.const_mul 12).of_le fun p t h => ?_
  have hshape := sharedShape_le p h.L_pos h.m_le
  have hLT : p.L + 1 ≤ 10 ^ p.L :=
    (Nat.le_self_pow (by norm_num) _).trans (succ_sq_le_ten_pow p.L)
  rw [Nat.add_one_mul p.N, ← Nat.mul_assoc, Nat.mul_comm p.nB 3, Nat.mul_assoc] at hshape
  omega

/-- **The preprocessing** takes `O((8))` steps.  c is the constant of the shared stage. -/
theorem exists_tPreCore_le (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCore c p t : ℝ) ≤ C * cost8 p.L p.m t p.N :=
  (((within8_sharedShape.const_mul c).add within8_tAllTiles).add (within8_one.const_mul 300)).of_le
    fun _ _ _ => le_of_eq (by simp [tPreCore])

/-- The length of the block, split into the shared block, the scratch strings, and the tries with
their roots. -/
theorem top_sub_eq (p : Sec2.Par) (t b0 : ℕ) :
    top p t b0 - b0 = (p.sharedEnd b0 - b0) + (3 * p.L + p.m + 2)
      + (1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card)) + p.nB * p.nB) := by
  have := base_le_sharedEnd p b0
  simp only [top, aTR, aROOTS, aFP, aSS, aBOX, aCUR, aWD, trieCap]
  omega

/-- **The block** has `O((8))` cells. -/
theorem exists_top_sub_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t b0 : ℕ), Hyp30 p t →
    ((top p t b0 - b0 : ℕ) : ℝ) ≤ C * cost8 p.L p.m t p.N := by
  obtain ⟨C, hC, hbound⟩ := (within8_shared.const_mul 194).add within8_trieSpace
  refine ⟨C, hC, fun p t b0 h => le_trans ?_ (hbound p t h)⟩
  have hshared := sharedEnd_sub_le p b0 h.L_pos h.m_le
  have hLT : p.L + 1 ≤ 10 ^ p.L :=
    (Nat.le_self_pow (by norm_num) _).trans (succ_sq_le_ten_pow p.L)
  have hm := h.m_le
  rw [top_sub_eq]
  refine Nat.cast_le.2 (Nat.add_le_add_right ?_ _)
  rw [Nat.mul_add p.nB]
  omega

/-- **A query** takes `O(L ∑_{d ≤ t} α_d)` steps. -/
theorem exists_tQueryAt_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tQueryAt p.L p.m t : ℝ) ≤ C * costQuery p.L p.m t := by
  obtain ⟨C, hC, hcore⟩ := exists_tQueryCore_le
  refine ⟨C + 510, by positivity, fun p t h => ?_⟩
  have hcore := hcore p.L p.m t h.L_pos h.m_le h.t_le
  have hL := cast_L_le_costQuery p.L p.m t
  have hL1 : (1 : ℝ) ≤ p.L := by exact_mod_cast h.L_pos
  -- tQueryAt = 70 L + 440 + tQueryCore
  unfold tQueryAt tOutDigits
  push_cast
  linarith

end Light.Sec4
