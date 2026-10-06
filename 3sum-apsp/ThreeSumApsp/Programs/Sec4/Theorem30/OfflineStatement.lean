/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.OfflineLayout
public import ThreeSumApsp.Programs.Sec4.Theorem30.ThinLayout
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize

/-!
# Theorem 30, the offline form (9), on the word RAM

From the specifications of preCore and queryAt to Items.Theorem_30_wanted, for any program that
holds wantedCore and wantedMain at their numbers (`theorem_30_wanted_of`). The light program solves
the problem (`wanted_topSolves`) for four reasons, one lemma each: the trusted input is laid out as
wantedMain expects (`wantedLayout_input`), the time is `O((9))` (`exists_tWantedCore_le`), the block
starts at an address that is polynomial in N (`wantedB0_le`), and the numbers of the input fit in a
word (`abs_wanted_input_le`).
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-- A list of positions without repetitions has at most N² members. -/
theorem length_le_sq {N : ℕ} {W : List (Fin N × Fin N)} (h : W.Nodup) : W.length ≤ N * N := by
  simpa using h.length_le_card

/-- **The time** of the main procedure is `O((9))`: the preprocessing is within (8), and each of the
w rounds is within the cost of a query. -/
theorem exists_tWantedCore_le (c0 : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t w : ℕ), Hyp30 p t →
    ((tWantedCore c0 p t w + 70 : ℕ) : ℝ) ≤ C * cost9 p.L p.m t p.N w := by
  obtain ⟨A, hA, hpre⟩ := exists_tPreCore_le c0
  obtain ⟨B, hB, hquery⟩ := exists_tQueryAt_le
  refine ⟨A + B + 86, by positivity, fun p t w h => ?_⟩
  have hpre := hpre p t h
  have hquery := hquery p t h
  have hone8 := one_le_cost8 p.L p.m t p.N h.L_ge h.N_ge
  have honeQ := one_le_costQuery (t := t) h.m_pos h.L_ge
  have hrounds : (w : ℝ) * ((tQueryAt p.L p.m t : ℝ) + 24)
      ≤ (w : ℝ) * ((B + 24) * costQuery p.L p.m t) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg w)
  have hwQ : 0 ≤ (w : ℝ) * costQuery p.L p.m t := mul_nonneg (Nat.cast_nonneg w) (by linarith)
  have hAwQ := mul_nonneg hA hwQ
  have hB8 : 0 ≤ B * cost8 p.L p.m t p.N := mul_nonneg hB (by linarith)
  -- tPreCore + w (tQueryAt + 24) + 86 ≤ (A + 86) (8) + (B + 24) w (query cost)
  rw [Theorem30.cost9_eq]
  unfold tWantedCore
  push_cast
  linarith [hpre, hrounds, hone8, hwQ, hAwQ, hB8]

/-- The trusted input of the offline form, with D = 4^m, is laid out as wantedMain expects. -/
theorem wantedLayout_input {N U : ℕ} (m L t : ℕ) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (bX : ∀ i j, |X i j| ≤ (U : ℤ))
    (bY : ∀ i j, |Y i j| ≤ (U : ℤ)) (W : List (Fin N × Fin N)) (nd : W.Nodup) :
    WantedLayout m L t X Y W (memOf
      ((⟨⟨N, D m, U, X, Y, bX, bY⟩, W, nd⟩ : ThinInstance).input [(m : ℤ), (L : ℤ), (t : ℤ)])) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, thinInstance_matAt_X _ _, thinInstance_matAt_Y _ _,
    thinInstance_seg_rows _ _, thinInstance_seg_cols _ _⟩

/-- **The block** starts at an address that is polynomial in N. -/
theorem wantedB0_le {N m w : ℕ} (hD : D m ≤ N) (hw : w ≤ N * N) :
    wantedB0 N m w ≤ 10 * (N + 1) ^ 3 := by
  have harea : N * D m ≤ N * N := Nat.mul_le_mul_left _ hD
  have hcube : 6 + 5 * (N * N) ≤ 10 * (N + 1) ^ 3 := by
    have : (N + 1) ^ 3 = N * N * N + 3 * (N * N) + 3 * N + 1 := by ring
    omega
  simp only [wantedB0, wantedOut]
  omega

/-- **The numbers of the input fit in a word** of the limits of Theorem 30, if the block starts
behind them. -/
theorem abs_wanted_input_le (x : ThinInstance) {m L t c b0 : ℕ} (hmL : m ≤ L) (ht : t ≤ m)
    (hU : x.U = x.N ^ c) (hN : x.N ≤ b0) (hD : x.D ≤ b0) (hW : x.W.length ≤ b0) :
    ∀ v ∈ x.input [(m : ℤ), (L : ℤ), (t : ℤ)], |v| ≤ (lim30 ⟨L, m, x.N⟩ t b0 c).word := by
  exact abs_thinInstance_input_le (cast_le_word30 _ t b0 c (Or.inl hN))
    (cast_le_word30 _ t b0 c (Or.inl hD)) (cast_le_word30 _ t b0 c (Or.inl hW))
    (hU ▸ pow_le_word30 ⟨L, m, x.N⟩ t b0 c) (abs_params_le_word30 x.N b0 c hmL ht)

/-- **The offline form of Theorem 30 as a light program.** -/
theorem wanted_topSolves {P : Program} {c0 : ℕ} (h56 : P[Proc.wantedCore]? = some wantedCoreBody)
    (h57 : P[Proc.wantedMain]? = some wantedMainBody) (hpre : ∀ lim, PreCoreSpec lim P c0)
    (hq : ∀ lim, QueryAtSpec lim P) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c m L t : ℕ,
    ProgramSolves (thinProduct [(m : ℤ), (L : ℤ), (t : ℤ)]) P Proc.wantedMain false 9 (20 + 2 * c)
      (fun x => Items.theorem30Dom c m L t x.toThinPair)
      (fun x => C * cost9 L m t x.N x.W.length) := by
  obtain ⟨C, hC, htime⟩ := exists_tWantedCore_le c0
  refine ⟨C, hC, fun c m L t => ?_⟩
  rintro ⟨⟨N, D', U, X, Y, bX, bY⟩, W, nd⟩ ⟨hm, hD, hL, ht, hN, hU⟩
  simp only at hD hN hU bX bY
  subst hD hU
  have hyp : Hyp30 ⟨L, m, N⟩ t := ⟨hm, hL, ht, hN⟩
  have hDN : D m ≤ N := hyp.D_le_N
  have hb0 := wantedB0_le hDN (length_le_sq nd)
  obtain ⟨b0, hblock⟩ : ∃ b0, b0 = wantedB0 N m W.length := ⟨_, rfl⟩
  rw [← hblock] at hb0
  have bX' : ∀ i j, |X i j| ≤ (N : ℤ) ^ c := fun i j => by exact_mod_cast bX i j
  have bY' : ∀ i j, |Y i j| ≤ (N : ℤ) ^ c := fun i j => by exact_mod_cast bY i j
  obtain ⟨σ', n, hexec, hn, -, hanswers⟩ := (wantedMain_meets (lim := lim30 ⟨L, m, N⟩ t b0 c) h57
    (wantedCore_spec h56 (hpre _) (hq _)) (by omega : m ≤ L) ht bX' bY'
    (hblock ▸ lim30_ok ⟨L, m, N⟩ t b0 c) (by change L + 9 ≤ L + 10; omega)
    (wantedLayout_input m L t X Y bX bY W nd)).main (by change 0 < L + 10; omega)
      (le_trans (Nat.cast_le.2 (by omega)) (htime ⟨L, m, N⟩ t W.length hyp))
  refine ⟨_, σ', n, hexec, hn, ?_, small_lim30 hyp b0 c hb0, rfl, fun i hi => ?_⟩
  · have hNb : N ≤ N * D m := Nat.le_mul_of_pos_right _ (by unfold D; positivity)
    simp only [wantedB0, wantedOut] at hblock
    exact abs_wanted_input_le _ (by omega) ht rfl (by change N ≤ b0; omega)
      (by change D m ≤ b0; omega)
      (by change W.length ≤ b0; omega)
  · -- the answer stands behind the input
    have hcell := hanswers i (by simpa using hi)
    rw [List.getElem_map] at hcell
    exact (congrArg (fun a => σ'.mem (a + i))
      ((length_thinInstance_input _ _).trans rfl)).trans hcell

/-- **Theorem 30, the offline form, on the word RAM**, for any program that holds the routines. -/
theorem theorem_30_wanted_of {P : Program} {c0 : ℕ}
    (h56 : P[Proc.wantedCore]? = some wantedCoreBody)
    (h57 : P[Proc.wantedMain]? = some wantedMainBody) (hpre : ∀ lim, PreCoreSpec lim P c0)
    (hq : ∀ lim, QueryAtSpec lim P) : Items.Theorem_30_wanted := by
  obtain ⟨C, -, hsolves⟩ := wanted_topSolves h56 h57 hpre hq
  intro c
  refine ⟨compileProgram P Proc.wantedMain false, slopeOf P false 9 (20 + 2 * c) 2,
    (timeConst P false : ℝ) * (C + 1), fun m L t => ?_⟩
  refine solves_of_programSolves_scaled (hsolves c m L t) (fun x => by simp [thinProduct]) ?_
  rintro x ⟨hm, -, hL, -, hN, -⟩
  -- (9) is at least (8), which is at least 1
  rw [Theorem30.cost9_eq]
  have hone8 := one_le_cost8 L m t x.N hL hN
  have honeQ := one_le_costQuery (t := t) hm hL
  have hwQ : (0 : ℝ) ≤ (x.W.length : ℝ) * costQuery L m t :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

end Light.Sec4
