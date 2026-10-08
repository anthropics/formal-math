/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.TimeBound
public import ThreeSumApsp.Programs.Sec5.Corollary39.MinMaxWeight.MaxTriangle
public import ThreeSumApsp.Programs.Sec5.Corollary39.MinMaxWeight.MinTriangle

/-!
# Corollary 39, minimum and maximum weight: the two claims about triangles in the light language

Proof of Corollary 39: "finding a maximum weight triangle costs O(log² n) times as much".  The
arithmetic that turns the time functions of the two hosts into the bounds of the claims
`Claim.VW13_Theorem_3_3_max` and `Claim.MinTriangleFromMax`, with "the problem is solved in time T"
read by `lightModel5` (`claim_VW13_Theorem_3_3_max`, `claim_minTriangleFromMax`).  With A := T + n²
(1 + log U) and Λ := log U + log n + 1, every search has O(Λ) rounds, a round of the searches for
the vertices takes O(A) steps, and a round of the search for the weight takes O(Λ A) steps
(`softO_maxTriTime`).
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp Light.Sec3

/-- The number of powers of two up to n is O(log n + 1). -/
theorem lv_le {n : ℕ} (hn : 1 ≤ n) : (lv n : ℝ) ≤ 2 * Real.log n + 1 := by
  have hlog : (Nat.log 2 n : ℝ) ≤ Real.logb (2 : ℕ) n := Real.natLog_le_logb n 2
  have hnonneg : 0 ≤ Real.log n := Real.log_nonneg (Nat.one_le_cast.2 hn)
  have hhalf := Real.one_half_lt_log_two
  have hlogb : Real.logb (2 : ℕ) n ≤ 2 * Real.log n := by
    rw [Real.logb, Nat.cast_ofNat, div_le_iff₀ (by linarith [hhalf])]
    nlinarith [hhalf, hnonneg]
  unfold lv
  push_cast
  linarith [hlog, hlogb]

/-! ## The time of maxTri -/

/-- The quantities in the time of maxTri: the size n, the bound U on the weights and a real number
u ≥ U, the time Tn of the solver of Exact Triangle, and an upper bound tau on its time at the two
bounds at which it is called. -/
structure TimePar where
  n : ℕ
  U : ℕ
  u : ℝ
  Tn : ℕ → ℕ → ℕ
  tau : ℝ

namespace TimePar

/-- What is known about the quantities. -/
structure Ok (p : TimePar) : Prop where
  n_pos : 1 ≤ p.n
  U_pos : 1 ≤ p.U
  U_le : (p.U : ℝ) ≤ p.u
  timeNT_le : (p.Tn p.n (6 * (10 * p.U)) : ℝ) ≤ p.tau
  timeET_le : (p.Tn p.n (7 * p.U + 1) : ℝ) ≤ p.tau

/-- A := T + n² (1 + log U). -/
noncomputable def work (p : TimePar) : ℝ := p.tau + (p.n : ℝ) ^ 2 * (1 + logU p.u)

/-- Λ := log U + log n + 1. -/
noncomputable def levels (p : TimePar) : ℝ := logU p.u + Real.log p.n + 1

variable {p : TimePar}

/-- n² ≤ A. -/
theorem Ok.sq_le_work (h : p.Ok) : (p.n : ℝ) * p.n ≤ p.work := by
  have htau : 0 ≤ p.tau := (Nat.cast_nonneg _).trans h.timeNT_le
  have hlog := logU_pos p.u
  have hsq : (p.n : ℝ) ^ 2 ≤ (p.n : ℝ) ^ 2 * (1 + logU p.u) :=
    le_mul_of_one_le_right (sq_nonneg _) (by linarith [hlog])
  unfold work
  linarith [htau, hsq, sq (p.n : ℝ)]

/-- 1 ≤ A. -/
theorem Ok.one_le_work (h : p.Ok) : 1 ≤ p.work :=
  (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 h.n_pos) (Nat.one_le_cast.2 h.n_pos)).trans
    h.sq_le_work

/-- T ≤ A. -/
theorem tau_le_work (p : TimePar) : p.tau ≤ p.work :=
  le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by linarith [logU_pos p.u]))

/-- log n ≥ 0. -/
theorem Ok.log_nonneg (h : p.Ok) : 0 ≤ Real.log p.n := Real.log_nonneg (Nat.one_le_cast.2 h.n_pos)

/-- 1 ≤ Λ. -/
theorem Ok.one_le_levels (h : p.Ok) : 1 ≤ p.levels := by
  unfold levels
  linarith [logU_pos p.u, h.log_nonneg]

/-- The scale of the bound: powers of A and of Λ. -/
noncomputable def scale : Scale TimePar (Fin 2) :=
  .ofBases Ok ![work, levels] fun i p hp => by
    fin_cases i
    exacts [hp.one_le_work, hp.one_le_levels]

end TimePar

open TimePar in
/-- **The time of maxTri** is O(A Λ²): every search has O(Λ) rounds, and n² and the times of the
solver are at most A. -/
theorem softO_maxTriTime : scale.SoftO (fun p => maxTriTime p.Tn p.n p.U) ![1, 2] := by
  have hsq : scale.SoftO (fun p => p.n * p.n) _ :=
    .of_le_base 0 fun p hp => by exact_mod_cast hp.sq_le_work
  have hNT : scale.SoftO (fun p => p.Tn p.n (6 * (10 * p.U))) _ :=
    .of_le_base 0 fun p hp => hp.timeNT_le.trans p.tau_le_work
  have hET : scale.SoftO (fun p => p.Tn p.n (7 * p.U + 1)) _ :=
    .of_le_base 0 fun p hp => hp.timeET_le.trans p.tau_le_work
  -- the three numbers of rounds are O(Λ)
  have hlogU : Dominated TimePar.Ok (fun p => logU p.u) levels :=
    .of_le fun p hp => by unfold levels; linarith [hp.log_nonneg]
  -- `lv (6 * U)` and `ntLevels U` are both `⌊log₂ 6U⌋ + 1`
  have hroundsW : Dominated TimePar.Ok (fun p => (lv (6 * p.U) : ℝ)) levels :=
    (Dominated.of_le_const_mul (by norm_num) fun p hp => ntLevels_le hp.U_pos hp.U_le).trans hlogU
  have hroundsNT : Dominated TimePar.Ok (fun p => (ntLevels (10 * p.U) : ℝ)) levels :=
    (Dominated.of_le_const_mul (g := fun p => Real.log 10 + logU p.u) (by norm_num) fun p hp =>
      (ntLevels_le (U := 10 * p.U) (u := 10 * p.u) (by have := hp.U_pos; omega)
        (by push_cast; linarith [hp.U_le])).trans
        (mul_le_mul_of_nonneg_left (logU_mul_le (by norm_num) p.u) (by norm_num))).trans
      ((Dominated.const _ fun p hp => hp.one_le_levels).add hlogU)
  have hroundsV : Dominated TimePar.Ok (fun p => (lv p.n : ℝ)) levels :=
    .of_le_const_mul (C := 2) (by norm_num) fun p hp => by
      unfold levels
      linarith [lv_le hp.n_pos, logU_pos p.u]
  have hW : scale.SoftO (fun p => lv (6 * p.U)) _ := .of_dominated_base 1 hroundsW
  have hN : scale.SoftO (fun p => ntLevels (10 * p.U)) _ := .of_dominated_base 1 hroundsNT
  have hV : scale.SoftO (fun p => lv p.n) _ := .of_dominated_base 1 hroundsV
  unfold maxTriTime ntTime
  growth [hsq, hNT, hET, hW, hN, hV]

/-- **Max-Weight Triangle from Exact Triangle.** -/
theorem claim_VW13_Theorem_3_3_max : Claim.VW13_Theorem_3_3_max lightModel5 := by
  obtain ⟨C, hC, hle⟩ := softO_maxTriTime.dominated fun _ _ => rfl
  refine ⟨60, C, by norm_num, hC, fun T hs =>
    isHost_maxTri.solvedIn hs fun Tn hTn n U u hn hU hu => ?_⟩
  have hU' : (1 : ℝ) ≤ U := Nat.one_le_cast.2 hU
  refine (hle ⟨n, U, u, Tn, T n (60 * u)⟩ ⟨hn, hU, hu,
    hTn n (6 * (10 * U)) (60 * u) hn (by omega) (by push_cast; linarith [hu]),
    hTn n (7 * U + 1) (60 * u) hn (by omega) (by push_cast; linarith [hu, hU'])⟩).trans_eq ?_
  simp [Scale.mon, TimePar.scale, Scale.ofBases, Fin.prod_univ_two, TimePar.work, TimePar.levels]

/-- **Min-Weight Triangle from Max-Weight Triangle.** -/
theorem claim_minTriangleFromMax : Claim.MinTriangleFromMax lightModel5 := by
  refine ⟨130, fun T hs => isHost_minTri.solvedIn hs fun Tn hTn n U u hn hU hu => ?_⟩
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (Nat.one_le_cast.2 hn)
  have hmul : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (1 + logU u) :=
    le_mul_of_one_le_right (sq_nonneg _) (by linarith [logU_pos u])
  unfold minTriTime
  push_cast
  linarith [hTn n U u hn hU hu, hsq, hmul, sq (n : ℝ)]

end Light.Sec5
