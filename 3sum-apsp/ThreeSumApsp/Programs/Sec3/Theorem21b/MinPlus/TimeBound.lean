/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.AllPairs
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.BitSearch
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.FindNegativeTriangle
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# The (min,+)-product from Negative Triangle: the claim

[VW18, Theorem 4.2] in the form needed for Theorem 21(b).  The three hosts
(finding from deciding, all pairs from finding, the product from all pairs) are composed, and their
time functions are bounded with the two properties of a good running time: T(s)/s is nondecreasing,
and T(s) ≥ s² (1 + log u).

Each host has one bound, up to a constant factor: finding costs O(T(n)) (findTime_dominated: the
side lengths of the search add up to at most 2n, and T(h) ≤ (h/n) T(n)); all pairs cost
O(n² T(⌈n^{1/3}⌉)) (pairsTime_dominated: there are O(n²) rounds, rounds_le); the product costs
O(log u) calls (mpTime_dominated, mpRounds_le).  claim_VW18_Theorem_4_2 puts the three together.
-/

@[expose] public section

/-! ## Good running times -/

namespace ThreeSumApsp.GoodTime

variable {T : ℕ → ℝ → ℝ}

/-- A good running time is at least s². -/
theorem sq_le (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) : (s : ℝ) ^ 2 ≤ T s u :=
  (le_mul_of_one_le_right (by positivity) (by linarith [logU_pos u])).trans (hT.1 s u hs)

/-- A good running time is at least 1. -/
theorem one_le (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) : 1 ≤ T s u :=
  (one_le_pow₀ (Nat.one_le_cast.2 hs)).trans (hT.sq_le hs u)

/-- T(h) ≤ h T(s)/s for h ≤ s. -/
theorem le_mul_div (hT : GoodTime T) {h s : ℕ} (hh : 1 ≤ h) (hs : h ≤ s) (u : ℝ) :
    T h u ≤ (h : ℝ) * (T s u / s) := by
  have hdiv := hT.2 u h s hh hs
  rwa [div_le_iff₀ (by exact_mod_cast hh), mul_comm] at hdiv

/-- C T is a good running time for C ≥ 1. -/
theorem const_mul (hT : GoodTime T) {C : ℝ} (hC : 1 ≤ C) : GoodTime fun s u => C * T s u := by
  refine ⟨fun s u hs => (hT.1 s u hs).trans (le_mul_of_one_le_left ?_ hC), fun u s₁ s₂ h₁ h₂ => ?_⟩
  · linarith [hT.one_le hs u]
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hT.2 u s₁ s₂ h₁ h₂) (by linarith)

end ThreeSumApsp.GoodTime

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The least s with s³ ≥ n is ⌈n^{1/3}⌉. -/
theorem cbrtLeast_eq_cbrtCeil (n : ℕ) : cbrtLeast n = ThreeSumApsp.cbrtCeil n := by
  have key : ∀ s : ℕ, (n : ℝ) ^ (1 / 3 : ℝ) ≤ s ↔ n ≤ s ^ 3 := by
    intro s
    have h3 : ((s : ℝ) ^ 3) ^ (1 / 3 : ℝ) = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    constructor
    · intro h
      have : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 ≤ (s : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
      norm_num at this
      exact_mod_cast this
    · intro h
      rw [← h3]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by norm_num)
  apply le_antisymm
  · exact cbrtLeast_le ((key _).1 (Nat.le_ceil _))
  · exact Nat.ceil_le.2 ((key _).2 (le_cbrtLeast_pow n))

namespace MinPlusFromNeg

/-! ## The parameters of a bound -/

/-- What a bound on the time of a host speaks about: a bound T on the time Tn of the solver, and an
instance of size n with a bound U ≤ u on its numbers. -/
structure Run where
  T : ℕ → ℝ → ℝ
  Tn : ℕ → ℕ → ℕ
  n : ℕ
  U : ℕ
  u : ℝ

/-- The solver keeps to its bound, and the instance is valid. -/
structure Run.Valid (p : Run) : Prop where
  solver : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (p.Tn n U : ℝ) ≤ p.T n u
  n_pos : 1 ≤ p.n
  U_pos : 1 ≤ p.U
  U_le : (p.U : ℝ) ≤ p.u

/-- The run is valid, and the bound on the time of the solver is a good running time. -/
structure Run.Good (p : Run) : Prop extends p.Valid where
  good : GoodTime p.T

/-- The run is valid, and the bound on the time of the solver is at least n². -/
structure Run.Quadratic (p : Run) : Prop extends p.Valid where
  sq_le : ∀ u, (p.n : ℝ) ^ 2 ≤ p.T p.n u

/-- The solver on the instance of the run keeps to its bound. -/
theorem Run.Valid.solver_le {p : Run} (hp : p.Valid) : (p.Tn p.n p.U : ℝ) ≤ p.T p.n p.u :=
  hp.solver _ _ _ hp.n_pos hp.U_pos hp.U_le

/-! ## Finding from deciding -/

/-- The round of the search that goes to the side length n costs O(T(n)):
8 (Tn + 150 n² + 130) ≤ 8 (T + 150 T + 130 T). -/
theorem roundBound_dominated :
    Dominated Run.Good (fun p => (roundBound p.Tn p.n p.U : ℝ)) fun p => p.T p.n p.u :=
  ((((Dominated.of_le fun p hp => hp.solver_le).add
    ((Dominated.of_le fun p hp => hp.good.sq_le hp.n_pos _).const_mul (c := 150) (by norm_num))).add
    (.const 130 fun p hp => hp.good.one_le hp.n_pos _)).const_mul (c := 8) (by norm_num)).congr
    (fun p _ => by simp [roundBound]) fun _ _ => rfl

/-- The rounds of the search cost O(T(n)): T(h) ≤ h (T(n)/n), and the side lengths add up to at most
2n. -/
theorem search_dominated :
    Dominated Run.Good (fun p => (((halvingChain p.n).map fun h => roundBound p.Tn h p.U).sum : ℕ))
      fun p => p.T p.n p.u := by
  obtain ⟨C, hC, hround⟩ := roundBound_dominated
  refine ⟨C * 2, by positivity, fun p hp => ?_⟩
  have hn : (0 : ℝ) < p.n := by exact_mod_cast hp.n_pos
  have hτ : 0 ≤ p.T p.n p.u := by linarith [hp.good.one_le hp.n_pos p.u]
  calc ((((halvingChain p.n).map fun h => roundBound p.Tn h p.U).sum : ℕ) : ℝ)
      = ((halvingChain p.n).map fun h => (roundBound p.Tn h p.U : ℝ)).sum := by
        rw [Nat.cast_list_sum, List.map_map]
        rfl
    _ ≤ ((halvingChain p.n).map fun h : ℕ => (h : ℝ) * (C * (p.T p.n p.u / p.n))).sum := by
        refine List.sum_le_sum fun h hh => ?_
        obtain ⟨hpos, hlt⟩ := bounds_of_mem_halvingChain hh
        calc (roundBound p.Tn h p.U : ℝ) ≤ C * p.T h p.u :=
              hround { p with n := h } { hp with n_pos := hpos }
          _ ≤ C * ((h : ℝ) * (p.T p.n p.u / p.n)) :=
              mul_le_mul_of_nonneg_left (hp.good.le_mul_div hpos hlt.le p.u) hC
          _ = (h : ℝ) * (C * (p.T p.n p.u / p.n)) := by ring
    _ = ((halvingChain p.n).sum : ℕ) * (C * (p.T p.n p.u / p.n)) := by
        rw [List.sum_map_mul_right, Nat.cast_list_sum]
    _ ≤ (2 * p.n : ℕ) * (C * (p.T p.n p.u / p.n)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast sum_halvingChain_le p.n) (by positivity)
    _ = C * 2 * p.T p.n p.u := by
        push_cast
        field_simp

/-- **Finding from deciding**: the time grows by a constant factor only. -/
theorem findTime_dominated :
    Dominated Run.Good (fun p => (findTime p.Tn p.n p.U : ℝ)) fun p => p.T p.n p.u := by
  refine (((Dominated.const 40 fun p hp => hp.good.one_le hp.n_pos _).add
    (.of_le fun p hp => hp.solver_le)).add search_dominated).congr (fun p _ => ?_) fun _ _ => rfl
  simp only [findTime]
  push_cast
  rfl

/-! ## All pairs from finding -/

/-- The number of rounds of "all pairs" is at most 9n². -/
theorem rounds_le {n : ℕ} (hn : 1 ≤ n) : blockCount n (cbrtLeast n) ^ 3 + n ^ 2 ≤ 9 * n ^ 2 := by
  have hcube : n ≤ cbrtLeast n ^ 3 := le_cbrtLeast_pow n
  have hblocks : blockCount n (cbrtLeast n) * cbrtLeast n ≤ 2 * n := by
    have := blockCount_mul_lt (n := n) (one_le_cbrtLeast hn)
    have := cbrtLeast_le_self n
    omega
  generalize cbrtLeast n = s at *
  generalize blockCount n s = p at *
  -- p³ n ≤ p³ s³ = (p s)³ ≤ (2n)³
  have hmul : p ^ 3 * n ≤ 8 * n ^ 2 * n :=
    calc p ^ 3 * n ≤ p ^ 3 * s ^ 3 := Nat.mul_le_mul_left _ hcube
      _ = (p * s) ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left hblocks 3
      _ = 8 * n ^ 2 * n := by ring
  have := Nat.le_of_mul_le_mul_right hmul hn
  omega

/-- **All pairs from finding**: O(n²) questions at the size ⌈n^{1/3}⌉. -/
theorem pairsTime_dominated :
    Dominated Run.Good (fun p => (pairsTime p.Tn p.n p.U : ℝ))
      fun p => (p.n : ℝ) ^ 2 * p.T (cbrtCeil p.n) (3 * p.u) := by
  have hs : ∀ p : Run, p.Good → 1 ≤ cbrtLeast p.n := fun p hp => one_le_cbrtLeast hp.n_pos
  -- powers of n and of T(s), where s = ⌈n^{1/3}⌉
  let s : Scale Run (Fin 2) := .ofBases Run.Good
    ![fun p => p.n, fun p => p.T (cbrtLeast p.n) (3 * p.u)] fun i p hp => by
      fin_cases i
      exacts [Nat.one_le_cast.2 hp.n_pos, hp.good.one_le (hs p hp) _]
  have hn : s.SoftO (fun p => p.n) _ := .of_le_base 0 fun _ _ => le_rfl
  -- One round costs O(T(s)).
  have hsq : s.SoftO (fun p => cbrtLeast p.n ^ 2) _ :=
    .of_le_base 1 fun p hp => by exact_mod_cast hp.good.sq_le (hs p hp) (3 * p.u)
  have hsolver : s.SoftO (fun p => p.Tn (cbrtLeast p.n) (2 * p.U + 1)) _ :=
    .of_le_base 1 fun p hp => hp.solver _ _ _ (hs p hp) (by omega) (by
      have hU : (1 : ℝ) ≤ p.U := by exact_mod_cast hp.U_pos
      push_cast
      linarith [hp.U_le])
  -- There are O(n²) rounds.
  have hrounds : s.SoftO (fun p => blockCount p.n (cbrtLeast p.n) ^ 3 + p.n ^ 2) ![2, 0] :=
    (by growth [hn] : s.SoftO (fun p => 9 * p.n ^ 2) ![2, 0]).of_le fun p hp => rounds_le hp.n_pos
  have htime : s.SoftO (fun p => pairsTime p.Tn p.n p.U) ![2, 1] := by
    unfold pairsTime
    growth [hrounds, hn, hsq, hsolver]
  refine (htime.dominated fun _ _ => rfl).congr (fun _ _ => rfl) fun p _ => ?_
  rw [← cbrtLeast_eq_cbrtCeil]
  simp [Scale.mon, s, Scale.ofBases, Fin.prod_univ_two]

/-! ## The product from all pairs -/

/-- The number of rounds of the search is O(log u). -/
theorem mpRounds_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (mpRounds U : ℝ) ≤ 8 * logU u := by
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hhalf := Real.one_half_lt_log_two
  have hpow : 2 ^ Nat.log 2 (4 * U) ≤ 4 * U := Nat.pow_log_le_self 2 (by omega)
  -- ⌊log₂ 4U⌋ log 2 ≤ log 4U = 2 log 2 + log U
  have hlog : (Nat.log 2 (4 * U) : ℝ) * Real.log 2 ≤ Real.log (4 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_four] at hlog
  have hUu : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  have h2u := log_two_le_logU u
  have hleft : (Nat.log 2 (4 * U) : ℝ) * (1 / 2) ≤ (Nat.log 2 (4 * U) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hhalf.le (Nat.cast_nonneg _)
  simp only [mpRounds]
  push_cast
  -- ⌊log₂ 4U⌋ / 2 ≤ 3 logU u, and 1 ≤ 2 logU u
  linarith

/-- **The product from all pairs**: O(log u) calls, if a call takes at least n² steps. -/
theorem mpTime_dominated :
    Dominated Run.Quadratic (fun p => (mpTime p.Tn p.n p.U : ℝ))
      fun p => p.T p.n (6 * p.u) * logU p.u := by
  -- powers of T(n) and of 2 log u, which is at least 1
  let s : Scale Run (Fin 2) := .ofBases Run.Quadratic
    ![fun p => p.T p.n (6 * p.u), fun p => 2 * logU p.u] fun i p hp => by
      fin_cases i
      · exact (one_le_pow₀ (Nat.one_le_cast.2 hp.n_pos)).trans (hp.sq_le _)
      · change 1 ≤ 2 * logU p.u
        linarith [log_two_le_logU p.u, Real.one_half_lt_log_two]
  -- A round, and the steps before the rounds, cost O(T(n)).
  have hsq : s.SoftO (fun p => p.n * p.n) _ :=
    .of_le_base 0 fun p hp => by exact_mod_cast (sq (p.n : ℝ)).ge.trans (hp.sq_le (6 * p.u))
  have hsolver : s.SoftO (fun p => p.Tn p.n (6 * p.U)) _ :=
    .of_le_base 0 fun p hp => hp.solver p.n (6 * p.U) (6 * p.u) hp.n_pos
      (by have := hp.U_pos; omega) (by push_cast; linarith [hp.U_le])
  have hrounds : s.SoftO (fun p => mpRounds p.U) _ :=
    .of_dominated_base 1 <| .of_le_const_mul (C := 4) (by norm_num) fun p hp => by
      change _ ≤ 4 * (2 * logU p.u)
      linarith [mpRounds_le hp.U_pos hp.U_le]
  have htime : s.SoftO (fun p => mpTime p.Tn p.n p.U) ![1, 1] := by
    unfold mpTime
    growth [hsq, hsolver, hrounds]
  refine (htime.dominated fun _ _ => rfl).trans (.of_le_const_mul (C := 2) (by norm_num)
    fun p _ => le_of_eq ?_)
  simp [Scale.mon, s, Scale.ofBases, Fin.prod_univ_two]
  ring

end MinPlusFromNeg

open MinPlusFromNeg in
/-- **[VW18, Theorem 4.2]: the (min,+)-product from Negative Triangle.** -/
theorem claim_VW18_Theorem_4_2 : Claim.VW18_Theorem_4_2 lightModel := by
  obtain ⟨C₁, hC₁, hfind⟩ := findTime_dominated
  obtain ⟨C₂, hC₂, hpairs⟩ := pairsTime_dominated
  obtain ⟨C₃, hC₃, hmp⟩ := mpTime_dominated
  refine ⟨18, C₃ * ((C₂ + 1) * (C₁ + 1)), by norm_num, by positivity, fun T hT hneg => ?_⟩
  -- Finding, in time (C₁ + 1) T(n), which is a good running time again.
  have hgood := hT.const_mul (le_add_of_nonneg_left hC₁ : 1 ≤ C₁ + 1)
  have hone : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ (C₁ + 1) * T (cbrtCeil n) u := fun n u hn =>
    hgood.one_le (one_le_cbrtCeil hn) u
  have hfindSolved : SolvedIn findTask fun n u => (C₁ + 1) * T n u :=
    isHost_find.solvedIn hneg fun Tn hTn n U u hn hU hu =>
      (hfind ⟨T, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, hT⟩).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith [hT.one_le hn u]))
  -- All pairs.
  have hpairsSolved : SolvedIn pairsTask fun n u =>
      (C₂ + 1) * ((n : ℝ) ^ 2 * ((C₁ + 1) * T (cbrtCeil n) (3 * u))) :=
    isHost_pairs.solvedIn hfindSolved fun Tn hTn n U u hn hU hu =>
      (hpairs ⟨_, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, hgood⟩).trans (mul_le_mul_of_nonneg_right
        (by linarith) (mul_nonneg (by positivity) (by linarith [hone n (3 * u) hn])))
  -- The product: a call for all pairs takes at least n² steps.
  have hmpSolved : SolvedIn mpTask fun n u =>
      C₃ * ((C₂ + 1) * ((n : ℝ) ^ 2 * ((C₁ + 1) * T (cbrtCeil n) (3 * (6 * u)))) * logU u) := by
    refine isHost_mp.solvedIn hpairsSolved fun Tn hTn n U u hn hU hu =>
      hmp ⟨_, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, fun u' => ?_⟩
    calc (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * ((C₁ + 1) * T (cbrtCeil n) (3 * u')) :=
          le_mul_of_one_le_right (by positivity) (hone n _ hn)
      _ ≤ _ := le_mul_of_one_le_left
          (mul_nonneg (by positivity) (by linarith [hone n (3 * u') hn])) (by linarith)
  refine ⟨_, hmpSolved, fun n U _ _ => le_of_eq ?_⟩
  rw [show 3 * (6 * U) = 18 * U by ring]
  ring

end Light.Sec3
