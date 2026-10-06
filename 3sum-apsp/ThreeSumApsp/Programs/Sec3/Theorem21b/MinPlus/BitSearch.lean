/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Passes
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem21b.BitSearch

/-!
# The (min,+)-product from "all pairs", bit by bit

Theorem 21(b), after [VW18, Theorem 4.2].  The host below computes the
(min,+)-product over an arbitrary solver of the task "all pairs": for three matrices X, Y, V, which
pairs (i, j) have X[i,k] + Y[k,j] < V[i,j] for some k.

mp(n, U, a, b, c, fr).  All entries of the product lie between −2U and 2U.  The output array starts
as −2U everywhere.  Let R be least with 2^R > 4U; the powers 1, 2, …, 2^(R−1) are written to the R
cells from fr while R is found by doubling.  For t = R − 1, …, 0: V := lo + 2^t (the n² cells from
fr + R), the solver writes its flags to the next n² cells, and lo grows by 2^t where the flag is 0.
Before the round for t, lo ≤ C[i,j] < lo + 2^(t+1): lo is C[i,j] with the lowest t + 1 bits of
C[i,j] + 2U cleared (lows x (t + 1)).  The entries of V have absolute value at most 6U.

The result is isHost_mp : IsHost pairsTask mpTask mpTime mpNeed.  First the lists: the lower bounds
lows x t, which start as −2U (lows_top), end as the product (lows_zero), and change in a round as
bump changes them (lows_round, from bitLo_step).  Then the program: the powers of two (powers_spec),
a round (round_spec, with the invariant Inv), all rounds (rounds_spec), the host (mp_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/

/-- The number of rounds: the least R with 2^R > 4U. -/
def mpRounds (U : ℕ) : ℕ := Nat.log 2 (4 * U) + 1

namespace Mp

/-- The local variables of mp: the arguments n, U, a, b, c, fr (Free); n² (Area), 2U, 4U, −2U (Low)
and 6U; Count counts the powers up and then the rounds down; Power is the power of two; then the
addresses fr + R of V (Asked), fr + R + n² of the flags and fr + R + 2n², the free pointer of the
solver (SolverFree); and the results of the calls, which are not used. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev A : ℕ := 2
@[inherit_doc N] abbrev B : ℕ := 3
@[inherit_doc N] abbrev C : ℕ := 4
@[inherit_doc N] abbrev Free : ℕ := 5
@[inherit_doc N] abbrev Area : ℕ := 6
@[inherit_doc N] abbrev TwoU : ℕ := 7
@[inherit_doc N] abbrev FourU : ℕ := 8
@[inherit_doc N] abbrev Low : ℕ := 9
@[inherit_doc N] abbrev SixU : ℕ := 10
@[inherit_doc N] abbrev Count : ℕ := 11
@[inherit_doc N] abbrev Power : ℕ := 12
@[inherit_doc N] abbrev Asked : ℕ := 13
@[inherit_doc N] abbrev Flags : ℕ := 14
@[inherit_doc N] abbrev SolverFree : ℕ := 15
@[inherit_doc N] abbrev Unused : ℕ := 16

end Mp

open Mp in
/-- The numbers n², 2U, 4U, −2U, 6U. -/
def mpConsts : Stmt :=
  .set Area (v N *' v N) ;;
  .set TwoU (v U +' v U) ;;
  .set FourU (v TwoU +' v TwoU) ;;
  .set Low (k 0 -' v TwoU) ;;
  .set SixU (v TwoU +' v FourU)

open Mp in
/-- The powers 1, 2, …, 2^(R−1) are written to the cells from fr, while R is found by doubling. -/
def mpPowers : Stmt :=
  .set Count (k 0) ;;
  .set Power (k 1) ;;
  .while (v Power ≤' v FourU) (
    .store (v Free +' v Count) (v Power) ;;
    .set Count (v Count +' k 1) ;;
    .set Power (v Power +' v Power))

open Mp in
/-- The round for t = Count − 1: V := lo + 2^t, the solver's flags, and lo grows by 2^t where the
flag is 0. -/
def mpRound (pPairs pAddc pBump : ℕ) : Stmt :=
  .set Count (v Count -' k 1) ;;
  .set Power (M (v Free +' v Count)) ;;
  .call pAddc [v Area, v Power, v C, v Asked] Unused ;;
  .call pPairs [v N, v SixU, v A, v B, v Asked, v Flags, v SolverFree] Unused ;;
  .call pBump [v Area, v Power, v Flags, v C] Unused

open Mp in
/-- mp(n, U, a, b, c, fr), over the procedures number pPairs (a solver of "all pairs"), pFill, pAddc
and pBump. -/
def mpBody (pPairs pFill pAddc pBump : ℕ) : Stmt :=
  mpConsts ;;
  mpPowers ;;
  .set Asked (v Free +' v Count) ;;
  .set Flags (v Asked +' v Area) ;;
  .set SolverFree (v Flags +' v Area) ;;
  .call pFill [v C, v Area, v Low] Unused ;;
  .while (k 0 <' v Count) (mpRound pPairs pAddc pBump)

/-- The number of steps of one round, given the time of the solver. -/
def Mp.roundTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := T n (6 * U) + 49 * (n * n) + 42

/-- The time of the host, given the time of the solver: R calls at the bound 6U, and O(n²) steps for
each call. -/
def mpTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  mpRounds U * (T n (6 * U) + 49 * (n * n) + 70) + 13 * (n * n) + 60

/-- The need of the host, given the need of the solver: the numbers up to 8U + 1, room for the R
powers of two, for V and for the flags, and one more level of calls. -/
def mpNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := max (r n (6 * U)).word (8 * U + 1)
  cells := mpRounds U + 2 * (n * n) + (r n (6 * U)).cells
  depth := (r n (6 * U)).depth + 1

namespace Mp

/-! ## The number of rounds -/

/-- The powers of two below 2^R are at most 4U. -/
theorem pow_range {U i : ℕ} (hU : 1 ≤ U) (hi : i < mpRounds U) :
    0 < (2 : ℤ) ^ i ∧ (2 : ℤ) ^ i ≤ 4 * U := by
  have hle : 2 ^ i ≤ 4 * U := Nat.pow_le_of_le_log (by omega) (by simp only [mpRounds] at hi; omega)
  exact ⟨by positivity, by exact_mod_cast hle⟩

/-- 2^R is above 4U. -/
theorem lt_pow_rounds (U : ℕ) : 4 * (U : ℤ) < 2 ^ mpRounds U := by
  exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (4 * U)

/-! ## The lists of a round -/

variable {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The lower bounds when t rounds remain: bitLo U t c for every entry c of the product, that is c
with the lowest t bits of c + 2U cleared.  So lo ≤ c < lo + 2^t. -/
def lows (x : MatInst) (t : ℕ) : List ℤ := (minPlusList x.n x.A x.B).map (bitLo x.U t)

/-- The matrix V of the round for t: the lower bounds plus 2^t. -/
def asked (x : MatInst) (t : ℕ) : List ℤ := (lows x (t + 1)).map (· + (2 : ℤ) ^ t)

/-- The flags that the solver returns in the round for t. -/
noncomputable def flags (x : MatInst) (t : ℕ) : List ℤ := pairFlags x.n x.A x.B (asked x t)

@[simp] theorem length_lows (x : MatInst) (t : ℕ) : (lows x t).length = x.n * x.n := by
  simp [lows, length_minPlusList]

@[simp] theorem length_asked (x : MatInst) (t : ℕ) : (asked x t).length = x.n * x.n := by
  simp [asked]

@[simp] theorem length_flags (x : MatInst) (t : ℕ) : (flags x t).length = x.n * x.n := by
  simp [flags, pairFlags]

/-- An entry of the lower bounds. -/
theorem getElem_lows (x : MatInst) (t q : ℕ) (hq : q < (lows x t).length) :
    (lows x t)[q] = bitLo x.U t (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) := by
  simp [lows, minPlusList]

/-- The entries of the product lie between −2U and 2U. -/
theorem entry_range (hpre : x.Pre μ fr) (i j : ℕ) :
    -(2 * (x.U : ℤ)) ≤ minPlusEntry x.n x.A x.B i j ∧ minPlusEntry x.n x.A x.B i j ≤ 2 * x.U :=
  abs_le.1 (abs_minPlusEntry_le hpre.n_pos (by positivity) hpre.leA hpre.leB i j)

/-- The lower bounds lie between −2U and 2U. -/
theorem lows_range (hpre : x.Pre μ fr) (t q : ℕ) (hq : q < (lows x t).length) :
    -(2 * (x.U : ℤ)) ≤ (lows x t)[q] ∧ (lows x t)[q] ≤ 2 * x.U := by
  rw [getElem_lows]
  have hentry := entry_range hpre (q / x.n) (q % x.n)
  exact ⟨le_bitLo _ _ _, (bitLo_le hentry.1 _).trans hentry.2⟩

/-- At the beginning all lower bounds are −2U. -/
theorem lows_top (hpre : x.Pre μ fr) :
    lows x (mpRounds x.U) = List.replicate (x.n * x.n) (-(2 * (x.U : ℤ))) := by
  refine List.ext_getElem (by simp) fun q hq _ => ?_
  rw [getElem_lows, List.getElem_replicate]
  exact bitLo_top (by linarith [(entry_range hpre (q / x.n) (q % x.n)).2, lt_pow_rounds x.U])

/-- At the end the lower bounds are the product. -/
theorem lows_zero (hpre : x.Pre μ fr) : lows x 0 = minPlusList x.n x.A x.B := by
  refine List.ext_getElem (by simp [length_minPlusList]) fun q hq _ => ?_
  rw [getElem_lows, bitLo_zero (entry_range hpre _ _).1]
  simp [minPlusList]

/-- A flag of the round for t: is the entry of the product below the lower bound plus 2^t? -/
theorem getElem_flags (hpre : x.Pre μ fr) (t q : ℕ) (hq : q < (flags x t).length) :
    (flags x t)[q] = flag (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n) <
      bitLo x.U (t + 1) (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) + 2 ^ t) := by
  have hq' : q < x.n * x.n := by simpa using hq
  have hV : (asked x t).getD q 0 =
      bitLo x.U (t + 1) (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) + 2 ^ t := by
    rw [List.getD_eq_getElem _ _ (by simpa using hq')]
    simp [asked, getElem_lows]
  simp only [flags, pairFlags, List.getElem_map, List.getElem_range, hV]
  exact flag_congr (exists_sum_lt_iff hpre.n_pos x.A x.B (q / x.n) (q % x.n) _)

/-- **One round**: each lower bound grows by 2^t where the flag is 0. -/
theorem lows_round (hpre : x.Pre μ fr) (t : ℕ) :
    List.zipWith (fun l f => l + (2 : ℤ) ^ t * (1 - f)) (lows x (t + 1)) (flags x t) =
      lows x t := by
  refine List.ext_getElem (by simp) fun q _ _ => ?_
  rw [List.getElem_zipWith, getElem_flags hpre, getElem_lows, getElem_lows,
    bitLo_step (entry_range hpre _ _).1 t]

/-- A flag is 0 or 1. -/
theorem flags_eq_zero_or_one (x : MatInst) (t : ℕ) : ∀ f ∈ flags x t, f = 0 ∨ f = 1 := by
  intro f hf
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hf
  have := flag_mem (∃ k < x.n, x.A.getD (q / x.n * x.n + k) 0 + x.B.getD (k * x.n + q % x.n) 0 <
    (asked x t).getD q 0)
  omega

/-- The lower bounds have absolute value at most 2U. -/
theorem absLe_lows (hpre : x.Pre μ fr) (t : ℕ) : AbsLe (lows x t) (2 * x.U) := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
  exact abs_le.2 (lows_range hpre t q hq)

/-- The entries of V have absolute value at most 6U. -/
theorem abs_asked_le (hpre : x.Pre μ fr) {t : ℕ} (ht : t < mpRounds x.U) :
    ∀ y ∈ lows x (t + 1), |y + (2 : ℤ) ^ t| ≤ 6 * (x.U : ℤ) := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
  have hpow := pow_range hpre.U_pos ht
  have hrange := lows_range hpre (t + 1) q hq
  exact abs_le.2 ⟨by omega, by omega⟩

/-! ## The surroundings -/

variable {P₀ R₀ : Program} {pPairs pFill pAddc pBump : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ}

/-- The surroundings of mp: a solver of "all pairs", and the three passes in the program. -/
structure Ctx (P₀ R₀ : Program) (pPairs pFill pAddc pBump : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) :
    Prop where
  sol : Solves pairsTask P₀ pPairs T r
  fill : (P₀ ++ R₀)[pFill]? = some fillBody
  addc : (P₀ ++ R₀)[pAddc]? = some addcBody
  bump : (P₀ ++ R₀)[pBump]? = some bumpBody

/-- What the limits have to allow for: the numbers of the solver and those up to 8U + 1; room for
the powers of two, V, the flags and the solver; one level of calls more than the solver needs. -/
structure Lim (lim : Limits) (d : ℕ) (r : ℕ → ℕ → Need) (x : MatInst) (fr : ℕ) : Prop where
  solver : ((r x.n (6 * x.U)).word : ℤ) ≤ lim.word
  word : 8 * (x.U : ℤ) + 1 ≤ lim.word
  cells : fr + (mpRounds x.U + 2 * (x.n * x.n) + (r x.n (6 * x.U)).cells) ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + ((r x.n (6 * x.U)).depth + 1) ≤ lim.depth

private theorem lim_of_ok (hok : (mpNeed r x.n x.U).Ok lim fr d) : Lim lim d r x fr where
  solver := le_trans (by exact_mod_cast le_max_left _ _) hok.word
  word := le_trans (by exact_mod_cast le_max_right (r x.n (6 * x.U)).word (8 * x.U + 1)) hok.word
  cells := hok.cells
  space := hok.space
  depth := hok.depth

/-- The first eleven local variables, which do not change after mpConsts. -/
abbrev consts (x : MatInst) (fr : ℕ) : List ℤ :=
  [x.n, x.U, x.a, x.b, x.c, fr, (x.n * x.n : ℕ), (2 * x.U : ℕ), (4 * x.U : ℕ), -(2 * (x.U : ℤ)),
    (6 * x.U : ℕ)]

/-- The local variables during the rounds. -/
abbrev locals (x : MatInst) (fr count : ℕ) (power unused : ℤ) : List ℤ :=
  consts x fr ++ [(count : ℤ), power, (fr + mpRounds x.U : ℕ),
    (fr + mpRounds x.U + x.n * x.n : ℕ), (fr + mpRounds x.U + x.n * x.n + x.n * x.n : ℕ), unused]

/-! ## Before the rounds -/

/-- mpConsts computes the five numbers. -/
theorem consts_spec {P : Program} (hpre : x.Pre μ fr) (hlim : Lim lim d r x fr) :
    Ends lim P d mpConsts ⟨frame [x.n, x.U, x.a, x.b, x.c, fr], μ⟩ 20 fun σ' =>
      σ' = ⟨frame (consts x fr), μ⟩ := by
  have hcells := hlim.cells
  light_facts hlim hpre
  unfold mpConsts
  refine Ends.setToThen (x.n * x.n : ℕ) ?_
  refine Ends.setToThen (2 * x.U : ℕ) ?_
  refine Ends.setToThen (4 * x.U : ℕ) ?_
  refine Ends.setToThen (-(2 * (x.U : ℤ))) ?_
  exact Ends.setTo (6 * x.U : ℕ) rfl

/-- mpPowers finds R and writes the powers of two to the R cells from fr. -/
theorem powers_spec {P : Program} (hpre : x.Pre μ fr) (hlim : Lim lim d r x fr) :
    Ends lim P d mpPowers ⟨frame (consts x fr), μ⟩ (19 * mpRounds x.U + 10) fun σ' =>
      σ' = ⟨frame (consts x fr ++ [(mpRounds x.U : ℤ), 2 ^ mpRounds x.U]),
        wrote μ fr (fun i => 2 ^ i) (mpRounds x.U)⟩ := by
  have hcells := hlim.cells
  light_facts hlim
  unfold mpPowers
  -- count := 0; power := 1
  light_set (0 : ℕ)
  light_set (2 ^ 0)
  -- while power ≤ 4U: mem[fr + count] := power; count := count + 1; power := power + power
  refine Ends.whileBlock (fun i σ => σ = ⟨frame (consts x fr ++ [(i : ℤ), 2 ^ i]),
    wrote μ fr (fun i => 2 ^ i) i⟩) (mpRounds x.U) (by rw [wrote_zero]; rfl) ?round ?done
  case round =>
    rintro i _ hi rfl
    have hpow := pow_range hpre.U_pos hi
    refine ⟨by light_side, by simp; omega, by light_side, ?_⟩
    rw [← wrote_succ]
    simp [update_frame_setLocal, pow_succ, mul_two]
  case done =>
    rintro _ rfl
    have hpow := lt_pow_rounds x.U
    exact ⟨by light_side, by simp; omega, rfl⟩

/-! ## A round -/

/-- The memory when t rounds remain: the lower bounds stand at c, the powers of two at fr, and below
the free pointer no cell outside c has changed. -/
structure Mem (x : MatInst) (μ : ℕ → ℤ) (fr t : ℕ) (μ' : ℕ → ℤ) : Prop where
  lo : Seg μ' x.c (lows x t)
  pows : ∀ i < mpRounds x.U, μ' (fr + i) = 2 ^ i
  kept : KeptBut μ μ' fr x.c (x.n * x.n)

/-- The state when t rounds remain. -/
def Inv (x : MatInst) (μ : ℕ → ℤ) (fr t : ℕ) (σ : State) : Prop :=
  ∃ (power unused : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals x fr t power unused), μ'⟩ ∧ Mem x μ fr t μ'

private theorem Inv.loc_count {t : ℕ} {σ : State} (hI : Inv x μ fr t σ) : σ.loc Count = t := by
  obtain ⟨_, _, _, rfl, -⟩ := hI
  rfl

/-- The instance that the solver gets in the round for t: the two matrices, V at fr + R, and the
place for the flags behind it. -/
def pairsInst (x : MatInst) (fr t : ℕ) : PairsInst :=
  ⟨x.n, 6 * x.U, x.a, x.b, fr + mpRounds x.U, fr + mpRounds x.U + x.n * x.n, x.A, x.B, asked x t⟩

/-- It is an instance, once V stands at its place and the two matrices are still at theirs. -/
theorem pairsInst_pre (hpre : x.Pre μ fr) {t : ℕ} (ht : t < mpRounds x.U) {μ' : ℕ → ℤ}
    (sA : Seg μ' x.a x.A) (sB : Seg μ' x.b x.B) (sV : Seg μ' (fr + mpRounds x.U) (asked x t)) :
    (pairsInst x fr t).Pre μ' (fr + mpRounds x.U + x.n * x.n + x.n * x.n) :=
  have hA := hpre.belowA
  have hB := hpre.belowB
  have hU := hpre.U_pos
  have hle : ∀ L : List ℤ, AbsLe L x.U → AbsLe L (6 * x.U : ℕ) := fun L hL y hy =>
    (hL y hy).trans (by push_cast; omega)
  { n_pos := hpre.n_pos
    U_pos := by change 1 ≤ 6 * x.U; omega
    lenX := hpre.lenA
    lenY := hpre.lenB
    lenV := length_asked x t
    segX := sA
    segY := sB
    segV := sV
    leX := hle _ hpre.leA
    leY := hle _ hpre.leB
    leV := fun y hy => by
      obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
      exact (abs_asked_le hpre ht y' hy').trans (le_of_eq (by simp [pairsInst]))
    belowX := by simp only [pairsInst]; omega
    belowY := by simp only [pairsInst]; omega
    belowV := by simp only [pairsInst]; omega
    belowOut := by simp only [pairsInst]; omega
    apartX := by simp only [pairsInst]; omega
    apartY := by simp only [pairsInst]; omega
    apartV := by simp only [pairsInst]; omega }

/-- **One round** goes from the state with t + 1 remaining rounds to the state with t. -/
theorem round_spec (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) (hpre : x.Pre μ fr)
    (hlim : Lim lim d r x fr) {t : ℕ} (ht : t < mpRounds x.U) {σ : State}
    (hI : Inv x μ fr (t + 1) σ) :
    Ends lim (P₀ ++ R₀) d (mpRound pPairs pAddc pBump) σ (roundTime T x.n x.U) (Inv x μ fr t) := by
  obtain ⟨power, unused, μ₀, rfl, hM⟩ := hI
  have hw := hlim.space
  have hlenLo := length_lows x (t + 1)
  light_facts hlim hpre hM
  unfold mpRound roundTime
  -- count := count - 1; power := mem[fr + count]
  light_set t
  light_set (2 ^ t) using hM.pows t ht
  -- addc(n², power, c, asked): V := lo + 2^t
  light_call (addc_meets C.addc (2 ^ t) (fr + mpRounds x.U) hM.lo (length_lows x _)
    (by omega) (by omega) fun y hy => (abs_asked_le hpre ht y hy).trans (by omega))
    with _ μ₁ ⟨sV, sameAddc⟩
  -- The solver writes its flags.
  refine Ends.callToThen (T' := T x.n (6 * x.U)) (C.sol.meets R₀ (pairsInst x fr t)
    (fr + mpRounds x.U + x.n * x.n + x.n * x.n) (pairsInst_pre hpre ht
      hpre.segA.keep hpre.segB.keep sV)
    ⟨hlim.solver, by simp only [pairsTask, pairsInst]; omega, hw,
      by simp only [pairsTask, pairsInst]; omega⟩) ?_ (by simp [pairsTask, pairsInst])
  rintro _ μ₂ ⟨sF, keptSolver⟩
  -- What the task promises, in terms of x: the flags, and no other change below the solver's free
  -- pointer.
  replace sF : Seg μ₂ (fr + mpRounds x.U + x.n * x.n) (flags x t) := sF
  replace keptSolver : KeptBut μ₁ μ₂ (fr + mpRounds x.U + x.n * x.n + x.n * x.n)
    (fr + mpRounds x.U + x.n * x.n) (x.n * x.n) := keptSolver
  -- bump(n², power, flags, c): lo grows by 2^t where the flag is 0
  have hpow := pow_range hpre.U_pos ht
  light_call (bump_meets C.bump (2 ^ t) sF hM.lo.keep ⟨length_flags x t, length_lows x _⟩
    (by omega) (by omega) (flags_eq_zero_or_one x t) (absLe_lows hpre _)
    ⟨by rw [abs_of_pos hpow.1]; omega, by omega⟩)
    with _ μ₃ ⟨hnew, sameBump⟩
  exact ⟨_, _, μ₃, rfl,
    { lo := lows_round hpre t ▸ hnew
      pows := fun i hi => (by light_keep : μ₃ (fr + i) = μ₀ (fr + i)).trans (hM.pows i hi)
      kept := by light_keep }⟩

/-- **The rounds** go from the state with R remaining rounds to the state with none. -/
theorem rounds_spec (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) (hpre : x.Pre μ fr)
    (hlim : Lim lim d r x fr) {σ : State} (hI : Inv x μ fr (mpRounds x.U) σ) :
    Ends lim (P₀ ++ R₀) d (.while (k 0 <' v Count) (mpRound pPairs pAddc pBump)) σ
      (mpRounds x.U * (roundTime T x.n x.U + 4) + 4) (Inv x μ fr 0) := by
  have hzero : ((0 : ℕ) : ℤ) ≤ lim.word := by have := hlim.word; omega
  refine Ends.whileConst (fun j σ => Inv x μ fr (mpRounds x.U - j) σ) (mpRounds x.U)
    (roundTime T x.n x.U) (by simpa using hI) ?round ?done
    (by simp only [Cond.cost, Expr.cost]; exact le_of_eq (by ring))
  case round =>
    intro j σ₂ hj hI₂
    obtain ⟨t, ht⟩ : ∃ t, mpRounds x.U - j = t + 1 := ⟨mpRounds x.U - j - 1, by omega⟩
    rw [show mpRounds x.U - (j + 1) = t by omega]
    rw [ht] at hI₂
    exact ⟨⟨hzero, trivial⟩, by light_norm [hI₂.loc_count]; omega,
      round_spec C hpre hlim (by omega) hI₂⟩
  case done =>
    intro σ₂ hI₂
    rw [Nat.sub_self] at hI₂
    exact ⟨⟨hzero, trivial⟩, by light_norm [hI₂.loc_count]; omega, hI₂⟩

end Mp

/-! ## The host -/

open Mp in
/-- **The host is correct**, in every program that begins with the solver's program and has the
three passes. -/
theorem mp_spec {P₀ R₀ : Program} {pPairs pFill pAddc pBump : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) {lim : Limits} {d : ℕ}
    {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) (hok : (mpNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R₀) d (mpBody pPairs pFill pAddc pBump)
      ⟨frame (mpTask.args x ++ [(fr : ℤ)]), μ⟩ (mpTime T x.n x.U)
      fun σ' => mpTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hlim := lim_of_ok hok
  have hw := hlim.space
  have hcells := hlim.cells
  light_facts hlim hpre
  have harea : 1 ≤ x.n * x.n := Nat.mul_pos hpre.n_pos hpre.n_pos
  -- For the comparisons of times below: of the steps counted for each round, 24 pay for its power
  -- of two.
  have hsplit : mpRounds x.U * (T x.n (6 * x.U) + 49 * (x.n * x.n) + 70) =
      mpRounds x.U * (roundTime T x.n x.U + 4) + 24 * mpRounds x.U := by unfold roundTime; ring
  unfold mpBody mpTime
  -- The numbers n², 2U, 4U, −2U, 6U, and the powers of two.
  light_piece (consts_spec hpre hlim) with _ rfl
  light_piece (powers_spec hpre hlim) with _ rfl
  -- asked := fr + R; flags := asked + n²; solverFree := flags + n²
  light_set (fr + mpRounds x.U : ℕ)
  light_set (fr + mpRounds x.U + x.n * x.n : ℕ)
  light_set (fr + mpRounds x.U + x.n * x.n + x.n * x.n : ℕ)
  -- fill(c, n², −2U): the first lower bounds
  light_call (fill_meets C.fill (dst := x.c) (n := x.n * x.n) (x := -(2 * (x.U : ℤ))) hw
    (by omega)) with _ μ₁ ⟨sLo, sameFill⟩
  -- The rounds.
  refine (rounds_spec C hpre hlim ⟨_, _, μ₁, rfl,
    { lo := lows_top hpre ▸ sLo
      pows := fun i hi => (sameFill _ (by omega)).trans (wrote_done hi)
      kept := by light_keep }⟩).mono ?_ ?_
  · light_time
  · rintro _ ⟨_, _, μ', rfl, hM⟩
    exact ⟨lows_zero hpre ▸ hM.lo, hM.kept⟩

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_mpNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (mpNeed r) := by
  unfold mpNeed mpRounds
  poly_need [hr.word, hr.cells, hr.depth]

/-- **The (min,+)-product from "all pairs"**, as a host. -/
theorem isHost_mp : IsHost pairsTask mpTask mpTime mpNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => polyNeed_mpNeed hr⟩
  refine ⟨[fillBody, addcBody, bumpBody, mpBody p P.length (P.length + 1) (P.length + 2)],
    P.length + 3, mpBody p P.length (P.length + 1) (P.length + 2), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact mp_spec ⟨hs, by simp, by simp, by simp⟩ hpre hok

end Light.Sec3
