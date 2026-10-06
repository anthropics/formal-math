/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21a.Convolution.Fill
public import ThreeSumApsp.Programs.Tasks

/-!
# Convolution-3SUM from Exact Triangle: the host

Theorem 21(a), after [VW13, Theorem 4.3]: whether an array of N integers is a yes-instance of
Convolution-3SUM is decided by asking O(√N) times whether there is a zero triangle, each time in an
instance with O(√N) vertices in each part whose weights are entries of the array, up to sign, or a
filler. c3(N, U, x, fr) computes t = ⌊√N⌋ + 1 and runs an arbitrary solver of Exact Triangle once
for each of the 2t instances, which have t vertices in each part and weights of absolute value at
most 2U + 1.  The three matrices of the current instance are written at the free pointer.  There is
no early exit.

One round writes instance s and asks the solver (`round_spec`); after s rounds the local Found says
whether one of the first s instances has a zero triangle.  By `convolution3SUM_vecOf_iff` the answer
after 2t rounds is the answer to Convolution-3SUM (`c3_spec`).  The need of the host is polynomially
bounded if the solver's is (`polyNeed_c3Need`).  The host with its time and its need is `isHost_c3`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/

namespace ConvHost

/-- The local variables of c3: the arguments N (Len; as local 0 it also takes the result), U
(Bound), x (Input), fr (Free); then t (Side), the number s of the instance (Inst), the answer so far
(Found), the result of a call (Answer), t² (Area) and the filler 2U + 1 (Filler). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Input : ℕ := 2
@[inherit_doc Len] abbrev Free : ℕ := 3
@[inherit_doc Len] abbrev Side : ℕ := 4
@[inherit_doc Len] abbrev Inst : ℕ := 5
@[inherit_doc Len] abbrev Found : ℕ := 6
@[inherit_doc Len] abbrev Answer : ℕ := 7
@[inherit_doc Len] abbrev Area : ℕ := 8
@[inherit_doc Len] abbrev Filler : ℕ := 9

end ConvHost

open ConvHost

/-- One round: writes instance number Inst at the free pointer and asks the solver. -/
def c3Round (pET pFill : ℕ) : Stmt :=
  .call pFill [v Side, v Len, v Inst, v Filler, v Input, v Free, v Free +' v Area,
    v Free +' k 2 *' v Area] Answer ;;
  .call pET [v Side, v Filler, v Free, v Free +' v Area, v Free +' k 2 *' v Area,
    v Free +' k 3 *' v Area] Answer ;;
  .ite (v Answer =' k 1) (.set Found (k 1)) .skip

/-- c3(N, U, x, fr), over the procedures pET (a solver of Exact Triangle), pSqrt (the integer square
root) and pFill (convFill).  The result is returned in local 0. -/
def c3Body (pET pSqrt pFill : ℕ) : Stmt :=
  .call pSqrt [v Len] Side ;;
  .set Side (v Side +' k 1) ;;
  .set Area (v Side *' v Side) ;;
  .set Filler (k 2 *' v Bound +' k 1) ;;
  .set Found (k 0) ;;
  .for Inst (k 2 *' v Side) (c3Round pET pFill) ;;
  .set Len (v Found)

/-- The time of one round: it writes 3t² cells and runs the solver on t vertices per part with the
bound 2U + 1. -/
def c3RoundTime (T : ℕ → ℕ → ℕ) (t U : ℕ) : ℕ := convFillTime t + 40 + T t (2 * U + 1)

/-- The time of the host: the square root, and 2t rounds with t = ⌊√N⌋ + 1. -/
def c3Time (T : ℕ → ℕ → ℕ) (N U : ℕ) : ℕ :=
  18 * Nat.sqrt N + 41 + 2 * (Nat.sqrt N + 1) * (c3RoundTime T (Nat.sqrt N + 1) U + 10)

/-- The need of the host: 3t² cells more than the solver, one level of calls more, and words for the
square root (3N + 4), the filler (2U + 1) and the indices (2t² + 2t). -/
def c3Need (r : ℕ → ℕ → Need) (N U : ℕ) : Need where
  word := (r (Nat.sqrt N + 1) (2 * U + 1)).word + 3 * N + 2 * U +
    2 * ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) + 2 * (Nat.sqrt N + 1) + 5
  cells := 3 * ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) + (r (Nat.sqrt N + 1) (2 * U + 1)).cells
  depth := (r (Nat.sqrt N + 1) (2 * U + 1)).depth + 1

namespace ConvHost

/-! ## One round -/

/-- What the host assumes about the program: it begins with the solver's program and holds the two
helpers. -/
structure Ctx (P R : Program) (pET pSqrt pFill : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop where
  sol : Solves etTask P pET T r
  sqrt : (P ++ R)[pSqrt]? = some sqrtBody
  fill : (P ++ R)[pFill]? = some convFillBody

/-- What the rounds assume: the input lies below the free pointer, N < t², and the limits allow for
the need of the host, written with t. -/
structure Ready (lim : Limits) (r : ℕ → ℕ → Need) (d : ℕ) (x : VecInst) (μ : ℕ → ℤ) (fr t : ℕ) :
    Prop where
  pre : x.Pre μ fr
  lenLt : x.N < t * t
  word : ((r t (2 * x.U + 1)).word : ℤ) + 3 * x.N + 2 * x.U + 2 * (t * t) + 2 * t + 5 ≤ lim.word
  cells : fr + (3 * (t * t) + (r t (2 * x.U + 1)).cells) ≤ lim.space
  addr : (lim.space : ℤ) ≤ lim.word
  depth : d + ((r t (2 * x.U + 1)).depth + 1) ≤ lim.depth

/-- The arguments of convFill for instance number s: the three matrices follow each other at the
free pointer, and the filler is 2U + 1. -/
def fillArgs (x : VecInst) (fr t s : ℕ) : ConvFill.Args :=
  ⟨t, x.N, s, 2 * x.U + 1, x.a, fr, fr + t * t, fr + 2 * (t * t), x.X⟩

/-- Instance number s of the reduction, at the free pointer. -/
def inst (x : VecInst) (fr t s : ℕ) : TriInst :=
  ⟨t, 2 * x.U + 1, fr, fr + t * t, fr + 2 * (t * t), convAB t x.N (2 * x.U + 1) x.X,
    convBC t x.N s (2 * x.U + 1) x.X, convAC t x.N s (2 * x.U + 1) x.X⟩

/-- Instance number s has a zero triangle. -/
def Hit (x : VecInst) (t s : ℕ) : Prop :=
  (triOf t (inst x 0 t s).AB (inst x 0 t s).BC (inst x 0 t s).AC).HasZeroTriangle

/-- The local variables in round s. -/
abbrev locals (x : VecInst) (fr t s : ℕ) (found res : ℤ) : List ℤ :=
  [x.N, x.U, x.a, fr, t, s, found, res, (t * t : ℕ), 2 * x.U + 1]

variable {P R : Program} {pET pSqrt pFill : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {lim : Limits}
  {d : ℕ} {x : VecInst} {μ μ' : ℕ → ℤ} {fr t s : ℕ}

/-- There is at least one vertex per part. -/
private theorem Ready.one_le (H : Ready lim r d x μ fr t) : 1 ≤ t :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using H.lenLt

/-- The numbers of the input are bounded by 2U + 1. -/
private theorem Ready.input_le (H : Ready lim r d x μ fr t) : AbsLe x.X ((2 * x.U + 1 : ℕ) : ℤ) :=
  fun e he => (H.pre.le e he).trans (by push_cast; omega)

/-- The filler is bounded by 2U + 1. -/
private theorem abs_filler_le (x : VecInst) : |2 * (x.U : ℤ) + 1| ≤ ((2 * x.U + 1 : ℕ) : ℤ) := by
  rw [abs_of_nonneg (by positivity)]
  push_cast
  exact le_rfl

/-- convFill can be called in every round. -/
private theorem fill_ctx (H : Ready lim r d x μ fr t) (hk : Kept μ μ' fr) (hs : s < 2 * t) :
    ConvFill.Ctx lim μ' (fillArgs x fr t s) (2 * x.U + 1) where
  side := H.one_le
  addr := H.addr
  input := H.pre.seg.of_sameOn hk fun i hi => by have := H.pre.below; have := H.pre.len; omega
  len := H.pre.len
  belowAB := H.pre.below
  belowBC := le_rfl
  belowAC := by simp only [fillArgs]; omega
  space := by have := H.cells; simp only [fillArgs]; omega
  inputLe := H.input_le
  fillerLe := abs_filler_le x
  valueLe := by have := H.word; have := mul_self_nonneg (t : ℤ); push_cast; omega
  indexLe := by have := H.word; simp only [fillArgs]; push_cast; omega

/-- After convFill the instance lies in the memory. -/
private theorem inst_pre {μ₁ : ℕ → ℤ} (H : Ready lim r d x μ fr t)
    (hpost : ConvFill.Post (fillArgs x fr t s) μ' μ₁) :
    (inst x fr t s).Pre μ₁ (fr + 3 * (t * t)) where
  n_pos := H.one_le
  U_pos := by simp [inst]
  lenAB := by simp [inst]
  lenBC := by simp [inst]
  lenAC := by simp [inst]
  segAB := hpost.segAB
  segBC := hpost.segBC
  segAC := hpost.segAC
  leAB := abs_convAB_le H.input_le (abs_filler_le x)
  leBC := abs_convBC_le H.input_le (abs_filler_le x)
  leAC := abs_convAC_le H.input_le (abs_filler_le x)
  belowAB := by simp only [inst]; omega
  belowBC := by simp only [inst]; omega
  belowAC := by simp only [inst]; omega

/-- The limits allow for the solver, after the three matrices and one level of calls down. -/
private theorem solver_ok (H : Ready lim r d x μ fr t) :
    (r t (2 * x.U + 1)).Ok lim (fr + 3 * (t * t)) (d + 1) where
  word := by have := H.word; have := mul_self_nonneg (t : ℤ); omega
  cells := by have := H.cells; omega
  space := H.addr
  depth := by have := H.depth; omega

/-- **One round**: if Found says whether one of the instances before s has a zero triangle, then
afterwards it says so of the instances up to s.  No cell below the free pointer changes. -/
private theorem round_spec (C : Ctx P R pET pSqrt pFill T r) (H : Ready lim r d x μ fr t)
    (hk : Kept μ μ' fr) (hs : s < 2 * t) (res : ℤ) :
    Ends lim (P ++ R) d (c3Round pET pFill)
      ⟨frame (locals x fr t s (flag (∃ s' < s, Hit x t s')) res), μ'⟩ (c3RoundTime T t x.U)
      fun σ' => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals x fr t s (flag (∃ s' < s + 1, Hit x t s')) res'), μ''⟩ ∧
          Kept μ μ'' fr := by
  obtain ⟨hword, hcells, haddr, hdepth⟩ := And.intro H.word (And.intro H.cells
    (And.intro H.addr H.depth))
  have harea := mul_self_nonneg (t : ℤ)
  unfold c3Round c3RoundTime
  -- Answer := convFill(t, N, s, 2U + 1, x, fr, fr + t², fr + 2t²)
  refine Ends.callToThen (T' := convFillTime t) (convFill_meets C.fill (fill_ctx H hk hs)) ?_
    (by light_side [fillArgs])
  rintro - μ₁ hpost
  -- Answer := et(t, 2U + 1, fr, fr + t², fr + 2t², fr + 3t²)
  refine Ends.callToThen (T' := T t (2 * x.U + 1)) (C.sol.meets R (inst x fr t s) (fr + 3 * (t * t))
    (inst_pre H hpost) (solver_ok H)) ?_ (by light_side [etTask, inst])
  rintro res' μ₂ ⟨hres, hk₂⟩
  replace hres : res' = flag (Hit x t s) := hres
  -- both calls write only from the free pointer on
  have hkept : Kept μ μ₂ fr := (hk.then hpost.same fun b hb => ⟨hb, Or.inl hb⟩).then hk₂
    fun b hb => ⟨hb, by omega⟩
  -- if Answer = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- Found := 1
    have hit : Hit x t s := flag_eq_one_iff.1 (by simpa [hres] using hyes)
    exact Ends.setTo 1
      ⟨res', μ₂, by rw [flag_of (Nat.exists_lt_succ_right.2 (Or.inr hit))]; rfl, hkept⟩
  · have miss : ¬ Hit x t s := fun hit => hno (by simp [hres, flag_of hit])
    exact Ends.skip
      ⟨res', μ₂, by rw [flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left miss))]; rfl, hkept⟩

/-! ## The host -/

/-- The invariant of the loop: before round s, Found says whether one of the instances before s has
a zero triangle, and no cell below the free pointer has changed. -/
def LoopInv (x : VecInst) (μ : ℕ → ℤ) (fr t s : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr t s (flag (∃ s' < s, Hit x t s')) res), μ'⟩ ∧ Kept μ μ' fr

/-- The need of the host allows for the rounds. -/
private theorem ready (hpre : x.Pre μ fr) (hok : (c3Need r x.N x.U).Ok lim fr d) :
    Ready lim r d x μ fr (Nat.sqrt x.N + 1) where
  pre := hpre
  lenLt := Nat.lt_succ_sqrt x.N
  word := by have := hok.word; simp only [c3Need] at this; push_cast at this ⊢; omega
  cells := hok.cells
  addr := hok.space
  depth := hok.depth

end ConvHost

open ConvHost in
/-- **The host is correct**, in every program that begins with the solver's and contains the two
helpers. -/
private theorem c3_spec {P R : Program} {pET pSqrt pFill : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (C : Ctx P R pET pSqrt pFill T r) {lim : Limits} {d : ℕ} {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (c3Need r x.N x.U).Ok lim fr d) :
    Ends lim (P ++ R) d (c3Body pET pSqrt pFill) ⟨frame [(x.N : ℤ), x.U, x.a, fr], μ⟩
      (c3Time T x.N x.U) fun σ' =>
        σ'.loc 0 = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have H := ready hpre hok
  unfold c3Time
  have hroot : Nat.sqrt x.N ≤ x.N := Nat.sqrt_le_self _
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.sqrt x.N + 1 := ⟨_, rfl⟩
  rw [← ht] at H ⊢
  obtain ⟨hword, hdepth⟩ := And.intro H.word H.depth
  have harea := mul_self_nonneg (t : ℤ)
  unfold c3Body
  -- Side := sqrt(N)
  light_call (sqrt_meets (K := x.N) C.sqrt μ (by push_cast; omega)) with _ μ₀ ⟨rfl, hμ⟩
  obtain rfl := hμ.symm
  -- Side := Side + 1; Area := Side * Side; Filler := 2 * Bound + 1; Found := 0
  light_set t
  light_set (t * t : ℕ)
  light_set (2 * (x.U : ℤ) + 1)
  light_set 0
  -- for Inst < 2 * Side
  refine Ends.next _ (Ends.for (LoopInv x μ fr t) (2 * t) (c3RoundTime T t x.U)
    ?start ?round ?done ?bound (hT := le_rfl))
  case start =>
    exact ⟨0, μ, by simp [update_frame_setLocal, locals, flag_of_not], SameOn.refl⟩
  case round =>
    rintro s _ hs - ⟨res, μ', rfl, hk⟩
    refine (round_spec C H hk hs res).mono le_rfl ?_
    rintro _ ⟨res', μ'', rfl, hk'⟩
    exact ⟨rfl, res', μ'', by simp [update_frame_setLocal, locals], hk'⟩
  case done =>
    rintro _ - ⟨res, μ', rfl, hk⟩
    -- Len := Found: the result
    exact Ends.setTo (flag (∃ s' < 2 * t, Hit x t s'))
      ⟨flag_congr (convolution3SUM_vecOf_iff hpre.N_pos H.lenLt (by positivity) hpre.le).symm, hk⟩
  case bound =>
    rintro s _ - - ⟨res, μ', rfl, -⟩
    exact ⟨by light_side, by simp⟩

/-! ## The need is polynomially bounded -/

/-- The need of the host is polynomially bounded if the need of the solver is. -/
private theorem polyNeed_c3Need {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (c3Need r) := by
  unfold c3Need
  poly_need [hr.word, hr.cells, hr.depth]

/-- **Convolution-3SUM from Exact Triangle**: the host makes a solver of Convolution-3SUM from every
solver of Exact Triangle. -/
theorem isHost_c3 : IsHost etTask c3Task c3Time c3Need := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_c3Need hr⟩
  refine ⟨[sqrtBody, convFillBody, c3Body p P.length (P.length + 1)], P.length + 2,
    c3Body p P.length (P.length + 1), by simp, ?_⟩
  intro R lim d x μ fr hpre hok
  rw [List.append_assoc]
  exact c3_spec ⟨hsol, by simp, by simp⟩ hpre hok

end Light.Sec3
