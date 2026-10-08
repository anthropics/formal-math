/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Memory

/-!
# The pruned recursion (Section 2.4.2), recursive as printed

pruned(n, ea, eb, l, len, out, sp, p10).  The set S passed to the call is the increasing list of len
codes at l; ea and eb are the addresses at which the parts of the two encodings below the current
vertex begin; the array that is returned is written to the len cells from out, in the order of the
list.  The frame of a call with n ≥ 1 starts at sp: 11 cells for the bounds of the ten slices, len
cells for the codes without their first digits, len cells for the list of a child, len cells for the
values of a child.

(1) If n = 0: the product of the two numbers looked up, for each code of the list
    (`prunedBody_ends_zero`).
(2) The slices S_z are segments of the list (segBounds); S_λ is the merge of the slice at z_ij and
    the slice at z₀ (`prunedSlice_ends`, then union).
(3) For each term λ with S_λ ≠ ∅: the recursive call.
(4) The slice of the result at z_ij is C_{P_ij} restricted to S_{z_ij} (pick, writing); the slice at
    z₀ is the sum of the ten C_λ restricted to S_{z₀} (pick, adding, after the cells have been
    cleared).  Steps (3) and (4) for one term are `prunedChild_ends`.

One round of the loop over the ten terms is `prunedRound_ends`; the case n ≥ 1 is
`prunedSetup_ends` followed by the loop (`prunedBody_ends_succ`); `PrunedCtx.entry` is the induction
on n.  What the calls do to the memory is proved in Pruned/Memory.lean; here each call is one step.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace PrunedLocal

/-- The number n of levels that are left. -/
abbrev NN : ℕ := 0
/-- Where the part of the first encoding below the current vertex begins. -/
abbrev PA : ℕ := 1
/-- Where the part of the second encoding below the current vertex begins. -/
abbrev PB : ℕ := 2
/-- The list of the codes that are passed to the call. -/
abbrev PL : ℕ := 3
/-- The length of that list. -/
abbrev LEN : ℕ := 4
/-- Where the values are written. -/
abbrev OUT : ℕ := 5
/-- The frame of the call; it begins with the bounds of the ten slices. -/
abbrev SP : ℕ := 6
/-- The table of the powers of ten. -/
abbrev P10 : ℕ := 7
/-- 10^(n-1); for n = 0 the product of the two numbers looked up. -/
abbrev PW : ℕ := 8
/-- Results of calls that are not used. -/
abbrev RES : ℕ := 9
/-- The codes without their first digits. -/
abbrev COD : ℕ := 10
/-- The list of the child. -/
abbrev CH : ℕ := 11
/-- The values of the child. -/
abbrev VAL : ℕ := 12
/-- The frame of the child. -/
abbrev NXT : ℕ := 13
/-- The position of the slice at z₀. -/
abbrev Z0 : ℕ := 14
/-- The length of the slice at z₀. -/
abbrev NZ0 : ℕ := 15
/-- The term λ. -/
abbrev LAM : ℕ := 16
/-- The position of the slice at the output variable of λ. -/
abbrev POS : ℕ := 17
/-- The length of that slice (0 for λ = P₀). -/
abbrev NPOS : ℕ := 18
/-- The length of the list of the child. -/
abbrev NCH : ℕ := 19

end PrunedLocal

open PrunedLocal

/-- Step (2), first half: the position and the length of the slice at the output variable of λ. -/
def prunedSlice : Stmt :=
  .set POS (M (v SP +' v LAM)) ;;
  .ite (v LAM <' k 9) (.set NPOS (M (v SP +' v LAM +' k 1) -' v POS)) (.set NPOS (k 0))

/-- Steps (3) and (4) for a term λ with S_λ ≠ ∅. -/
def prunedChild : Stmt :=
  .call pPruned [v NN -' k 1, v PA +' v LAM *' v PW, v PB +' v LAM *' v PW, v CH, v NCH, v VAL,
    v NXT, v P10] RES ;;
  .call pPick [v COD +' v POS, v NPOS, v CH, v NCH, v VAL, v OUT +' v POS, k 0] RES ;;
  .call pPick [v COD +' v Z0, v NZ0, v CH, v NCH, v VAL, v OUT +' v Z0, k 1] RES

/-- One round of the loop over the ten terms. -/
def prunedRound : Stmt :=
  prunedSlice ;;
  .call pUnion [v COD +' v POS, v NPOS, v COD +' v Z0, v NZ0, v CH] NCH ;;
  .ite (k 0 <' v NCH) prunedChild .skip ;;
  .set LAM (v LAM +' k 1)

/-- What a call with n ≥ 1 does before the loop: the slices are found, the parts of the frame get
their addresses, and the cells of the slice at z₀ are cleared. -/
def prunedSetup : Stmt :=
  .set PW (M (v P10 +' (v NN -' k 1))) ;;
  .call pSegBounds [v PL, v LEN, v PW, v SP] RES ;;
  .set COD (v SP +' k 11) ;;
  .set CH (v COD +' v LEN) ;;
  .set VAL (v CH +' v LEN) ;;
  .set NXT (v VAL +' v LEN) ;;
  .set Z0 (M (v SP +' k 9)) ;;
  .set NZ0 (v LEN -' v Z0) ;;
  .call pFill [v OUT +' v Z0, v NZ0, k 0] RES ;;
  .set LAM (k 0)

/-- pruned(n, ea, eb, l, len, out, sp, p10). -/
def prunedBody : Stmt :=
  .ite (v NN =' k 0)
    (.set PW (M (v PA) *' M (v PB)) ;;
     .call pFill [v OUT, v LEN, v PW] RES)
    (prunedSetup ;;
     .while (v LAM <' k 10) prunedRound)

/-! ## What the proofs assume -/

/-- What the recursion assumes about its surroundings: the limits, its own place in the program, and
the entries of the four helpers, all with the constant h. -/
structure PrunedCtx (lim : Limits) (P : Program) (h : ℕ) : Prop where
  std : Std lim
  body : P[pPruned]? = some prunedBody
  fill : FillSpec lim P h
  segBounds : SegBoundsSpec lim P h
  union : UnionSpec lim P h
  pickSet : PickSetSpec lim P h
  pickAdd : PickAddSpec lim P h

/-- What a call of pruned achieves. -/
def PrunedPost (n : ℕ) (x : PrunedArgs) (μ : ℕ → ℤ) (_ : ℤ) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' x.out (prunedList x.EA x.EB n x.base x.codes) ∧
    SameOutside2 μ μ' x.out x.codes.length x.sp (n * (3 * x.codes.length + 11))

/-- What the recursion may assume about the calls with n levels left: what `PrunedSpec` says, with
the running time of the program. -/
def PrunedIH (lim : Limits) (P : Program) (h n : ℕ) : Prop :=
  ∀ (x : PrunedArgs) (μ : ℕ → ℤ), PrunedPre lim μ n x →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pPruned d (x.vals n) μ (prunedTime h n x.codes) (PrunedPost n x μ)

variable {lim : Limits} {P : Program} {h d n t : ℕ} {x : PrunedArgs} {μ μ' : ℕ → ℤ}

/-! ## Step (1) -/

/-- The case n = 0. -/
theorem prunedBody_ends_zero (C : PrunedCtx lim P h) (hd : d + 1 ≤ lim.depth)
    (pre : PrunedPre lim μ 0 x) :
    Ends lim P d prunedBody ⟨frame (x.vals 0), μ⟩ (prunedTime h 0 x.codes)
      fun σ' => PrunedPost 0 x μ (σ'.loc 0) σ'.mem := by
  have std := C.std
  light_facts std pre
  have hreadA : μ (x.aEA + x.base) = x.EA.getD x.base 0 := pre.encA.getD (by omega) 0
  have hreadB : μ (x.aEB + x.base) = x.EB.getD x.base 0 := pre.encB.getD (by omega) 0
  obtain ⟨hlow, hhigh⟩ := abs_le.mp ((pre.abs_getD_mul_le x.base).trans
    (by simpa using pre.word : x.A * x.B ≤ lim.word))
  simp only [List.getD_eq_getElem?_getD] at hlow hhigh
  unfold prunedBody prunedTime
  -- if n = 0
  refine Ends.iteLast (fun _ => ?_) (fun hne => absurd (by simp) hne)
  -- pw := mem[ea] * mem[eb]
  light_set (x.EA.getD x.base 0 * x.EB.getD x.base 0) using hreadA, hreadB
  -- fill(out, len, pw)
  light_call (C.fill x.out x.codes.length (x.EA.getD x.base 0 * x.EB.getD x.base 0) μ
    (by omega) (by omega) _ (by omega)) with r μ₁ ⟨hvalues, hrest⟩
  exact ⟨by simpa [prunedList] using hvalues, by light_keep⟩

/-! ## One round of the loop -/

/-- The state in the loop over the ten terms: t is the term; res, pos, npos and nch are what the
locals RES, POS, NPOS and NCH hold. -/
abbrev roundState (n : ℕ) (x : PrunedArgs) (t : ℕ) (res pos npos nch : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame (x.vals (n + 1) ++ [((10 ^ n : ℕ) : ℤ), res, (x.sp + 11 : ℕ),
    (x.sp + 11 + x.codes.length : ℕ), (x.sp + 11 + 2 * x.codes.length : ℕ),
    (x.sp + 11 + 3 * x.codes.length : ℕ), segStart n x.codes 9, (sliceList n 9 x.codes).length, t,
    pos, npos, nch]), μ'⟩

/-- The invariant of the loop, before round t. -/
def RoundInv (n : ℕ) (x : PrunedArgs) (μ : ℕ → ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ (res pos npos nch : ℤ) (μ' : ℕ → ℤ),
    σ = roundState n x t res pos npos nch μ' ∧ PrunedInv n x μ μ' t

/-- Step (2), first half: the slice at the output variable of the term t begins at
segStart n codes t and is the first list of the round. -/
theorem prunedSlice_ends (std : Std lim) (pre : PrunedPre lim μ (n + 1) x)
    (inv : PrunedInv n x μ μ' t) (ht : t < 10) (res pos npos nch : ℤ) :
    Ends lim P d prunedSlice (roundState n x t res pos npos nch μ') 18
      (· = roundState n x t res (segStart n x.codes t) (firstList n t x.codes).length nch
        μ') := by
  light_facts std (pre.round ht)
  have hstart := pre.sizes.start_le t (by omega)
  have hread := inv.bounds t (by omega)
  unfold prunedSlice
  -- pos := mem[sp + λ]
  light_set (segStart n x.codes t : ℕ) using hread
  -- if λ < 9
  refine Ends.iteLast (fun h9 => ?_) (fun h9 => ?_)
  · replace h9 : t < 9 := by simpa using h9
    have hnext := inv.bounds (t + 1) (by omega)
    have hlen := pre.sizes.slice_le t ht
    rw [segStart_succ] at hnext
    have haddr : ((x.sp : ℤ) + t + 1).toNat = x.sp + (t + 1) := by omega
    -- npos := mem[sp + λ + 1] - pos
    light_set ((firstList n t x.codes).length : ℕ) using haddr, hnext, firstList, h9
    rfl
  · replace h9 : ¬ t < 9 := by simpa using h9
    -- npos := 0
    light_set ((firstList n t x.codes).length : ℕ) using firstList, h9
    rfl

/-- Steps (3) and (4) for a term t whose list is not empty: the recursive call and the two calls of
pick lead to the invariant of the loop (`RoundInv`) before round t + 1. -/
theorem prunedChild_ends (C : PrunedCtx lim P h) (ih : PrunedIH lim P h n)
    (hd : d + (n + 1 + 1) ≤ lim.depth) (pre : PrunedPre lim μ (n + 1) x)
    (inv : PrunedInv n x μ μ' t) (ht : t < 10) {μ₁ : ℕ → ℤ} (m : Merged n x t μ' μ₁) (res : ℤ) :
    Ends lim P d prunedChild
      (roundState n x t res (segStart n x.codes t) (firstList n t x.codes).length
        (childList n t x.codes).length μ₁)
      (childTime h (prunedTime h n) n t x.codes)
      fun σ' => ∃ (res' : ℤ) (μ₄ : ℕ → ℤ),
        σ' = roundState n x t res' (segStart n x.codes t) (firstList n t x.codes).length
          (childList n t x.codes).length μ₄ ∧
        PrunedInv n x μ μ₄ (t + 1) := by
  have std := C.std
  light_facts std pre (pre.round ht)
  have hcast : (t : ℤ) * 10 ^ n = ((t * 10 ^ n : ℕ) : ℤ) := by push_cast; rfl
  have hsorted := pairwise_childList (n := n) pre.sorted t
  unfold prunedChild childTime
  -- res := pruned(n - 1, ea + λ * pw, eb + λ * pw, ch, nch, val, nxt, p10)
  light_call (ih (x.child n t) μ₁ (pre.child inv ht m) _ (by omega)) with r₂ μ₂ ⟨hvalues, hframe⟩
  rw [PrunedArgs.child, prunedList_eq_map x.EA x.EB n _ hsorted (lt_of_mem_childList pre.sorted t)]
    at hvalues
  dsimp only [PrunedArgs.child] at hframe
  have ret : Returned n x t μ₁ μ₂ := ⟨hvalues, by light_keep⟩
  -- res := pick(cod + pos, npos, ch, nch, val, out + pos, 0)
  light_call (C.pickSet _ μ₂ (ret.pickFirst pre inv ht m) _ (by omega))
    with r₃ μ₃ ⟨hvalues₃, hrest₃⟩
  dsimp only [PrunedArgs.pick] at hvalues₃ hrest₃
  rw [restrictList_map _ hsorted (pairwise_firstList pre.sorted) firstList_subset_childList]
    at hvalues₃
  have rst : Restricted n x t μ₂ μ₃ := ⟨hvalues₃, hrest₃⟩
  -- res := pick(cod + z0, nz0, ch, nch, val, out + z0, 1)
  refine Ends.callTo (C.pickAdd _ _ μ₃ (rst.pickLast pre inv ht m ret) (rst.acc pre inv ht m ret)
    (by simp) ?_ _ (by omega)) ?_
  · rw [PrunedArgs.pick, zipWith_add_pvSum x n t pre.sorted]
    exact pre.abs_pvSum_le (by omega)
  rintro r₄ μ₄ ⟨hvalues₄, hrest₄⟩
  rw [PrunedArgs.pick, zipWith_add_pvSum x n t pre.sorted] at hvalues₄
  exact ⟨r₄, μ₄, rfl, rst.next pre inv ht m ret hvalues₄ hrest₄⟩

/-- **One round of the loop**: steps (2), (3) and (4) for the term t. -/
theorem prunedRound_ends (C : PrunedCtx lim P h) (ih : PrunedIH lim P h n)
    (hd : d + (n + 1 + 1) ≤ lim.depth) (pre : PrunedPre lim μ (n + 1) x) (ht : t < 10)
    {σ : State} (hσ : RoundInv n x μ t σ) :
    Ends lim P d prunedRound σ (roundTime h (prunedTime h n) n t x.codes)
      (RoundInv n x μ (t + 1)) := by
  obtain ⟨res, pos, npos, nch, μ', rfl, inv⟩ := hσ
  have std := C.std
  light_facts std (pre.round ht)
  unfold prunedRound roundTime
  -- the slice at the output variable of λ
  light_piece (prunedSlice_ends C.std pre inv ht res pos npos nch) with _ rfl
  -- nch := union(cod + pos, npos, cod + z0, nz0, ch)
  light_call (C.union (x.sp + 11 + segStart n x.codes t)
    (x.sp + 11 + segStart n x.codes 9) (x.sp + 11 + x.codes.length) _ _ μ' (inv.first ht)
    (inv.segs 9 (by omega)) (by omega) (by omega) (by omega) _ (by omega))
    with _ μ₁ ⟨rfl, hchild, hrest⟩
  rw [← childList_eq_mergeUnion n x.codes ht] at hchild ⊢
  have m : Merged n x t μ' μ₁ := ⟨hchild, hrest⟩
  -- if 0 < nch
  refine Ends.iteThen (fun hpos => ?_) (fun hzero => ?_)
  · have hne : childList n t x.codes ≠ [] := by
      rintro hnil
      simp [hnil] at hpos
    rw [if_neg hne]
    -- steps (3) and (4)
    light_piece (prunedChild_ends C ih hd pre inv ht m res) with _ ⟨res', μ₄, rfl, inv'⟩
    -- λ := λ + 1
    light_set (t + 1 : ℕ)
    exact ⟨_, _, _, _, μ₄, rfl, inv'⟩
  · have hnil : childList n t x.codes = [] := by
      simpa using hzero
    -- skip; λ := λ + 1
    refine Ends.next 0 (Ends.skip ?_)
    light_set (t + 1 : ℕ)
    exact ⟨_, _, _, _, μ₁, rfl, inv.next_of_nil pre ht m hnil⟩

/-! ## The case n ≥ 1 -/

/-- The running time of the loop over the ten terms. -/
def loopTime (h n : ℕ) (codes : List ℕ) : ℕ :=
  ∑ t ∈ Finset.range 10, ((v LAM <' k 10).cost + 1 + roundTime h (prunedTime h n) n t codes)
    + ((v LAM <' k 10).cost + 1)

/-- The loop, segBounds, fill and 66 more steps are the time of the call. -/
theorem loopTime_add_le (h n : ℕ) (codes : List ℕ) :
    loopTime h n codes + 66 + h * (codes.length + 11) + h * ((sliceList n 9 codes).length + 1)
      ≤ prunedTime h (n + 1) codes := by
  rw [prunedTime, List.sum_map_range, loopTime]
  simp only [Cond.cost, Expr.cost, Nat.reduceAdd]
  omega

/-- Before the loop: afterwards the invariant of the loop (`RoundInv`) holds for t = 0. -/
theorem prunedSetup_ends (C : PrunedCtx lim P h) (hd : d + (n + 1 + 1) ≤ lim.depth)
    (pre : PrunedPre lim μ (n + 1) x) :
    Ends lim P d prunedSetup ⟨frame (x.vals (n + 1)), μ⟩
      (50 + h * (x.codes.length + 11) + h * ((sliceList n 9 x.codes).length + 1))
      (RoundInv n x μ 0) := by
  have std := C.std
  light_facts std pre (pre.round (t := 0) (by omega))
  have hread : μ (x.p10 + n) = (10 : ℤ) ^ n := by
    simpa [powList] using pre.powers n (by simp [powList]; omega)
  have hpw : (10 : ℤ) ^ n ≤ lim.word :=
    le_trans (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 10) (by omega : n ≤ n + 2))
      pre.pow
  have hpw0 : (0 : ℤ) ≤ 10 ^ n := by positivity
  have haddr : ((x.sp : ℤ) + 9).toNat = x.sp + 9 := by omega
  unfold prunedSetup
  -- pw := mem[p10 + (n - 1)]
  light_set (10 ^ n : ℕ) using hread
  -- res := segBounds(l, len, pw, sp)
  light_call (C.segBounds n x.l x.sp x.codes μ pre.list pre.sorted pre.lt (by omega)
    (by omega) pre.pow _ (by omega)) with r μa ⟨hbounds, hsegs, hresta⟩
  -- cod := sp + 11; ch := cod + len; val := ch + len; nxt := val + len
  light_set (x.sp + 11 : ℕ)
  light_set (x.sp + 11 + x.codes.length : ℕ)
  light_set (x.sp + 11 + 2 * x.codes.length : ℕ)
  light_set (x.sp + 11 + 3 * x.codes.length : ℕ)
  -- z0 := mem[sp + 9]; nz0 := len - z0
  light_set (segStart n x.codes 9 : ℕ) using haddr, hbounds 9 (by omega)
  light_set ((sliceList n 9 x.codes).length : ℕ)
  -- res := fill(out + z0, nz0, 0)
  light_call (C.fill (x.out + segStart n x.codes 9) (sliceList n 9 x.codes).length 0 μa
    (by omega) (by omega) _ (by omega)) with r' μb ⟨hzero, hrestb⟩
  -- λ := 0
  light_set (0 : ℕ)
  exact ⟨r', 0, 0, 0, μb, by rw [roundState, ← frame_append_zeros _ 3]; rfl,
    PrunedInv.start pre hbounds hsegs hresta hzero hrestb⟩

/-- **The case n + 1**: the frame is set up, and the loop runs through the ten terms. -/
theorem prunedBody_ends_succ (C : PrunedCtx lim P h) (ih : PrunedIH lim P h n)
    (hd : d + (n + 1 + 1) ≤ lim.depth) (pre : PrunedPre lim μ (n + 1) x) :
    Ends lim P d prunedBody ⟨frame (x.vals (n + 1)), μ⟩ (prunedTime h (n + 1) x.codes)
      fun σ' => PrunedPost (n + 1) x μ (σ'.loc 0) σ'.mem := by
  have h100 := C.std.const_le
  have hT := loopTime_add_le h n x.codes
  unfold prunedBody
  -- if n = 0
  refine Ends.iteLast (fun h0 => absurd h0 (by simp; omega)) (fun _ => ?_)
  -- the frame
  refine Ends.next _ ((prunedSetup_ends C hd pre).mono le_rfl fun σ hσ => ?_)
  -- while λ < 10
  refine (Ends.while (RoundInv n x μ) 10 (fun t => roundTime h (prunedTime h n) n t x.codes) hσ
    ?round ?done).mono ?time fun _ hq => hq
  case round =>
    intro t σ ht hσ
    obtain ⟨res, pos, npos, nch, μ', rfl, -⟩ := id hσ
    exact ⟨by light_side, by light_side, prunedRound_ends C ih hd pre ht hσ⟩
  case done =>
    rintro _ ⟨res, pos, npos, nch, μ', rfl, inv⟩
    exact ⟨by light_side, by light_side, inv.result pre.sorted, inv.frame⟩
  case time =>
    change loopTime h n x.codes ≤ _
    light_time

/-! ## The recursion -/

/-- **The pruned recursion meets its entry**, with the constant 50 h + 2000, where h is a common
constant of the four helpers. -/
theorem PrunedCtx.entry (C : PrunedCtx lim P h) : PrunedSpec lim P (50 * h + 2000) := by
  have key : ∀ n, PrunedIH lim P h n := by
    intro n
    induction n with
    | zero => exact fun x μ pre d hd => .of_body C.body (prunedBody_ends_zero C hd pre)
    | succ n ih => exact fun x μ pre d hd => .of_body C.body (prunedBody_ends_succ C ih hd pre)
  exact fun n x μ pre d hd => (key n x μ pre d hd).mono_time (prunedTime_le h n pre.sorted pre.lt)

end Light.Sec2
