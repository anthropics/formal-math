/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.SliceFacts

/-!
# The pruned recursion: what one round does to the memory (Section 2.4.2, steps (2) to (4))

A call of pruned with n + 1 ≥ 1 levels left runs ten rounds, one for each term λ of Schönhage's
identity.  This file has no program in it.  It says what the memory looks like before round t
(`PrunedInv`) and shows that after the four calls of a round `PrunedInv` holds for t + 1.

* Step (3).  If the list of the child is empty, the round is over (`PrunedInv.next_of_nil`).  If
  not, what the recursive call assumes holds (`PrunedPre.child`); its arguments are `x.child n t`.
* Step (4).  What the two calls of pick assume holds (`Returned.pickFirst`, `Restricted.pickLast`),
  and afterwards `PrunedInv` holds for t + 1 (`Restricted.next`).

The memories after the calls are μ₁ (`Merged`), μ₂ (`Returned`), μ₃ (`Restricted`) and μ₄.  Each of
these records says which cells its call may have changed, and `RoundSizes` holds the inequalities
between the places of a round; that a list is still where it was follows from these two.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {n t : ℕ} {x : PrunedArgs} {μ μ' : ℕ → ℤ}

/-- The memory before round number t of the loop: the bounds of the ten slices and the codes without
their first digits are in the frame; the slices of the result at the output variables of the terms
before t are written; the slice at z₀ holds the sum over the terms before t. -/
structure PrunedInv (n : ℕ) (x : PrunedArgs) (μ μ' : ℕ → ℤ) (t : ℕ) : Prop where
  bounds : ∀ z ≤ 10, μ' (x.sp + z) = segStart n x.codes z
  segs : ∀ z < 10, SegN μ' (x.sp + 11 + segStart n x.codes z) (sliceList n z x.codes)
  done : ∀ s < 9, s < t →
    Seg μ' (x.out + segStart n x.codes s)
      ((sliceList n s x.codes).map (prunedValue x.EA x.EB n (x.base + s * 10 ^ n)))
  acc : Seg μ' (x.out + segStart n x.codes 9)
    ((sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base t))
  frame : SameOutside2 μ μ' x.out x.codes.length x.sp ((n + 1) * (3 * x.codes.length + 11))

/-- The bound on the numbers of the first encoding is not negative, because there are such
numbers. -/
theorem PrunedPre.A_nonneg (pre : PrunedPre lim μ n x) : 0 ≤ x.A := by
  have hpos : 0 < 10 ^ n := by positivity
  have hbase : x.base < x.EA.length := by have := pre.partA; omega
  exact (abs_nonneg _).trans (pre.boundA _ (List.getElem_mem hbase))

/-- The bound on the numbers of the second encoding is not negative. -/
theorem PrunedPre.B_nonneg (pre : PrunedPre lim μ n x) : 0 ≤ x.B := by
  have hpos : 0 < 10 ^ n := by positivity
  have hbase : x.base < x.EB.length := by have := pre.partB; omega
  exact (abs_nonneg _).trans (pre.boundB _ (List.getElem_mem hbase))

/-- The product of two encoded numbers is at most A B. -/
theorem PrunedPre.abs_getD_mul_le (pre : PrunedPre lim μ n x) (i : ℕ) :
    |x.EA.getD i 0 * x.EB.getD i 0| ≤ x.A * x.B := by
  rw [abs_mul]
  exact mul_le_mul (AbsLe.abs_getD_le pre.A_nonneg pre.boundA i)
    (AbsLe.abs_getD_le pre.B_nonneg pre.boundB i)
    (abs_nonneg _) pre.A_nonneg

/-- If 10^(n+1) numbers of size X add up to at most W, then so do k 10^n of them for k ≤ 10. -/
theorem mul_ten_pow_mul_le (n : ℕ) {k : ℕ} (hk : k ≤ 10) {X W : ℤ} (hX : 0 ≤ X)
    (h : 10 ^ (n + 1) * X ≤ W) : k * (10 ^ n * X) ≤ W := by
  have hk' : (k : ℤ) * 10 ^ n ≤ 10 ^ (n + 1) := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (by positivity)
  calc (k : ℤ) * (10 ^ n * X) = (k * 10 ^ n) * X := by ring
    _ ≤ 10 ^ (n + 1) * X := mul_le_mul_of_nonneg_right hk' hX
    _ ≤ W := h

/-- The first list lies in the frame. -/
theorem PrunedInv.first (inv : PrunedInv n x μ μ' t) (ht : t < 10) :
    SegN μ' (x.sp + 11 + segStart n x.codes t) (firstList n t x.codes) := by
  unfold firstList
  split_ifs
  · exact inv.segs t ht
  · simp [SegN]

/-! ## Sizes -/

/-- The arithmetic of a frame: where the slices begin and end. -/
structure PrunedSizes (n : ℕ) (codes : List ℕ) : Prop where
  start_le : ∀ z ≤ 10, segStart n codes z ≤ codes.length
  slice_le : ∀ z < 10, segStart n codes z + (sliceList n z codes).length ≤ codes.length

/-- The ten slices lie within the list, because together they make it up. -/
theorem PrunedPre.sizes (pre : PrunedPre lim μ (n + 1) x) : PrunedSizes n x.codes := by
  have hstart : ∀ z ≤ 10, segStart n x.codes z ≤ x.codes.length := fun z hz =>
    segStart_ten pre.sorted pre.lt ▸ segStart_mono n x.codes hz
  refine ⟨hstart, fun z hz => ?_⟩
  rw [← segStart_succ]
  exact hstart _ (by omega)

/-- The arithmetic of round t: the two lists that are merged lie one behind the other among the
codes, the list of the child is no longer than the two together, the stack of the child is no larger
than a stack for all codes, the frame and that stack fit in the memory, and the part of an encoding
below the child t lies within the part below the current vertex. -/
structure RoundSizes (lim : Limits) (n : ℕ) (x : PrunedArgs) (t : ℕ) : Prop where
  first : segStart n x.codes t + (firstList n t x.codes).length ≤ segStart n x.codes 9
  nine : segStart n x.codes 9 + (sliceList n 9 x.codes).length = x.codes.length
  child : (childList n t x.codes).length
    ≤ (firstList n t x.codes).length + (sliceList n 9 x.codes).length
  stack : n * (3 * (childList n t x.codes).length + 11) ≤ n * (3 * x.codes.length + 11)
  room : x.sp + (n * (3 * x.codes.length + 11) + (3 * x.codes.length + 11)) ≤ lim.space
  part : t * 10 ^ n + 10 ^ n ≤ 10 ^ (n + 1)

/-- The inequalities of round t follow from what the call assumes. -/
theorem PrunedPre.round (pre : PrunedPre lim μ (n + 1) x) (ht : t < 10) :
    RoundSizes lim n x t := by
  have first := segStart_add_firstList_le n x.codes ht
  have nine : segStart n x.codes 9 + (sliceList n 9 x.codes).length = x.codes.length := by
    rw [← segStart_succ, segStart_ten pre.sorted pre.lt]
  have child := length_childList_le n x.codes ht
  have room := pre.space
  rw [Nat.succ_mul] at room
  exact ⟨first, nine, child, Nat.mul_le_mul_left _ (by omega), room,
    pow_succ' 10 n ▸ Nat.mul_add_le_mul ht le_rfl⟩

/-! ## From one round to the next -/

/-- `PrunedInv` holds for t + 1 in a memory μ₄ if the frame, the earlier results and the cells that
do not belong to the call are as before round t, the slice at the output variable of the term t is
written, and the term t is added to the slice at z₀. -/
theorem PrunedInv.next (inv : PrunedInv n x μ μ' t) (sz : PrunedSizes n x.codes) {μ₄ : ℕ → ℤ}
    (hframe : SameOn (Inside x.sp (11 + x.codes.length)) μ' μ₄)
    (hdone : SameOn (Inside x.out (segStart n x.codes t)) μ' μ₄)
    (hrest : SameOutside2 μ' μ₄ x.out x.codes.length x.sp ((n + 1) * (3 * x.codes.length + 11)))
    (hnew : t < 9 →
      Seg μ₄ (x.out + segStart n x.codes t)
        ((sliceList n t x.codes).map (prunedValue x.EA x.EB n (x.base + t * 10 ^ n))))
    (hacc : Seg μ₄ (x.out + segStart n x.codes 9)
      ((sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base (t + 1)))) :
    PrunedInv n x μ μ₄ (t + 1) := by
  have hbefore := inv.frame
  refine ⟨fun z hz => (hframe _ ⟨by omega, by omega⟩).trans (inv.bounds z hz), fun z hz => ?_,
    fun s hs9 hst => ?_, hacc, by light_keep⟩
  · have := sz.slice_le z hz
    exact (inv.segs z hz).keep
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hst with hlt | rfl
    · have hmono := segStart_mono n x.codes (show s + 1 ≤ t by omega)
      rw [segStart_succ] at hmono
      exact (inv.done s hs9 hlt).keep
    · exact hnew hs9

/-- Before the first round: segBounds has filled the frame (memory μa), and the cells of the slice
at z₀ have been cleared (memory μb). -/
theorem PrunedInv.start (pre : PrunedPre lim μ (n + 1) x) {μa μb : ℕ → ℤ}
    (hbounds : ∀ z ≤ 10, μa (x.sp + z) = segStart n x.codes z)
    (hsegs : ∀ z < 10, SegN μa (x.sp + 11 + segStart n x.codes z) (sliceList n z x.codes))
    (hresta : SameOutside μ μa x.sp (11 + x.codes.length))
    (hzero : Seg μb (x.out + segStart n x.codes 9)
      (List.replicate (sliceList n 9 x.codes).length 0))
    (hrestb : SameOutside μa μb (x.out + segStart n x.codes 9) (sliceList n 9 x.codes).length) :
    PrunedInv n x μ μb 0 := by
  light_facts pre (pre.round (t := 0) (by omega))
  refine ⟨fun z hz => (hrestb _ (Or.inr (by omega))).trans (hbounds z hz),
    fun z hz => (hsegs z hz).keep, fun s _ hs => absurd hs (by omega), ?_, ?_⟩
  · have hsum : (sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base 0)
        = List.replicate (sliceList n 9 x.codes).length 0 := by
      simp [List.eq_replicate_iff, pvSum]
    rw [hsum]
    exact hzero
  · rw [Nat.succ_mul]
    light_keep

/-- After the last round the ten slices of the result stand one behind the other. -/
theorem PrunedInv.result (hsorted : x.codes.Pairwise (· < ·)) (inv : PrunedInv n x μ μ' 10) :
    Seg μ' x.out (prunedList x.EA x.EB (n + 1) x.base x.codes) := by
  rw [prunedList_succ x.EA x.EB n x.base hsorted, seg_append]
  refine ⟨Seg.flatMap_range _ 9 fun t ht => ?_, ?_⟩
  · have hpos : ((List.range t).map fun s =>
        ((sliceList n s x.codes).map (prunedValue x.EA x.EB n (x.base + s * 10 ^ n))).length).sum
          = segStart n x.codes t := by
      simp [segStart]
    rw [hpos]
    exact inv.done t ht (by omega)
  · have hpos : ((List.range 9).flatMap fun t =>
        (sliceList n t x.codes).map (prunedValue x.EA x.EB n (x.base + t * 10 ^ n))).length
          = segStart n x.codes 9 := by
      simp [segStart, List.length_flatMap]
    rw [hpos]
    exact inv.acc

/-! ## The four calls of a round -/

/-- The arguments of the recursive call for the term t.  Its list is the list of the child, which
stands behind the codes in the frame; its output are the cells behind that list; its stack is what
follows. -/
@[simp]
def PrunedArgs.child (x : PrunedArgs) (n t : ℕ) : PrunedArgs :=
  { x with
    base := x.base + t * 10 ^ n
    l := x.sp + 11 + x.codes.length
    out := x.sp + 11 + 2 * x.codes.length
    sp := x.sp + 11 + 3 * x.codes.length
    codes := childList n t x.codes }

/-- The values of the child t. -/
abbrev PrunedArgs.childValues (x : PrunedArgs) (n t : ℕ) : List ℤ :=
  (childList n t x.codes).map (prunedValue x.EA x.EB n (x.base + t * 10 ^ n))

/-- The arguments of a call of pick in round t: the values of the child t are restricted to the list
small, which stands at the position pos among the codes in the frame, and go to the same position of
the output. -/
@[simp]
def PrunedArgs.pick (x : PrunedArgs) (n t pos : ℕ) (small : List ℕ) : PickArgs where
  pSub := x.sp + 11 + pos
  pU := x.sp + 11 + x.codes.length
  pVal := x.sp + 11 + 2 * x.codes.length
  pDst := x.out + pos
  small := small
  big := childList n t x.codes
  values := x.childValues n t

/-- Step (2) is done: the list of the child t has been written behind the codes, and nothing else
has changed. -/
structure Merged (n : ℕ) (x : PrunedArgs) (t : ℕ) (μ' μ₁ : ℕ → ℤ) : Prop where
  child : SegN μ₁ (x.sp + 11 + x.codes.length) (childList n t x.codes)
  rest : SameOutside μ' μ₁ (x.sp + 11 + x.codes.length)
    ((firstList n t x.codes).length + (sliceList n 9 x.codes).length)

/-- Step (3) is done: the values of the child t have been written behind its list; only these cells
and the frames above have changed. -/
structure Returned (n : ℕ) (x : PrunedArgs) (t : ℕ) (μ₁ μ₂ : ℕ → ℤ) : Prop where
  values : Seg μ₂ (x.sp + 11 + 2 * x.codes.length) (x.childValues n t)
  rest : SameOutside μ₁ μ₂ (x.sp + 11 + 2 * x.codes.length)
    (x.codes.length + n * (3 * (childList n t x.codes).length + 11))

/-- The first half of step (4) is done: the slice of the result at the output variable of the term t
has been written. -/
structure Restricted (n : ℕ) (x : PrunedArgs) (t : ℕ) (μ₂ μ₃ : ℕ → ℤ) : Prop where
  values : Seg μ₃ (x.out + segStart n x.codes t)
    ((firstList n t x.codes).map (prunedValue x.EA x.EB n (x.base + t * 10 ^ n)))
  rest : SameOutside μ₂ μ₃ (x.out + segStart n x.codes t) (firstList n t x.codes).length

section Round

variable {μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} (pre : PrunedPre lim μ (n + 1) x) (inv : PrunedInv n x μ μ' t)
  (ht : t < 10) (m : Merged n x t μ' μ₁)
include pre inv ht m

/-- Step (3), for a term λ with S_λ = ∅: if the list of the child is empty, then so are the two
slices, and the round is over. -/
theorem PrunedInv.next_of_nil (hnil : childList n t x.codes = []) :
    PrunedInv n x μ μ₁ (t + 1) := by
  light_facts pre (pre.round ht) m
  have hfirst0 : firstList n t x.codes = [] := List.eq_nil_iff_forall_not_mem.mpr fun c hc => by
    simpa [hnil] using firstList_subset_childList c hc
  have hlast0 : sliceList n 9 x.codes = [] := List.eq_nil_iff_forall_not_mem.mpr fun c hc => by
    simpa [hnil] using sliceList_nine_subset_childList (n := n) (l := x.codes) t c hc
  refine inv.next pre.sizes (by light_keep) (by light_keep) (by rw [Nat.succ_mul]; light_keep)
    (fun h9 => ?_) (by rw [hlast0]; simp)
  rw [← if_pos h9 (t := sliceList n t x.codes) (e := []), ← firstList, hfirst0]
  simp

/-- Step (3): what the recursive call assumes holds. -/
theorem PrunedPre.child : PrunedPre lim μ₁ n (x.child n t) := by
  light_facts pre (pre.round ht) m inv
  have hAB : 0 ≤ x.A * x.B := mul_nonneg pre.A_nonneg pre.B_nonneg
  exact
    { powers := pre.powers.keep
      encA := pre.encA.keep
      encB := pre.encB.keep
      list := m.child
      sorted := pairwise_childList pre.sorted t
      lt := lt_of_mem_childList pre.sorted t
      boundA := pre.boundA
      boundB := pre.boundB
      word := by simpa using mul_ten_pow_mul_le n (k := 1) (by omega) hAB pre.word
      pow := le_trans (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)) pre.pow }

variable (r : Returned n x t μ₁ μ₂)
include r

/-- Step (4), first half (c_{z_ij} is C_{P_ij} restricted to S_{z_ij}): what the first call of pick
assumes holds. -/
theorem Returned.pickFirst :
    PickPre lim μ₂ (x.pick n t (segStart n x.codes t) (firstList n t x.codes)) := by
  light_facts pre (pre.round ht) m r
  exact
    { small := (inv.first ht).keep
      big := m.child.keep
      values := r.values
      len := by simp
      big_sorted := pairwise_childList pre.sorted t
      small_sorted := pairwise_firstList pre.sorted
      sub := firstList_subset_childList }

variable (s : Restricted n x t μ₂ μ₃)
include s

/-- Step (4), second half (c_{z₀} is the sum of the C_λ restricted to S_{z₀}): what the second call
of pick assumes holds. -/
theorem Restricted.pickLast :
    PickPre lim μ₃ (x.pick n t (segStart n x.codes 9) (sliceList n 9 x.codes)) := by
  light_facts pre (pre.round ht) m r s
  exact
    { small := (inv.segs 9 (by omega)).keep
      big := m.child.keep
      values := r.values.keep
      len := by simp
      big_sorted := pairwise_childList pre.sorted t
      small_sorted := pairwise_sliceList pre.sorted
      sub := sliceList_nine_subset_childList t }

/-- The sum over the terms before t still stands in the slice at z₀. -/
theorem Restricted.acc :
    Seg μ₃ (x.out + segStart n x.codes 9)
      ((sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base t)) := by
  light_facts pre (pre.round ht) m r s
  exact inv.acc.keep

/-- Step (4) is done: after the second call of pick `PrunedInv` holds for t + 1. -/
theorem Restricted.next
    (hsum : Seg μ₄ (x.out + segStart n x.codes 9)
      ((sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base (t + 1))))
    (hrest : SameOutside μ₃ μ₄ (x.out + segStart n x.codes 9) (sliceList n 9 x.codes).length) :
    PrunedInv n x μ μ₄ (t + 1) := by
  light_facts pre (pre.round ht) m r s
  refine inv.next pre.sizes (by light_keep) (by light_keep) (by rw [Nat.succ_mul]; light_keep)
    (fun h9 => ?_) hsum
  have hvalues : Seg μ₄ _ _ := s.values.keep
  rwa [firstList, if_pos h9] at hvalues

end Round

/-! ## The values -/

/-- Adding the values of the child t to the sum over the terms before t. -/
theorem zipWith_add_pvSum (x : PrunedArgs) (n t : ℕ) (h : x.codes.Pairwise (· < ·)) :
    List.zipWith (· + ·) ((sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base t))
        (restrictList (childList n t x.codes) (x.childValues n t) (sliceList n 9 x.codes))
      = (sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base (t + 1)) := by
  rw [restrictList_map _ (pairwise_childList h t) (pairwise_sliceList h)
    (sliceList_nine_subset_childList t), List.zipWith_map, List.zipWith_self]
  exact List.map_congr_left fun c _ => (pvSum_succ x.EA x.EB n x.base t c).symm

/-- The sum of the values of a code at the first k children is at most k 10^n A B. -/
theorem abs_pvSum_le {EA EB : List ℤ} {A B : ℤ} (hA : AbsLe EA A) (hB : AbsLe EB B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (n base k c : ℕ) :
    |pvSum EA EB n base k c| ≤ k * (10 ^ n * (A * B)) := by
  induction k with
  | zero => simp [pvSum]
  | succ k ih =>
    rw [pvSum_succ]
    have hterm := abs_prunedValue_le hA hB hA0 hB0 n (base + k * 10 ^ n) c
    have hadd := abs_add_le (pvSum EA EB n base k c) (prunedValue EA EB n (base + k * 10 ^ n) c)
    push_cast
    linarith

/-- The sums that are formed in the slice at z₀ fit in a word. -/
theorem PrunedPre.abs_pvSum_le (pre : PrunedPre lim μ (n + 1) x) {k : ℕ} (hk : k ≤ 10) :
    ∀ y ∈ (sliceList n 9 x.codes).map (pvSum x.EA x.EB n x.base k), |y| ≤ lim.word := by
  intro y hy
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy
  exact (Sec2.abs_pvSum_le pre.boundA pre.boundB pre.A_nonneg pre.B_nonneg n x.base k c).trans
    (mul_ten_pow_mul_le n hk (mul_nonneg pre.A_nonneg pre.B_nonneg) pre.word)

end Light.Sec2
