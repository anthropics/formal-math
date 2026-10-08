/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Chunks
public import ThreeSumApsp.Util.CountingSort

/-!
# The classes W_ϱ of the pairs (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p)".  (The cutting of
the classes into chunks, with which the sentence goes on, is a routine of its own.)

classes(rab, n, p, cls, cur, qi, qj) sorts the n² pairs (a, b) by the residue of w(a,b), which is in
the cell rab + a n + b, keeping the row-major order within a class: a stable counting sort.  It
writes the rows of the sorted pairs to qi, their columns to qj, and the places where the classes
start to cls.  The row and the column of the current pair are kept in two counters, so that no
division is needed.  `classes_meets` proves this, within `tClasses n p` steps, a number linear in
n² + p.

The routine has five phases.  Between them the state is described by `ClsState`:

* `clsZero_ends`: the counters are cleared;
* `clsCount_ends`: the sizes of the classes are counted;
* `clsPrefix_ends`: prefix sums turn the sizes into the starts;
* `clsCopy_ends`: the starts are copied to cur, the next free places;
* `clsPlace_ends`: each pair goes to the next free place of its class (`ClsPlaced.step` for the
  memory, `clsPlaceOne_ends` for the program), and row and column step to the next pair.

The place of a pair is its place `sortPos` in a stable sort; `getD_sortedIdx` and
`segN_map_sortedIdx` identify what stands there with the lists of the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side: the lists of the specification and the places of a stable sort -/

section pure

/-- The key of the pair number i. -/
def clsKey (RAB : List ℕ) : ℕ → ℕ := fun i => RAB.getD i 0

/-- The size of a class, as a count of keys. -/
theorem length_classIdx (n : ℕ) (RAB : List ℕ) (r : ℕ) :
    (classIdx n RAB r).length = cntEq (clsKey RAB) r (n * n) :=
  List.length_filter_range (fun i => RAB.getD i 0 = r) (n * n)

/-- The sizes of the classes before `r` add up to the number of smaller keys. -/
theorem sum_length_classIdx (n : ℕ) (RAB : List ℕ) (r : ℕ) :
    ((List.range r).map fun r' => (classIdx n RAB r').length).sum =
      cntLt (clsKey RAB) r (n * n) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, cntLt_succ_left]
    simp [length_classIdx]

/-- An entry of the list of the starts. -/
theorem getD_classStarts (n p : ℕ) (RAB : List ℕ) {r : ℕ} (hr : r ≤ p) :
    (classStarts n p RAB).getD r 0 = cntLt (clsKey RAB) r (n * n) := by
  have h : r < p + 1 := by omega
  simp [classStarts, classStart, List.getD_eq_getElem?_getD, h, sum_length_classIdx]

/-- The pair number i stands at its place in the list of all the pairs, class after class. -/
theorem getD_sortedIdx (n p : ℕ) (RAB : List ℕ) {i : ℕ} (hi : i < n * n) (hk : clsKey RAB i < p) :
    (sortedIdx n p RAB).getD (sortPos (clsKey RAB) (n * n) i) 0 = i := by
  have ho : cntEq (clsKey RAB) (clsKey RAB i) i < (classIdx n RAB (clsKey RAB i)).length := by
    rw [length_classIdx]
    exact cntEq_lt_of_lt hi
  rw [sortedIdx, sortPos, ← sum_length_classIdx, List.getD_flatMap_range_sum _ hk ho]
  exact List.getD_filter_range_count (fun j => RAB.getD j 0 = clsKey RAB i) (n * n) hi rfl

/-- All the pairs are listed if all the keys are below `p`. -/
theorem length_sortedIdx (n p : ℕ) (RAB : List ℕ) (h : ∀ i < n * n, clsKey RAB i < p) :
    (sortedIdx n p RAB).length = n * n := by
  rw [sortedIdx, List.length_flatMap, sum_length_classIdx, cntLt_of_forall_lt h]

/-- What stands at the places of a stable sort is the list of the pairs, class after class. -/
theorem segN_map_sortedIdx {μ' : ℕ → ℤ} {n p : ℕ} {RAB : List ℕ}
    (hkeys : ∀ j < n * n, clsKey RAB j < p) {base : ℕ} (f : ℕ → ℕ)
    (h : ∀ j < n * n, μ' (base + sortPos (clsKey RAB) (n * n) j) = (f j : ℕ)) :
    SegN μ' base ((sortedIdx n p RAB).map f) := by
  have hlen := length_sortedIdx n p RAB hkeys
  intro q hq
  have hq' : q < n * n := by simpa [hlen] using hq
  obtain ⟨j, hj, rfl⟩ := exists_sortPos_eq (clsKey RAB) hq'
  have hg := getD_sortedIdx n p RAB hj (hkeys j hj)
  rw [List.getD_eq_getElem _ 0 (by rw [hlen]; exact hq')] at hg
  simp only [List.getElem_map, hg]
  exact h j hj

end pure

/-! ## The routine -/

namespace Classes

/-- Local 0 of classes: the address of the residues. -/
abbrev Rab : ℕ := 0
/-- Local 1 of classes: the number n of vertices of a part. -/
abbrev Size : ℕ := 1
/-- Local 2 of classes: the prime p. -/
abbrev Prime : ℕ := 2
/-- Local 3 of classes: the address of the starts of the classes. -/
abbrev Cls : ℕ := 3
/-- Local 4 of classes: the address of the next free places. -/
abbrev Cur : ℕ := 4
/-- Local 5 of classes: the address of the rows of the sorted pairs. -/
abbrev Rows : ℕ := 5
/-- Local 6 of classes: the address of their columns. -/
abbrev Cols : ℕ := 6
/-- Local 7 of classes: the number n² of pairs. -/
abbrev Pairs : ℕ := 7
/-- Local 8 of classes: a counter. -/
abbrev Idx : ℕ := 8
/-- Local 9 of classes: an address. -/
abbrev Addr : ℕ := 9
/-- Local 10 of classes: the row of the current pair. -/
abbrev Row : ℕ := 10
/-- Local 11 of classes: its column. -/
abbrev Col : ℕ := 11
/-- Local 12 of classes: its place. -/
abbrev Place : ℕ := 12

end Classes

open Classes in
/-- cls[t] := 0 for t ≤ p. -/
def clsZero : Stmt := .for Idx (v Prime +' k 1) (.store (v Cls +' v Idx) (k 0))

open Classes in
/-- cls[rab[i] + 1] += 1 for i < n². -/
def clsCount : Stmt :=
  .for Idx (v Pairs) (
    .set Addr (v Cls +' M (v Rab +' v Idx) +' k 1) ;;
    .store (v Addr) (M (v Addr) +' k 1))

open Classes in
/-- cls[t] += cls[t - 1] for t = 1, …, p. -/
def clsPrefix : Stmt :=
  .set Idx (k 1) ;;
  .while (v Idx ≤' v Prime) (
    .store (v Cls +' v Idx) (M (v Cls +' v Idx) +' M (v Cls +' v Idx -' k 1)) ;;
    .set Idx (v Idx +' k 1))

open Classes in
/-- cur[t] := cls[t] for t < p. -/
def clsCopy : Stmt := pass Idx (v Prime) (v Cur) (M (v Cls +' v Idx))

open Classes in
/-- The pair number i, which is (row, col), goes to the next free place of its class. -/
def clsPlaceOne : Stmt :=
  .set Addr (v Cur +' M (v Rab +' v Idx)) ;;
  .set Place (M (v Addr)) ;;
  .store (v Rows +' v Place) (v Row) ;;
  .store (v Cols +' v Place) (v Col) ;;
  .store (v Addr) (v Place +' k 1)

open Classes in
/-- All pairs go to their places. -/
def clsPlace : Stmt :=
  .set Row (k 0) ;; .set Col (k 0) ;; .for Idx (v Pairs) (clsPlaceOne ;; nextPair Row Col Size)

open Classes in
/-- classes(rab, n, p, cls, cur, qi, qj). -/
def classesBody : Stmt :=
  .set Pairs (v Size *' v Size) ;; clsZero ;; clsCount ;; clsPrefix ;; clsCopy ;; clsPlace

/-- The time of classes. -/
def tClasses (n p : ℕ) : ℕ := 70 * (n * n) + 56 * p + 57

/-- The arguments of classes, and the list `RAB` of the residues, which stands at `rab`. -/
structure ClassesArgs : Type where
  (rab n p cls cur qi qj : ℕ)
  (RAB : List ℕ)

/-- The values of the arguments of classes. -/
abbrev ClassesArgs.vals (x : ClassesArgs) : List ℤ := [x.rab, x.n, x.p, x.cls, x.cur, x.qi, x.qj]

/-- The locals of classes: the arguments, the number n² of pairs, and the five that change. -/
abbrev ClassesArgs.locals (x : ClassesArgs) (i ad row col pl : ℤ) : List ℤ :=
  [x.rab, x.n, x.p, x.cls, x.cur, x.qi, x.qj, (x.n * x.n : ℕ), i, ad, row, col, pl]

/-- Only cells of the four areas that classes writes have changed. -/
abbrev ClassesArgs.Same (x : ClassesArgs) (μ μ' : ℕ → ℤ) : Prop :=
  SameOutside μ μ' x.cls (x.qj + x.n * x.n - x.cls)

/-- What classes assumes: the residues, below p, stand at rab; behind them lie, in this order, the
four areas cls, cur, qi and qj that it writes; everything is inside the memory. -/
structure ClassesPre (lim : Limits) (μ : ℕ → ℤ) (x : ClassesArgs) : Prop where
  seg : SegN μ x.rab x.RAB
  len : x.RAB.length = x.n * x.n
  lt : ∀ r ∈ x.RAB, r < x.p
  rab_le : x.rab + x.n * x.n ≤ x.cls := by light_arith
  cls_le : x.cls + (x.p + 1) ≤ x.cur := by light_arith
  cur_le : x.cur + x.p ≤ x.qi := by light_arith
  qi_le : x.qi + x.n * x.n ≤ x.qj := by light_arith
  qj_le : x.qj + x.n * x.n < lim.space := by light_arith

section phases

variable {μ μ' : ℕ → ℤ} {x : ClassesArgs}

/-- The keys are below p. -/
theorem ClassesPre.key_lt (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n) :
    clsKey x.RAB i < x.p := by
  have hl : i < x.RAB.length := pre.len ▸ hi
  rw [clsKey, List.getD_eq_getElem _ 0 hl]
  exact pre.lt _ (List.getElem_mem hl)

/-- The residues lie before the areas that are written, so they can be read at any time. -/
theorem ClassesPre.read (pre : ClassesPre lim μ x) (h : x.Same μ μ') {i : ℕ}
    (hi : i < x.n * x.n) : μ' (x.rab + i) = (clsKey x.RAB i : ℕ) := by
  have hl : i < x.RAB.length := pre.len ▸ hi
  have := pre.rab_le
  rw [h _ (by omega), pre.seg _ (by simpa using hl), List.getElem_map, clsKey,
    List.getD_eq_getElem _ 0 hl]

/-- A state of classes between two phases: the locals hold the arguments and n², only the four areas
have been written, and R holds of the memory. -/
def ClsState (μ : ℕ → ℤ) (x : ClassesArgs) (R : (ℕ → ℤ) → Prop) (σ : State) : Prop :=
  ∃ (i ad row col pl : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (x.locals i ad row col pl), μ'⟩ ∧ x.Same μ μ' ∧ R μ'

/-- After the first phase: the counters are 0. -/
def ClsZeroed (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop := ∀ t ≤ x.p, μ' (x.cls + t) = 0

/-- After the second phase: the cell t + 1 holds the size of the class t. -/
def ClsCounted (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop :=
  μ' x.cls = 0 ∧ ∀ t < x.p, μ' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t (x.n * x.n) : ℕ)

/-- After the third phase: the cell t holds the start of the class t. -/
def ClsStarts (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop :=
  ∀ t ≤ x.p, μ' (x.cls + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)

variable {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)

include hw

/-- cls[t] := 0 for t ≤ p. -/
theorem clsZero_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (fun _ => True) σ) :
    Ends lim P d clsZero σ (15 * x.p + 23) (ClsState μ x (ClsZeroed x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, -⟩ := h
  light_facts pre
  refine Ends.forFrame
    (fun j μ'' => x.Same μ μ'' ∧ ∀ t < j, μ'' (x.cls + t) = 0) (x.p + 1)
    ⟨hrest, fun t ht => absurd ht (by omega)⟩ ?round ?done
  case round =>
    rintro j μ'' hj ⟨hr, hz⟩
    refine Ends.storeTo (x.cls + j) 0 ⟨rfl, hr.update ⟨by omega, by omega⟩ _, fun t ht => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (hz t ht)
    · exact Function.update_self ..
  case done =>
    exact fun μ'' ⟨hr, hz⟩ => ⟨_, ad, row, col, pl, μ'', rfl, hr, fun t ht => hz t (by omega)⟩

/-- cls[rab[i] + 1] += 1 for i < n². -/
theorem clsCount_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsZeroed x) σ) :
    Ends lim P d clsCount σ (23 * (x.n * x.n) + 6) (ClsState μ x (ClsCounted x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hz⟩ := h
  light_facts pre
  refine Ends.for (fun j σ => ∃ (ad : ℤ) (μ'' : ℕ → ℤ),
      σ = ⟨frame (x.locals j ad row col pl), μ''⟩ ∧ x.Same μ μ'' ∧ μ'' x.cls = 0 ∧
      ∀ t < x.p, μ'' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t j : ℕ)) (x.n * x.n) 15
    ?start ?round ?done ?bound
  case start =>
    exact ⟨ad, μ', by rw [update_frame_setLocal]; rfl, hrest, hz 0 (by omega),
      fun t ht => by simpa [cntEq] using hz (t + 1) (by omega)⟩
  case bound =>
    rintro j _ - - ⟨ad, μ'', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨ad, μ'', rfl, hr, hfirst, hc⟩
    exact ⟨_, ad, row, col, pl, μ'', rfl, hr, hfirst, hc⟩
  case round =>
    rintro j _ hj - ⟨ad, μ'', rfl, hr, hfirst, hc⟩
    have hread := pre.read hr hj
    have hk := pre.key_lt hj
    have hcell := hc _ hk
    have hle : cntEq (clsKey x.RAB) (clsKey x.RAB j) j ≤ j := Nat.count_le _
    have haddr :
        ((x.cls : ℤ) + ((clsKey x.RAB j : ℤ) + 1)).toNat = x.cls + (clsKey x.RAB j + 1) := by
      omega
    -- ad := cls + rab[i] + 1
    light_set (x.cls + (clsKey x.RAB j + 1) : ℕ) using hread
    -- mem[ad] := mem[ad] + 1
    refine Ends.storeTo (x.cls + (clsKey x.RAB j + 1))
      (cntEq (clsKey x.RAB) (clsKey x.RAB j) j + 1 : ℕ)
      ⟨by simp, _, _, by rw [update_frame_setLocal]; rfl, hr.update ⟨by omega, by omega⟩ _,
        (Function.update_of_ne (by omega) _ _).trans hfirst, fun t ht => ?_⟩
      (by light_side [haddr, hcell])
    rw [cntEq_succ]
    by_cases e : clsKey x.RAB j = t
    · subst e
      rw [if_pos rfl, Function.update_self]
    · rw [if_neg e, Function.update_of_ne (by omega)]
      exact hc t ht

/-- cls[t] += cls[t - 1] for t = 1, …, p. -/
theorem clsPrefix_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsCounted x) σ) :
    Ends lim P d clsPrefix σ (25 * x.p + 8) (ClsState μ x (ClsStarts x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hfirst, hc⟩ := h
  light_facts pre
  -- i := 1
  light_set (1 : ℕ)
  -- while i ≤ p; before round j the counter is j + 1, and the cells up to j hold the starts
  refine Ends.whileConst (fun j σ => ∃ μ'' : ℕ → ℤ,
      σ = ⟨frame (x.locals (j + 1 : ℕ) ad row col pl), μ''⟩ ∧ x.Same μ μ'' ∧
      (∀ t ≤ j, μ'' (x.cls + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) ∧
      ∀ t < x.p, j ≤ t → μ'' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t (x.n * x.n) : ℕ)) x.p 19
    ?start ?round ?done (by light_time)
  case start =>
    refine ⟨μ', rfl, hrest, fun t ht => ?_, fun t ht _ => hc t ht⟩
    obtain rfl : t = 0 := by omega
    simpa [cntLt] using hfirst
  case done =>
    rintro _ ⟨μ'', rfl, hr, hs, -⟩
    exact ⟨by light_side, by light_side, _, ad, row, col, pl, μ'', rfl, hr, hs⟩
  case round =>
    rintro j _ hj ⟨μ'', rfl, hr, hs, hc⟩
    have hprev := hs j le_rfl
    have hcell := hc j hj le_rfl
    have hle : cntLt (clsKey x.RAB) (j + 1) (x.n * x.n) ≤ x.n * x.n := cntLt_le _ _ _
    have hsum := cntLt_succ_left (clsKey x.RAB) j (x.n * x.n)
    have haddr : ((x.cls : ℤ) + ((j : ℤ) + 1)).toNat = x.cls + (j + 1) := by omega
    have haddr' : ((x.cls : ℤ) + ((j : ℤ) + 1) - 1).toNat = x.cls + j := by omega
    refine ⟨by light_side, by light_side, ?_⟩
    -- cls[i] := cls[i] + cls[i - 1]
    refine Ends.storeToThen (x.cls + (j + 1)) (cntLt (clsKey x.RAB) (j + 1) (x.n * x.n) : ℕ) ?_
      (by light_side [haddr, haddr', hprev, hcell])
    -- i := i + 1
    light_set (j + 1 + 1 : ℕ)
    refine ⟨_, rfl, hr.update ⟨by omega, by omega⟩ _, fun t ht => ?_,
      fun t ht hjt => (Function.update_of_ne (by omega) _ _).trans (hc t ht (by omega))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with ht | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (hs t (by omega))
    · exact Function.update_self ..

/-- After the fourth phase: cur holds the starts as well. -/
def ClsCopied (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop :=
  ClsStarts x μ' ∧ ∀ t < x.p, μ' (x.cur + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)

open Classes in
/-- cur[t] := cls[t] for t < p. -/
theorem clsCopy_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsStarts x) σ) :
    Ends lim P d clsCopy σ (16 * x.p + 6) (ClsState μ x (ClsCopied x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hs⟩ := h
  light_facts pre
  refine Ends.pass (x := Prime) (y := Cur) (dst := x.cur) (n := x.p)
    (fun t => (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) (fun j hj => ?_) ?_ hw (by omega) rfl rfl
  · have hcell := (wrote_rest (μ := μ') (dst := x.cur) (j := j)
      (f := fun t => (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) (a := x.cls + j) (by omega)).trans
      (hs j (by omega))
    simp [Limits.Addr, abs_le, hcell]
    omega
  · rw [update_frame_setLocal]
    exact ⟨_, ad, row, col, pl, _, rfl,
      hrest.trans ((sameOutside_wrote le_rfl).mono (by omega) (by omega)),
      fun t ht => (wrote_rest (by omega)).trans (hs t ht), fun t ht => wrote_done ht⟩

/-- While the pairs are placed, before the pair number i: cls holds the starts, cur the next free
place of each class, and the pairs before i stand at their places. -/
structure ClsPlaced (x : ClassesArgs) (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  keep : ClsStarts x μ'
  next : ∀ t < x.p,
    μ' (x.cur + t) = ((cntLt (clsKey x.RAB) t (x.n * x.n) + cntEq (clsKey x.RAB) t i : ℕ) : ℤ)
  done : ∀ j < i, μ' (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) j) = (j / x.n : ℕ) ∧
    μ' (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) j) = (j % x.n : ℕ)

omit hw in
/-- **The pair number i is placed**: its row and its column are written to its place, and the next
free place of its class moves on. -/
theorem ClsPlaced.step (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n)
    (h : ClsPlaced x i μ') :
    ClsPlaced x (i + 1)
      (Function.update (Function.update (Function.update μ'
        (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i) (i / x.n : ℕ))
        (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i) (i % x.n : ℕ))
        (x.cur + clsKey x.RAB i) (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)) := by
  light_facts pre
  have hk := pre.key_lt hi
  have hpos := sortPos_lt (clsKey x.RAB) hi
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun j hj => ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact h.keep t ht
  · rw [cntEq_succ]
    by_cases e : clsKey x.RAB i = t
    · subst e
      rw [Function.update_self, if_pos rfl, sortPos, Nat.add_assoc]
    · rw [if_neg e, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact h.next t ht
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hne : sortPos (clsKey x.RAB) (x.n * x.n) j ≠ sortPos (clsKey x.RAB) (x.n * x.n) i :=
        fun e => absurd (eq_of_sortPos_eq (by omega) hi e) (by omega)
      have hlt := sortPos_lt (clsKey x.RAB) (show j < x.n * x.n by omega)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.done j hj
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      exact ⟨rfl, rfl⟩

/-- **The pair number i is written to its place.** -/
theorem clsPlaceOne_ends (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n) (ad pl : ℤ)
    (hrest : x.Same μ μ') (h : ClsPlaced x i μ') :
    Ends lim P d clsPlaceOne ⟨frame (x.locals i ad (i / x.n : ℕ) (i % x.n : ℕ) pl), μ'⟩ 25
      fun σ' => ∃ (ad' pl' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (x.locals i ad' (i / x.n : ℕ) (i % x.n : ℕ) pl'), μ''⟩ ∧
          x.Same μ μ'' ∧ ClsPlaced x (i + 1) μ'' := by
  light_facts pre
  have hread := pre.read hrest hi
  have hk := pre.key_lt hi
  have hpos : sortPos (clsKey x.RAB) (x.n * x.n) i < x.n * x.n := sortPos_lt (clsKey x.RAB) hi
  have hcell : μ' (x.cur + clsKey x.RAB i) = (sortPos (clsKey x.RAB) (x.n * x.n) i : ℕ) :=
    h.next _ hk
  have hrow := Nat.div_le_self i x.n
  have hcol := Nat.mod_le i x.n
  have hstep := h.step pre hi
  have hrest' := ((hrest.update (b := x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i)
    ⟨by omega, by omega⟩ (i / x.n : ℕ)).update (b := x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i)
    ⟨by omega, by omega⟩ (i % x.n : ℕ)).update (b := x.cur + clsKey x.RAB i) ⟨by omega, by omega⟩
    (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)
  generalize i / x.n = row at *
  generalize i % x.n = col at *
  -- ad := cur + rab[i]; pl := mem[ad]
  light_set (x.cur + clsKey x.RAB i : ℕ) using hread
  light_set (sortPos (clsKey x.RAB) (x.n * x.n) i : ℕ) using hcell
  -- qi[pl] := row; qj[pl] := col; mem[ad] := pl + 1
  light_store (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i) (row : ℕ)
  light_store (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i) (col : ℕ)
  light_store (x.cur + clsKey x.RAB i) (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)
  exact ⟨_, _, _, rfl, hrest', hstep⟩

/-- All pairs go to their places. -/
theorem clsPlace_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsCopied x) σ) :
    Ends lim P d clsPlace σ (47 * (x.n * x.n) + 10) (ClsState μ x (ClsPlaced x (x.n * x.n))) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hs, hcur⟩ := h
  light_facts pre
  -- row := 0; col := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- for i < nn
  refine Ends.for (fun j σ => ∃ (ad pl : ℤ) (μ'' : ℕ → ℤ),
      σ = ⟨frame (x.locals j ad (j / x.n : ℕ) (j % x.n : ℕ) pl), μ''⟩ ∧
        x.Same μ μ'' ∧ ClsPlaced x j μ'') (x.n * x.n) 39
    ?start ?round ?done ?bound
  case start =>
    exact ⟨ad, pl, μ', by rw [update_frame_setLocal, Nat.zero_div, Nat.zero_mod]; rfl, hrest, hs,
      fun t ht => by simpa [cntEq] using hcur t ht, fun j hj => absurd hj (by omega)⟩
  case bound =>
    rintro j _ - - ⟨ad, pl, μ'', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨ad, pl, μ'', rfl, hr, hp⟩
    exact ⟨_, ad, _, _, pl, μ'', rfl, hr, hp⟩
  case round =>
    rintro j _ hj - ⟨ad, pl, μ'', rfl, hr, hp⟩
    have hn : 0 < x.n := Nat.pos_of_ne_zero fun e => by simp [e] at hj
    have hnn : x.n ≤ x.n * x.n := Nat.le_mul_of_pos_left x.n hn
    refine Ends.next 25 ((clsPlaceOne_ends hw pre hj ad pl hr hp).mono le_rfl ?_)
    rintro _ ⟨ad', pl', μ₃, rfl, hr', hp'⟩
    refine Ends.nextPair ?_ hn (by omega) (by omega) rfl rfl rfl
    exact ⟨by simp, ad', pl', μ₃, by rw [update_frame_setLocal]; rfl, hr', hp'⟩

end phases

open Classes in
/-- **classes** writes the starts of the classes and the rows and columns of the pairs, class after
class. -/
theorem classes_meets {pClasses : ℕ} (hP : P[pClasses]? = some classesBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (x : ClassesArgs) (μ : ℕ → ℤ) (pre : ClassesPre lim μ x) :
    Meets lim P pClasses d x.vals μ (tClasses x.n x.p) fun _ μ' =>
      SegN μ' x.cls (classStarts x.n x.p x.RAB) ∧ SegN μ' x.qi (queryRows x.n x.p x.RAB) ∧
        SegN μ' x.qj (queryCols x.n x.p x.RAB) ∧ x.Same μ μ' := by
  refine .of_body hP ?_
  light_facts pre
  unfold tClasses
  -- pairs := n * n
  light_set (x.n * x.n : ℕ)
  have h0 : ClsState μ x (fun _ => True) ⟨frame (setLocal x.vals Pairs (x.n * x.n : ℕ)), μ⟩ :=
    ⟨0, 0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, .refl, trivial⟩
  -- the five phases
  refine Ends.next _ ((clsZero_ends hw pre h0).mono le_rfl fun _ h1 => ?_)
  refine Ends.next _ ((clsCount_ends hw pre h1).mono le_rfl fun _ h2 => ?_)
  refine Ends.next _ ((clsPrefix_ends hw pre h2).mono le_rfl fun _ h3 => ?_)
  refine Ends.next _ ((clsCopy_ends hw pre h3).mono le_rfl fun _ h4 => ?_)
  light_piece (clsPlace_ends hw pre h4) with _ ⟨_, _, _, _, _, μ', rfl, hrest, hp⟩
  have hkeys : ∀ j < x.n * x.n, clsKey x.RAB j < x.p := fun j hj => pre.key_lt hj
  refine ⟨fun t ht => ?_, segN_map_sortedIdx hkeys _ fun j hj => (hp.done j hj).1,
    segN_map_sortedIdx hkeys _ fun j hj => (hp.done j hj).2, hrest⟩
  have hl : t < (classStarts x.n x.p x.RAB).length := by simpa using ht
  have ht' : t < x.p + 1 := by simpa [classStarts] using hl
  rw [List.getElem_map, ← List.getD_eq_getElem _ 0 hl, getD_classStarts x.n x.p x.RAB (by omega)]
  exact hp.keep t (by omega)

end Light.Sec3
