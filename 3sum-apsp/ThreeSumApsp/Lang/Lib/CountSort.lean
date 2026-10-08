/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Util.CountingSort

/-!
# Counting sort of a list of items by a key that is read through the item

countSort(n, src, dst, key, stride, off, nb, cnt) sorts the n items at src stably by their keys and
writes them to dst.  The key of the item x is the number in the cell key + x · stride + off, a
natural number below nb.  cnt is a scratch area of nb + 1 cells, of arbitrary content on entry; on
exit cnt[t] is the number of items with a key below t, which is where bucket t starts.

The routine has five phases, each of them one loop:
* `csZero` sets the cells of cnt to 0 (`csZero_ends`);
* `csCount` counts the items with key t in cnt[t + 1] (`csCount_ends`);
* `csPrefix` adds up, so that cnt[t] is the start of bucket t (`csPrefix_ends`);
* `csPlace` writes each item to the next free place of its bucket, which it reads from cnt and moves
  on by one (`csPlace_ends`);
* `csShift` moves the contents of cnt up by one cell, so that cnt[t] is again the start of bucket t
  (`csShift_ends`).

Each phase has an invariant, a structure about the memory, with two lemmas: `start` says that it
holds before the first round, and `succ` says what a round does to the memory.  Three numbers
describe the memory, where kf j is the key of item number j: `cntLt kf t n` is the number of items
with a key below t, the start of bucket t; `cntEq kf t i` is the number of items before item number
i with key t; and `sortPos kf n j`, their sum at t = kf j and i = j, is the place of item number j.
What is assumed is `CountSort.Pre`, what is achieved is `CountSort.Post`, and the result is
`countSort_meets`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace CountSort

/-- The local variables of countSort: the arguments n (Len), src, dst, key (Keys), stride, off
(Offset), nb (Buckets), cnt; the counter of the loops (Idx); the address of a cell of cnt (Cell); a
place in dst (Place). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Dst : ℕ := 2
@[inherit_doc Len] abbrev Keys : ℕ := 3
@[inherit_doc Len] abbrev Stride : ℕ := 4
@[inherit_doc Len] abbrev Offset : ℕ := 5
@[inherit_doc Len] abbrev Buckets : ℕ := 6
@[inherit_doc Len] abbrev Cnt : ℕ := 7
@[inherit_doc Len] abbrev Idx : ℕ := 8
@[inherit_doc Len] abbrev Cell : ℕ := 9
@[inherit_doc Len] abbrev Place : ℕ := 10

end CountSort

open CountSort in
/-- The key of item number i, where i is the value of the counter:
mem[key + src[i] · stride + off]. -/
def csKey : Expr := M (v Keys +' M (v Src +' v Idx) *' v Stride +' v Offset)

@[simp] theorem csKey_cost : csKey.cost = 11 := rfl

open CountSort in
/-- cnt[t] := 0 for t ≤ nb. -/
def csZero : Stmt := .for Idx (v Buckets +' k 1) (.store (v Cnt +' v Idx) (k 0))

open CountSort in
/-- cnt[(key of item i) + 1] += 1 for i < n. -/
def csCount : Stmt :=
  .for Idx (v Len) (.set Cell (v Cnt +' csKey +' k 1) ;; .store (v Cell) (M (v Cell) +' k 1))

open CountSort in
/-- cnt[t + 1] += cnt[t] for t < nb. -/
def csPrefix : Stmt :=
  .for Idx (v Buckets)
    (.store (v Cnt +' v Idx +' k 1) (M (v Cnt +' v Idx +' k 1) +' M (v Cnt +' v Idx)))

open CountSort in
/-- dst[cnt[key of item i]] := item i, cnt[key of item i] += 1, for i < n. -/
def csPlace : Stmt :=
  .for Idx (v Len) (
    .set Cell (v Cnt +' csKey) ;;
    .set Place (M (v Cell)) ;;
    .store (v Dst +' v Place) (M (v Src +' v Idx)) ;;
    .store (v Cell) (v Place +' k 1))

open CountSort in
/-- cnt[t] := cnt[t - 1] for t = nb, …, 1, and cnt[0] := 0. -/
def csShift : Stmt :=
  .set Idx (v Buckets) ;;
  .while (k 0 <' v Idx) (
    .store (v Cnt +' v Idx) (M (v Cnt +' v Idx -' k 1)) ;;
    .set Idx (v Idx -' k 1)) ;;
  .store (v Cnt) (k 0)

/-- countSort(n, src, dst, key, stride, off, nb, cnt). -/
def countSortBody : Stmt := csZero ;; csCount ;; csPrefix ;; csPlace ;; csShift

/-! ## What is assumed, and the state between the phases -/

namespace CountSort

/-- The arguments of countSort. -/
structure Args where
  /-- the number of items -/
  n : ℕ
  /-- where the items stand -/
  src : ℕ
  /-- where the sorted items go -/
  dst : ℕ
  /-- the key of the item x is in the cell key + x · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells of scratch space -/
  cnt : ℕ

/-- The cell that holds the key of the item x. -/
def Args.keyCell (A : Args) (x : ℕ) : ℕ := A.key + x * A.stride + A.off

/-- A state of countSort: the arguments, the counter i, the scratch variables c and p, and the
memory. -/
abbrev Args.state (A : Args) (i c p : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt, i, c, p], μ'⟩

/-- Only dst and cnt have changed. -/
abbrev Args.Same (A : Args) (μ μ' : ℕ → ℤ) : Prop := SameOutside2 μ μ' A.dst A.n A.cnt (A.nb + 1)

end CountSort

open CountSort

/-- What countSort assumes: where the arrays lie, that what is read is not overwritten, and what the
items (it) and their keys (kf) are. -/
structure CountSort.Pre (lim : Limits) (μ : ℕ → ℤ) (A : Args) (it kf : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  srcB : A.src + A.n ≤ lim.space
  dstB : A.dst + A.n ≤ lim.space
  cntB : A.cnt + (A.nb + 1) ≤ lim.space
  items : ∀ i < A.n, μ (A.src + i) = it i
  keyB : ∀ i < A.n, A.keyCell (it i) < lim.space
  keys : ∀ i < A.n, μ (A.keyCell (it i)) = kf i
  keyLt : ∀ i < A.n, kf i < A.nb
  srcDst : Apart A.src A.n A.dst A.n
  srcCnt : Apart A.src A.n A.cnt (A.nb + 1)
  dstCnt : Apart A.dst A.n A.cnt (A.nb + 1)
  keyDst : ∀ i < A.n, Outside A.dst A.n (A.keyCell (it i))
  keyCnt : ∀ i < A.n, Outside A.cnt (A.nb + 1) (A.keyCell (it i))

/-- What countSort achieves: item number j stands at dst[sortPos kf n j], cnt[t] is the number of
items with a key below t, and nothing else has changed. -/
structure CountSort.Post (μ : ℕ → ℤ) (A : Args) (it kf : ℕ → ℕ) (μ' : ℕ → ℤ) : Prop where
  placed : ∀ j < A.n, μ' (A.dst + sortPos kf A.n j) = it j
  starts : ∀ t ≤ A.nb, μ' (A.cnt + t) = cntLt kf t A.n
  same : A.Same μ μ'

variable {μ μ' : ℕ → ℤ} {A : Args} {it kf : ℕ → ℕ} {σ : State}

/-- The items are still there after writing to dst and cnt. -/
theorem CountSort.Pre.item (pre : CountSort.Pre lim μ A it kf) (same : A.Same μ μ') {i : ℕ}
    (hi : i < A.n) : μ' (A.src + i) = it i := by
  light_facts pre
  exact (same _ ⟨by omega, by omega⟩).trans (pre.items i hi)

/-- Reading the key of item number i: the expression stays within the limits and gives kf i. -/
theorem csKey_gives (pre : CountSort.Pre lim μ A it kf) (same : A.Same μ μ') {i : ℕ} (hi : i < A.n)
    (c p : ℤ) : csKey.Gives lim (A.state i c p μ') (kf i) := by
  light_facts pre
  have hcell := pre.keyB i hi
  have hitem := pre.item same hi
  have hkey : μ' (A.keyCell (it i)) = kf i :=
    (same _ ⟨pre.keyDst i hi, pre.keyCnt i hi⟩).trans (pre.keys i hi)
  unfold Args.keyCell at hcell hkey
  have haddr : ((A.key : ℤ) + (it i : ℤ) * A.stride + A.off).toNat
      = A.key + it i * A.stride + A.off := by
    rw [← Int.toNat_natCast (A.key + it i * A.stride + A.off)]
    push_cast
    rfl
  simp [csKey, Limits.Addr, abs_le, hitem, haddr, hkey]
  omega

/-- The state between two phases, and before a round of a phase: the counter is i, only dst and cnt
have changed since the start, and R holds of the memory. -/
def CsState (μ : ℕ → ℤ) (A : Args) (i : ℤ) (R : (ℕ → ℤ) → Prop) (σ : State) : Prop :=
  ∃ (c p : ℤ) (μ' : ℕ → ℤ), σ = A.state i c p μ' ∧ A.Same μ μ' ∧ R μ'

/-- A weaker fact about the memory. -/
theorem CsState.imp {entry : ℤ} {R R' : (ℕ → ℤ) → Prop} (h : CsState μ A entry R σ)
    (hR : ∀ μ', R μ' → R' μ') : CsState μ A entry R' σ := by
  obtain ⟨c, p, μ', rfl, same, h⟩ := h
  exact ⟨c, p, μ', rfl, same, hR _ h⟩

/-- **The loop rule for the phases.**  The loop has m rounds, the value of hi.  The body is a block
that keeps the arguments and the counter.  R j holds of the memory before round j; afterwards the
counter is m and R m holds. -/
theorem Ends.csFor {entry : ℤ} {hi : Expr} {body : Stmt} {T : ℕ} (R : ℕ → (ℕ → ℤ) → Prop) (m : ℕ)
    (start : CsState μ A entry (R 0) σ)
    (round : ∀ (j : ℕ) (c p : ℤ) (μ' : ℕ → ℤ), j < m → A.Same μ μ' → R j μ' →
      Ends lim P d body (A.state j c p μ') body.blockCost (CsState μ A j (R (j + 1))))
    (bound : ∀ (j : ℕ) (c p : ℤ) (μ' : ℕ → ℤ), hi.Gives lim (A.state j c p μ') m := by
      intros; light_side)
    (hm : (m : ℤ) ≤ lim.word := by omega)
    (hT : m * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (.for Idx hi body) σ T (CsState μ A m (R m)) := by
  obtain ⟨c, p, μ', rfl, same, h⟩ := start
  refine Ends.forShape (fun j (s : ℤ × ℤ) μ' => A.state j s.1 s.2 μ')
    (fun j μ' => A.Same μ μ' ∧ R j μ') m body.blockCost (c, p) ⟨same, h⟩ ?round
    (fun s μ' h => ⟨s.1, s.2, μ', rfl, h.1, h.2⟩) (bound := fun j s μ' _ _ => bound j s.1 s.2 μ')
    (hn := hm) (hT := hT)
  intro j s μ' hj h
  refine (round j s.1 s.2 μ' hj h.1 h.2).mono le_rfl ?_
  rintro _ ⟨c, p, μ', rfl, same, h⟩
  exact ⟨(c, p), μ', rfl, same, h⟩

/-! ## The first phase: the counters are set to 0 -/

/-- The first j cells of cnt are 0. -/
def CsZeroed (A : Args) (j : ℕ) (μ' : ℕ → ℤ) : Prop := ∀ t < j, μ' (A.cnt + t) = 0

/-- One more cell is set to 0. -/
theorem CsZeroed.succ {j : ℕ} (h : CsZeroed A j μ') :
    CsZeroed A (j + 1) (Function.update μ' (A.cnt + j) 0) := by
  intro t ht
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
  · exact (Function.update_of_ne (by omega) _ _).trans (h t ht)
  · exact Function.update_self ..

/-- `csZero`: the nb + 1 cells of cnt are 0 afterwards. -/
theorem csZero_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (fun _ => True) σ) :
    Ends lim P d csZero σ (15 * A.nb + 23)
      (CsState μ A (A.nb + 1 : ℕ) (CsZeroed A (A.nb + 1))) := by
  light_facts pre
  -- for t < nb + 1
  refine Ends.csFor (CsZeroed A) (A.nb + 1) (h.imp fun _ _ t ht => absurd ht (by omega)) ?round
  case round =>
    intro t c p μ' ht same zero
    -- cnt[t] := 0
    light_store (A.cnt + t) 0
    exact ⟨c, p, _, rfl, same.update (Or.inr ⟨by omega, by omega⟩) _, zero.succ⟩

/-! ## The second phase: the sizes of the buckets -/

/-- The items before item number i have been counted: the cell t + 1 of cnt holds the number of
those with key t, and the cell 0 holds 0. -/
structure CsCounted (A : Args) (kf : ℕ → ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  first : μ' A.cnt = 0
  sizes : ∀ t < A.nb, μ' (A.cnt + (t + 1)) = cntEq kf t i

/-- Nothing has been counted yet, and all cells are 0. -/
theorem CsCounted.start (h : CsZeroed A (A.nb + 1) μ') : CsCounted A kf 0 μ' :=
  ⟨h 0 (by omega), fun t ht => by simpa using h (t + 1) (by omega)⟩

/-- Item number i is counted. -/
theorem CsCounted.succ {i : ℕ} (h : CsCounted A kf i μ') :
    CsCounted A kf (i + 1)
      (Function.update μ' (A.cnt + (kf i + 1)) (cntEq kf (kf i) i + 1 : ℕ)) := by
  refine ⟨(Function.update_of_ne (by omega) _ _).trans h.first, fun t ht => ?_⟩
  rw [cntEq_succ]
  by_cases e : kf i = t
  · subst e
    rw [if_pos rfl, Function.update_self]
  · rw [if_neg e, Function.update_of_ne (by omega)]
    exact h.sizes t ht

/-- `csCount`: cnt[t + 1] is the number of items with key t afterwards. -/
theorem csCount_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsZeroed A (A.nb + 1)) σ) :
    Ends lim P d csCount σ (30 * A.n + 6) (CsState μ A A.n (CsCounted A kf A.n)) := by
  light_facts pre
  -- for i < n
  refine Ends.csFor (CsCounted A kf) A.n (h.imp fun _ => .start) ?round (hT := by simp; omega)
  case round =>
    intro i c p μ' hi same counted
    obtain ⟨hsafe, hval⟩ := csKey_gives pre same hi c p
    have hlt := pre.keyLt i hi
    have hcell := counted.sizes _ hlt
    have hle : cntEq kf (kf i) i ≤ i := Nat.count_le _
    have haddr : ((A.cnt : ℤ) + ((kf i : ℤ) + 1)).toNat = A.cnt + (kf i + 1) := by omega
    -- cell := cnt + key + 1
    light_set (A.cnt + (kf i + 1) : ℕ) using hsafe, hval
    -- mem[cell] := mem[cell] + 1
    light_store (A.cnt + (kf i + 1)) (cntEq kf (kf i) i + 1 : ℕ) using haddr, hcell
    exact ⟨_, p, _, rfl, same.update (Or.inr ⟨by omega, by omega⟩) _, counted.succ⟩

/-! ## The third phase: the starts of the buckets -/

/-- The first r sizes have been added up: the cells t ≤ r of cnt hold the starts of their buckets,
and a cell t + 1 after them still holds the size of bucket t. -/
structure CsSummed (A : Args) (kf : ℕ → ℕ) (r : ℕ) (μ' : ℕ → ℤ) : Prop where
  starts : ∀ t ≤ r, μ' (A.cnt + t) = cntLt kf t A.n
  sizes : ∀ t < A.nb, r ≤ t → μ' (A.cnt + (t + 1)) = cntEq kf t A.n

/-- What `csCount` leaves: the cell 0 holds 0, the start of bucket 0, and the others the sizes. -/
theorem CsSummed.start (h : CsCounted A kf A.n μ') : CsSummed A kf 0 μ' := by
  refine ⟨fun t ht => ?_, fun t ht _ => h.sizes t ht⟩
  obtain rfl : t = 0 := by omega
  simpa using h.first

/-- The cell r + 1 receives the start of bucket r + 1. -/
theorem CsSummed.succ {r : ℕ} (h : CsSummed A kf r μ') :
    CsSummed A kf (r + 1) (Function.update μ' (A.cnt + (r + 1)) (cntLt kf (r + 1) A.n : ℕ)) := by
  refine ⟨fun t ht => ?_,
    fun t ht hrt => (Function.update_of_ne (by omega) _ _).trans (h.sizes t ht (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with ht | rfl
  · exact (Function.update_of_ne (by omega) _ _).trans (h.starts t (by omega))
  · exact Function.update_self ..

/-- `csPrefix`: cnt[t] is the number of items with a key below t afterwards. -/
theorem csPrefix_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsCounted A kf A.n) σ) :
    Ends lim P d csPrefix σ (25 * A.nb + 6) (CsState μ A A.nb (CsSummed A kf A.nb)) := by
  light_facts pre
  -- for t < nb
  refine Ends.csFor (CsSummed A kf) A.nb (h.imp fun _ => .start) ?round
  case round =>
    intro t c p μ' ht same summed
    have hprev := summed.starts t le_rfl
    have hcell := summed.sizes t ht le_rfl
    have hle : cntLt kf (t + 1) A.n ≤ A.n := cntLt_le _ _ _
    -- The start of bucket t + 1 is the start of bucket t plus its size.
    have hsum := cntLt_succ_left kf t A.n
    have haddr : ((A.cnt : ℤ) + t + 1).toNat = A.cnt + (t + 1) := by omega
    -- cnt[t + 1] := cnt[t + 1] + cnt[t]
    light_store (A.cnt + (t + 1)) (cntLt kf (t + 1) A.n : ℕ) using haddr, hprev, hcell
    exact ⟨c, p, _, rfl, same.update (Or.inr ⟨by omega, by omega⟩) _, summed.succ⟩

/-! ## The fourth phase: the items go to their places -/

/-- The items before item number i have been placed: they stand at their places in dst, and the
cell t of cnt holds the next free place of bucket t. -/
structure CsPlaced (A : Args) (it kf : ℕ → ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  next : ∀ t < A.nb, μ' (A.cnt + t) = (cntLt kf t A.n + cntEq kf t i : ℕ)
  done : ∀ j < i, μ' (A.dst + sortPos kf A.n j) = it j

/-- What `csPrefix` leaves: no item has been placed, and the next free places are the starts. -/
theorem CsPlaced.start (h : CsSummed A kf A.nb μ') : CsPlaced A it kf 0 μ' :=
  ⟨fun t ht => by simpa using h.starts t (by omega), fun j hj => absurd hj (by omega)⟩

/-- **Item number i is placed**: it is written to its place, and the next free place of its bucket
moves on. -/
theorem CsPlaced.succ (pre : CountSort.Pre lim μ A it kf) {i : ℕ} (hi : i < A.n)
    (h : CsPlaced A it kf i μ') :
    CsPlaced A it kf (i + 1) (Function.update (Function.update μ'
      (A.dst + sortPos kf A.n i) (it i)) (A.cnt + kf i) (sortPos kf A.n i + 1 : ℕ)) := by
  have hapart := pre.dstCnt
  have hk := pre.keyLt i hi
  have hpos := sortPos_lt kf hi
  refine ⟨fun t ht => ?_, fun j hj => ?_⟩
  · rw [cntEq_succ]
    by_cases e : kf i = t
    · subst e
      rw [Function.update_self, if_pos rfl, sortPos, Nat.add_assoc]
    · rw [if_neg e, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.next t ht
  · have hlt := sortPos_lt kf (show j < A.n by omega)
    rw [Function.update_of_ne (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hne : sortPos kf A.n j ≠ sortPos kf A.n i := fun e =>
        absurd (eq_of_sortPos_eq (by omega) hi e) (by omega)
      exact (Function.update_of_ne (by omega) _ _).trans (h.done j hj)
    · exact Function.update_self ..

/-- `csPlace`: item number j is written to dst[sortPos kf n j], and cnt[t] moves on to the start of
bucket t + 1. -/
theorem csPlace_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsSummed A kf A.nb) σ) :
    Ends lim P d csPlace σ (38 * A.n + 6) (CsState μ A A.n (CsPlaced A it kf A.n)) := by
  light_facts pre
  -- for i < n
  refine Ends.csFor (CsPlaced A it kf) A.n (h.imp fun _ => .start) ?round (hT := by simp; omega)
  case round =>
    intro i c p μ' hi same placed
    obtain ⟨hsafe, hval⟩ := csKey_gives pre same hi c p
    have hlt := pre.keyLt i hi
    have hpos : sortPos kf A.n i < A.n := sortPos_lt kf hi
    have hcell : μ' (A.cnt + kf i) = (sortPos kf A.n i : ℕ) := placed.next _ hlt
    have hitem := pre.item same hi
    -- cell := cnt + key
    light_set (A.cnt + kf i : ℕ) using hsafe, hval
    -- place := mem[cell]
    light_set (sortPos kf A.n i : ℕ) using hcell
    -- dst[place] := src[i]
    light_store (A.dst + sortPos kf A.n i) (it i) using hitem
    -- mem[cell] := place + 1
    light_store (A.cnt + kf i) (sortPos kf A.n i + 1 : ℕ)
    exact ⟨_, _, _, rfl, (same.update (Or.inl ⟨by omega, by omega⟩) _).update
        (Or.inr ⟨by omega, by omega⟩) _, placed.succ pre hi⟩

/-! ## The fifth phase: the contents of cnt move up by one cell -/

/-- While the contents of cnt move up, with the counter at s: the items stand at their places, the
cells after s of cnt hold the starts of their buckets, and the cells before s still the starts of
the next buckets.  Nothing is said about the cell s: the next write goes there. -/
structure CsShifted (A : Args) (it kf : ℕ → ℕ) (s : ℕ) (μ' : ℕ → ℤ) : Prop where
  placed : ∀ j < A.n, μ' (A.dst + sortPos kf A.n j) = it j
  moved : ∀ t ≤ A.nb, s < t → μ' (A.cnt + t) = cntLt kf t A.n
  waiting : ∀ t < s, μ' (A.cnt + t) = cntLt kf (t + 1) A.n

/-- What `csPlace` leaves, with the counter at nb: every bucket is full, so that its next free place
is the start of the next bucket. -/
theorem CsShifted.start (h : CsPlaced A it kf A.n μ') : CsShifted A it kf A.nb μ' :=
  ⟨h.done, fun t ht hlt => absurd hlt (by omega),
    fun t ht => by rw [cntLt_succ_left]; exact h.next t ht⟩

/-- A write to a cell of cnt leaves the items at their places. -/
theorem CsShifted.placed_update (pre : CountSort.Pre lim μ A it kf) {s t : ℕ}
    (h : CsShifted A it kf s μ') (ht : t ≤ A.nb) (x : ℤ) :
    ∀ j < A.n, Function.update μ' (A.cnt + t) x (A.dst + sortPos kf A.n j) = it j := by
  intro j hj
  have hapart := pre.dstCnt
  have hlt := sortPos_lt kf hj
  exact (Function.update_of_ne (by omega) _ _).trans (h.placed j hj)

/-- The cell s + 1 receives what the cell s holds. -/
theorem CsShifted.succ (pre : CountSort.Pre lim μ A it kf) {s : ℕ} (hs : s < A.nb)
    (h : CsShifted A it kf (s + 1) μ') :
    CsShifted A it kf s (Function.update μ' (A.cnt + (s + 1)) (cntLt kf (s + 1) A.n : ℕ)) := by
  refine ⟨h.placed_update pre hs _, fun t ht hst => ?_,
    fun t ht => (Function.update_of_ne (by omega) _ _).trans (h.waiting t (by omega))⟩
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hst) with hst | rfl
  · exact (Function.update_of_ne (by omega) _ _).trans (h.moved t ht hst)
  · exact Function.update_self ..

/-- The cell 0 of cnt is set to 0, the start of bucket 0. -/
theorem CsShifted.last (pre : CountSort.Pre lim μ A it kf) (same : A.Same μ μ')
    (h : CsShifted A it kf 0 μ') : CountSort.Post μ A it kf (Function.update μ' A.cnt 0) := by
  refine ⟨h.placed_update pre (Nat.zero_le _) 0, fun t ht => ?_,
    same.update (Or.inr ⟨le_rfl, by omega⟩) _⟩
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · simp
  · exact (Function.update_of_ne (by omega) _ _).trans (h.moved t ht hpos)

/-- `csShift`: from cnt[t] = start of bucket t + 1 to cnt[t] = start of bucket t. -/
theorem csShift_ends (pre : CountSort.Pre lim μ A it kf) {entry : ℤ}
    (h : CsState μ A entry (CsPlaced A it kf A.n) σ) :
    Ends lim P d csShift σ (18 * A.nb + 9) fun σ' => CountSort.Post μ A it kf σ'.mem := by
  obtain ⟨c, p, μ', rfl, same, placed⟩ := h
  light_facts pre
  -- t := nb
  light_set A.nb
  -- while 0 < t; before round r the counter is nb - r
  refine Ends.next _ (Ends.whileBlock
    (fun r => CsState μ A (A.nb - r : ℕ) (CsShifted A it kf (A.nb - r))) A.nb
    ⟨c, p, μ', rfl, same, .start placed⟩ ?round ?done (hT := le_rfl))
  case round =>
    rintro r _ hr ⟨c, p, μ', rfl, same, shifted⟩
    obtain ⟨s, hs⟩ : ∃ s, A.nb - r = s + 1 := ⟨A.nb - r - 1, by omega⟩
    rw [show A.nb - (r + 1) = s by omega]
    rw [hs] at shifted ⊢
    have hread := shifted.waiting s (by omega)
    have haddr : ((A.cnt : ℤ) + ((s : ℤ) + 1)).toNat = A.cnt + (s + 1) := by omega
    have hfrom : ((A.cnt : ℤ) + ((s : ℤ) + 1) - 1).toNat = A.cnt + s := by omega
    -- cnt[t] := cnt[t - 1]; t := t - 1
    refine ⟨by light_side, by light_side, by light_side, c, p, _, ?_,
      same.update (Or.inr ⟨by omega, by omega⟩) _, shifted.succ pre (by omega)⟩
    simp [update_frame_setLocal, haddr, hfrom, hread]
  case done =>
    rintro _ ⟨c, p, μ', rfl, same, shifted⟩
    rw [Nat.sub_self] at shifted
    -- cnt[0] := 0
    exact ⟨by light_side, by light_side, Ends.storeTo A.cnt 0 (shifted.last pre same)⟩

/-! ## The routine -/

/-- The time of countSort, for n items and keys below nb. -/
@[simp] def countSortTime (n nb : ℕ) : ℕ := 68 * n + 58 * nb + 52

/-- **countSort** sorts the items stably by their keys: the five phases, one after the other. -/
theorem countSort_meets {q : ℕ} (hq : P[q]? = some countSortBody)
    (pre : CountSort.Pre lim μ A it kf) :
    Meets lim P q d [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt] μ
      (countSortTime A.n A.nb) fun _ μ' => CountSort.Post μ A it kf μ' := by
  have start : CsState μ A 0 (fun _ => True)
      ⟨frame [A.n, A.src, A.dst, A.key, A.stride, A.off, A.nb, A.cnt], μ⟩ :=
    ⟨0, 0, μ, by rw [← frame_append_zeros _ 3]; rfl, .refl, trivial⟩
  refine .of_body hq ?_
  unfold countSortTime
  refine Ends.next _ ((csZero_ends pre start).mono le_rfl fun _ zeroed => ?_)
  refine Ends.next _ ((csCount_ends pre zeroed).mono le_rfl fun _ counted => ?_)
  refine Ends.next _ ((csPrefix_ends pre counted).mono le_rfl fun _ summed => ?_)
  refine Ends.next _ ((csPlace_ends pre summed).mono le_rfl fun _ placed => ?_)
  light_piece (csShift_ends pre placed)

end Light
