/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.RadixPass
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import Mathlib.Tactic.Linarith

/-!
# Theorem 5 in the light language: sorting the wanted positions

sortWanted(w, L, nT, tid, dgt, perm): "sort the sets W_T" (Section 2.4.4), by a radix sort of the
indices 0, …, w - 1, in O((L + 1) (w + 10) + nT) steps.  The routine writes the list 0, …, w - 1 to
perm (swInit_ends).  Then, unless w = 0, it makes L stable passes on the stored digits of the codes,
the last digit first: after r of them the list is sorted by the last r digits (swDigit_ends for one
pass, swDigits_ends for all).  One more pass, on the numbers of the tiles, sorts the list by tile
and code and leaves the number of positions in the tiles below s, for every s (swTiles_ends).
sortWantedBody_ends puts the parts together, and sortWanted_entry is the specification
SortWantedSpec that the callers use.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace SortWanted

/-- The local variables of sortWanted: the arguments w (Num), L (Levels), nT (Tiles), tid (TileOf),
dgt (Digits), perm (Perm); a counter (Idx); the unused results of the calls (Res).  A pass
(radixPass) reads w and perm from the locals 0 and 5 and writes to local 7, which are Num, Perm and
Res. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Levels : ℕ := 1
@[inherit_doc Num] abbrev Tiles : ℕ := 2
@[inherit_doc Num] abbrev TileOf : ℕ := 3
@[inherit_doc Num] abbrev Digits : ℕ := 4
@[inherit_doc Num] abbrev Perm : ℕ := 5
@[inherit_doc Num] abbrev Idx : ℕ := 6
@[inherit_doc Num] abbrev Res : ℕ := 7

end SortWanted

open SortWanted

/-- perm[i] := i for i < w. -/
def swInit : Stmt := .for Idx (v Num) (.store (v Perm +' v Idx) (v Idx))

/-- The pass on the digit whose index is in the counter. -/
def swDigit : Stmt :=
  radixPass pCountSort pCopy (v Digits) (v Levels) (v Idx) (k 10) (v Perm +' v Num +' v Num)

/-- The passes on the digits L - 1, …, 0. -/
def swDigits : Stmt :=
  .set Idx (v Levels) ;;
  .while (k 0 <' v Idx) (.set Idx (v Idx -' k 1) ;; swDigit)

/-- The pass on the numbers of the tiles. -/
def swTiles : Stmt :=
  radixPass pCountSort pCopy (v TileOf) (k 1) (k 0) (v Tiles)
    (v Perm +' v Num +' v Num +' v Tiles +' k 11)

/-- sortWanted(w, L, nT, tid, dgt, perm).  For w = 0 there are no passes on the digits: only for
w > 0 do the assumptions say that L fits in a word. -/
def sortWantedBody : Stmt := swInit ;; .ite (k 0 <' v Num) swDigits .skip ;; swTiles

/-! ## What is assumed, and the state between the passes -/

namespace SortWanted

/-- A state of sortWanted: the arguments, the counter i, the last result r, and the memory. -/
abbrev Args.state (A : Args) (i r : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [A.w, A.L, A.nT, A.tid, A.dgt, A.perm, i, r], μ'⟩

end SortWanted

/-- The list π at perm is a rearrangement of 0, …, w - 1 that is sorted by g, and only the room
cells from perm on have changed. -/
structure SwSorted (μ : ℕ → ℤ) (A : Args) (g : ℕ → ℕ) (π : List ℕ) (μ' : ℕ → ℤ) : Prop where
  same : SameOutside μ μ' A.perm A.room
  perm : π.Perm (List.range A.w)
  seg : SegN μ' A.perm π
  sorted : (π.map g).Pairwise (· ≤ ·)

/-- The state between two passes: the counter is i, and the list at perm is sorted by g. -/
def SwState (μ : ℕ → ℤ) (A : Args) (g : ℕ → ℕ) (i : ℤ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ) (π : List ℕ), σ = A.state i r μ' ∧ SwSorted μ A g π μ'

variable {μ μ' : ℕ → ℤ} {A : Args} {t x g : ℕ → ℕ} {π : List ℕ} {σ : State}

/-- The list has w entries. -/
theorem SwSorted.length (h : SwSorted μ A g π μ') : π.length = A.w := by
  simpa using h.perm.length_eq

/-- The entries of the list are below w. -/
theorem SwSorted.lt (h : SwSorted μ A g π μ') : ∀ i ∈ π, i < A.w :=
  fun i hi => by simpa using h.perm.mem_iff.1 hi

/-! ## The list 0, …, w - 1 -/

/-- The first j cells of perm hold 0, …, j - 1, and nothing outside the w cells from perm has
changed. -/
def SwInitInv (μ : ℕ → ℤ) (A : Args) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < j, μ' (A.perm + i) = i) ∧ SameOutside μ μ' A.perm A.w

/-- swInit: the list 0, …, w - 1 stands at perm; it is sorted by the last 0 digits. -/
theorem swInit_ends (std : Std lim) (pre : SwPre lim μ A t x) (idx r : ℤ) :
    Ends lim P d swInit (A.state idx r μ) (13 * A.w + 6)
      (SwState μ A (fun i => x i % 10 ^ 0) A.w) := by
  have hw := std.space_le
  have hspace := pre.space
  have hroom := A.room_eq
  -- for i < w
  refine Ends.forFrame (SwInitInv μ A) A.w ⟨fun i hi => absurd hi (by omega), .refl⟩
    ?round ?done
  case round =>
    rintro i μ' hi ⟨filled, rest⟩
    -- perm[i] := i
    light_store (A.perm + i) i
    refine ⟨rfl, fun j hj => ?_, rest.update ⟨by omega, by omega⟩ _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (filled j hj)
    · exact Function.update_self ..
  case done =>
    rintro μ' ⟨filled, rest⟩
    exact ⟨r, μ', List.range A.w, rfl,
      { same := rest.mono le_rfl (by omega)
        perm := .refl _
        seg := fun i hi => by simpa using filled i (by simpa using hi)
        sorted := by simp [Nat.mod_one, List.pairwise_replicate] }⟩

/-! ## The passes on the digits -/

/-- The digit with index L - 1 - r is the digit number r from the least significant. -/
theorem digit_from_end {L r : ℕ} (hr : r < L) (x : ℕ) :
    digit 10 L x (L - (r + 1)) = x / 10 ^ r % 10 := by
  unfold digit
  rw [show L - 1 - (L - (r + 1)) = r by omega]

/-- The layout of the pass on digit number r from the least significant. -/
abbrev SortWanted.Args.digitPass (A : Args) (r : ℕ) : RadixPass.Args :=
  ⟨A.w, A.perm, A.dgt, A.L, A.L - (r + 1), 10, A.perm + A.w + A.w, A.room⟩

/-- What the pass on digit number r assumes: the digits still stand where they stood. -/
theorem SwSorted.digitPre (std : Std lim) (pre : SwPre lim μ A t x) (h : SwSorted μ A g π μ')
    {r : ℕ} (hr : r < A.L) : RadixPass.Pre lim μ' (A.digitPass r) π fun i => x i / 10 ^ r % 10 := by
  have hbefore := pre.dgtBefore
  have hroom := A.room_eq
  have hidx : ∀ i < A.w, i * A.L + (A.L - (r + 1)) < A.w * A.L := fun i hi =>
    Nat.mul_add_lt_mul hi (by omega)
  exact
    { hw := std.space_le
      len := h.length
      lt := h.lt
      seg := h.seg
      keyBefore := fun i hi => by
        have := hidx i hi
        dsimp only
        omega
      keys := fun i hi => by
        have hlt := hidx i hi
        dsimp only
        rw [Nat.add_assoc, h.same _ (Or.inl (by omega)), ← Nat.add_assoc,
          (pre.codes i hi).getElem (by simp [digitList]; omega)]
        simp only [digitList, List.getElem_map, List.getElem_range]
        rw [digit_from_end hr]
      keyLt := fun i _ => Nat.mod_lt _ (by omega)
      cntAfter := by dsimp only; omega
      cntIn := by dsimp only; omega
      space := pre.space }

/-- After the pass on digit number r, a list that was sorted by the last r digits is sorted by the
last r + 1 digits. -/
theorem SwSorted.digit_succ {μ'' : ℕ → ℤ} {r : ℕ} (h : SwSorted μ A (fun i => x i % 10 ^ r) π μ')
    (passed : RadixPass.Post μ' (A.digitPass r) π (fun i => x i / 10 ^ r % 10) μ'') :
    ∃ π', SwSorted μ A (fun i => x i % 10 ^ (r + 1)) π' μ'' := by
  obtain ⟨same, -, π', stable, seg⟩ := passed
  exact ⟨π',
    { same := h.same.trans same
      perm := stable.perm.trans h.perm
      seg := seg
      sorted := by
        simpa only [Nat.mod_pow_succ, Nat.add_comm, Nat.mul_comm] using
          stable.sorted (B := 10 ^ r) (fun i _ => Nat.mod_lt _ (by positivity)) h.sorted }⟩

/-- One pass: the counter holds the index L - 1 - r of digit number r. -/
theorem swDigit_ends (hpc : P[pCountSort]? = some countSortBody) (hpp : P[pCopy]? = some copyBody)
    (hd : d < lim.depth) (std : Std lim) (pre : SwPre lim μ A t x) {r : ℕ} (hr : r < A.L)
    (h : SwState μ A (fun i => x i % 10 ^ r) (A.L - (r + 1) : ℕ) σ) :
    Ends lim P d swDigit σ (84 * A.w + 58 * 10 + 81)
      (SwState μ A (fun i => x i % 10 ^ (r + 1)) (A.L - (r + 1) : ℕ)) := by
  obtain ⟨res, μ', π, rfl, sorted⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hspace := pre.space
  have hroom := A.room_eq
  -- the pass on the digit with index i
  refine (radixPass_ends hpc hpp (sorted.digitPre std pre hr) (hT := by light_time)).mono le_rfl ?_
  rintro ⟨_, μ''⟩ ⟨⟨res', rfl⟩, passed⟩
  obtain ⟨π', sorted'⟩ := sorted.digit_succ passed
  exact ⟨res', μ'', π', by rw [update_frame_setLocal]; rfl, sorted'⟩

/-- swDigits: after the L passes the list is sorted by the codes. -/
theorem swDigits_ends (hpc : P[pCountSort]? = some countSortBody) (hpp : P[pCopy]? = some copyBody)
    (hd : d < lim.depth) (std : Std lim) (pre : SwPre lim μ A t x) (hpos : 0 < A.w) {idx : ℤ}
    (h : SwState μ A (fun i => x i % 10 ^ 0) idx σ) :
    Ends lim P d swDigits σ (A.L * (84 * A.w + 58 * 10 + 89) + 6)
      (SwState μ A (fun i => x i % 10 ^ A.L) (0 : ℕ)) := by
  obtain ⟨res, μ', π, rfl, sorted⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hspace := pre.space
  have hbefore := pre.dgtBefore
  have hlevels : A.L ≤ A.w * A.L := Nat.le_mul_of_pos_left _ hpos
  -- i := L
  light_set A.L
  -- while 0 < i; before round r the counter is L - r; a round is 4 steps for i := i - 1 and a pass
  refine Ends.whileConst (fun r => SwState μ A (fun i => x i % 10 ^ r) (A.L - r : ℕ)) A.L
    (4 + (84 * A.w + 58 * 10 + 81)) ⟨res, μ', π, rfl, sorted⟩ ?round ?done
    (by simp; ring_nf; omega)
  case round =>
    rintro r _ hr ⟨res, μ', π, rfl, sorted⟩
    refine ⟨by light_side, by light_side, ?_⟩
    -- i := i - 1
    light_set (A.L - (r + 1) : ℕ)
    -- the pass on the digit with index i
    exact (swDigit_ends hpc hpp hd std pre hr ⟨res, μ', π, rfl, sorted⟩).mono (by simp) fun _ h => h
  case done =>
    rintro _ ⟨res, μ', π, rfl, sorted⟩
    rw [Nat.sub_self]
    exact ⟨by light_side, by light_side, res, μ', π, rfl, sorted⟩

/-! ## The pass on the tiles -/

/-- The layout of the pass on the numbers of the tiles. -/
abbrev SortWanted.Args.tilePass (A : Args) : RadixPass.Args :=
  ⟨A.w, A.perm, A.tid, 1, 0, A.nT, A.perm + A.w + A.w + A.nT + 11, A.room⟩

/-- What the pass on the tiles assumes: the numbers of the tiles still stand where they stood. -/
theorem SwSorted.tilePre (std : Std lim) (pre : SwPre lim μ A t x) (h : SwSorted μ A g π μ') :
    RadixPass.Pre lim μ' A.tilePass π t := by
  have hbefore := pre.tidBefore
  have hroom := A.room_eq
  exact
    { hw := std.space_le
      len := h.length
      lt := h.lt
      seg := h.seg
      keyBefore := fun i hi => by dsimp only at hi ⊢; omega
      keys := fun i hi => by
        dsimp only at hi ⊢
        rw [Nat.mul_one, Nat.add_zero, h.same _ (Or.inl (by omega))]
        exact pre.tiles i hi
      keyLt := pre.tileLt
      cntAfter := by dsimp only; omega
      cntIn := by dsimp only; omega
      space := pre.space }

/-- What sortWanted achieves: the list at perm sorts the positions by tile and code, the cell s
after the scratch space holds the number of positions in the tiles below s, and only the room cells
from perm on have changed. -/
def SwDone (μ : ℕ → ℤ) (A : Args) (t x : ℕ → ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∃ π : List ℕ, π.Perm (List.range A.w) ∧ SegN μ' A.perm π ∧
      (π.map fun i => t i * 10 ^ A.L + x i).Pairwise (· ≤ ·)) ∧
    (∀ s ≤ A.nT, μ' (A.perm + 2 * A.w + (A.nT + 11) + s)
      = (((List.range A.w).filter fun i => t i < s).length : ℕ)) ∧
    SameOutside μ μ' A.perm A.room

/-- After the pass on the tiles, a list that was sorted by the codes is sorted by tile and code, and
the counters of the pass count the positions in the tiles below s. -/
theorem SwSorted.tile_succ {μ'' : ℕ → ℤ} (pre : SwPre lim μ A t x)
    (h : SwSorted μ A (fun i => x i % 10 ^ A.L) π μ')
    (passed : RadixPass.Post μ' A.tilePass π t μ'') :
    SwDone μ A t x μ'' := by
  obtain ⟨same, starts, π', stable, seg⟩ := passed
  dsimp only at starts
  have hperm := stable.perm.trans h.perm
  refine ⟨⟨π', hperm, seg, ?_⟩, fun s hs => ?_, h.same.trans same⟩
  · rw [List.map_congr_left (g := fun i => t i * 10 ^ A.L + x i % 10 ^ A.L)]
    · exact stable.sorted (B := 10 ^ A.L) (fun i _ => Nat.mod_lt _ (by positivity)) h.sorted
    · intro i hi
      rw [Nat.mod_eq_of_lt (pre.codeLt i (by simpa using hperm.mem_iff.1 hi))]
  · rw [show A.perm + 2 * A.w + (A.nT + 11) + s = A.perm + A.w + A.w + A.nT + 11 + s by omega,
      starts s hs, show cntLt (keyAt t π) s A.w = cntLt (keyAt t π) s π.length by rw [h.length],
      cntLt_keyAt, h.perm.countP_eq, List.countP_eq_length_filter]

/-- swTiles: the last pass. -/
theorem swTiles_ends (hpc : P[pCountSort]? = some countSortBody) (hpp : P[pCopy]? = some copyBody)
    (hd : d < lim.depth) (std : Std lim) (pre : SwPre lim μ A t x) {idx : ℤ}
    (h : SwState μ A (fun i => x i % 10 ^ A.L) idx σ) :
    Ends lim P d swTiles σ (84 * A.w + 58 * A.nT + 85) fun σ' => SwDone μ A t x σ'.mem := by
  obtain ⟨res, μ', π, rfl, sorted⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hspace := pre.space
  have hroom := A.room_eq
  -- the pass on the numbers of the tiles
  exact (radixPass_ends hpc hpp (sorted.tilePre std pre) (hT := by light_time)).mono le_rfl
    fun _ ⟨_, passed⟩ => sorted.tile_succ pre passed

/-! ## The routine -/

/-- The body of sortWanted achieves SwDone; the time is the sum of the times of the three parts and
of the test. -/
theorem sortWantedBody_ends (hpc : P[pCountSort]? = some countSortBody)
    (hpp : P[pCopy]? = some copyBody) (hd : d < lim.depth) (std : Std lim)
    (pre : SwPre lim μ A t x) :
    Ends lim P d sortWantedBody ⟨frame [A.w, A.L, A.nT, A.tid, A.dgt, A.perm], μ⟩
      (13 * A.w + 6 + 4 + (A.L * (84 * A.w + 58 * 10 + 89) + 6) + (84 * A.w + 58 * A.nT + 85))
      fun σ' => SwDone μ A t x σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  -- The two further locals, the counter and the result, are 0 at the start.
  rw [← frame_append_zeros _ 2]
  -- perm[i] := i for i < w
  light_piece (swInit_ends std pre 0 0) with _ ⟨res, μ', π, rfl, sorted⟩
  -- if 0 < w
  refine Ends.iteThen (fun hpos => ?_) (fun hzero => ?_)
  · -- the passes on the digits, then the pass on the tiles
    refine Ends.next _ ((swDigits_ends hpc hpp hd std pre (by simpa using hpos)
      ⟨res, μ', π, rfl, sorted⟩).mono le_rfl fun _ h => ?_)
    exact (swTiles_ends hpc hpp hd std pre h).mono (by simp; omega) fun _ h => h
  · -- skip, then the pass on the tiles; the empty list is sorted
    obtain rfl : π = [] := List.length_eq_zero_iff.1 (by
      have := sorted.length
      simp at hzero
      omega)
    refine Ends.next 0 (Ends.skip ?_)
    exact (swTiles_ends hpc hpp hd std pre
      ⟨res, μ', [], rfl, { sorted with sorted := by simp }⟩).mono (by simp; omega) fun _ h => h

/-- **sortWanted** meets its entry of the map, with the constant 97. -/
theorem sortWanted_entry (std : Std lim) (hpc : P[pCountSort]? = some countSortBody)
    (hpp : P[pCopy]? = some copyBody) (hps : P[pSortWanted]? = some sortWantedBody) {c : ℕ}
    (hc : 97 ≤ c) : SortWantedSpec lim P c := by
  intro A μ t x pre d hd
  refine .mono_const (.of_body hps
    ((sortWantedBody_ends hpc hpp (by omega) std pre).mono ?_ fun _ h => h)) hc
  -- 97 ((L + 1) (w + 10) + nT + 1) = L (97 w + 970) + 97 w + 97 nT + 1067
  have hmul : A.L * (84 * A.w + 58 * 10 + 89) ≤ A.L * (97 * A.w + 970) :=
    Nat.mul_le_mul_left A.L (by omega)
  have hexp : 97 * ((A.L + 1) * (A.w + 10) + A.nT + 1)
      = A.L * (97 * A.w + 970) + 97 * A.w + 97 * A.nT + 1067 := by ring
  rw [hexp]
  linarith [hmul]

end Light.Sec2
