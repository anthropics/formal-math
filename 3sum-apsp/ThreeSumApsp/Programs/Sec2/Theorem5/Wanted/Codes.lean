/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The tile and the output string of each wanted position

Section 2.4.4: "Each wanted position (I, J) ∈ W lies in one tile T and is indexed by one output
string of T".  For the i-th wanted position (I, J) the routine wanted(w, L, Lo, N, K0, nB, aWI, aWJ,
band, dig3, mask, tid) writes the number BAND[I] · nB + BAND[J] of its tile to tid + i, the code
Spec.outCodeOfPos L m I J of its output string to tid + w + i, and the L digits of the code to
tid + 2 w + i L.  The code is formed by Horner's rule in base 10 while walking the mask of the
subset number BLOCK[I] · K₀ + BLOCK[J]: digit 9 at a level of the subset, and otherwise 3 x + y for
the next base-3 digits x, y of the offsets of I and J.  O(L) steps for each position.

In the paper's letters (Sections 2.3.3 and 2.3.4): D = 4^m, N₀ = 3^(L-m) is the side of a block,
K₀ = ⌊√binom(L, m)⌋ is the number of blocks along the side of a tile, and the offset of I is
I mod N₀, the place of I within its block.

A round of the loop over the positions has three parts, each with its lemma: `prepBlock_ends` (the
position, its tile and the three addresses), `levelLoop_ends` (the walk along the mask; one level is
`levelRound_ends`) and `finishBlock_ends` (the tile and the code are stored).  `wantedRound_ends`
puts them together, `wantedBody_ends` is the loop, and `wanted_entry` is the result for the callers:
a call of procedure `pWanted` does what `WantedSpec` says.
-/

@[expose] public section

namespace Light.Sec2.Wanted

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace Local

/-- The number w of wanted positions. -/
abbrev WW : ℕ := 0
/-- The number L of levels. -/
abbrev LL : ℕ := 1
/-- Lo = L - m, the number of base-3 digits of an offset. -/
abbrev LO : ℕ := 2
/-- The size N. -/
abbrev NN : ℕ := 3
/-- K₀, the number of blocks along the side of a tile. -/
abbrev KK : ℕ := 4
/-- The number nB of bands. -/
abbrev NB : ℕ := 5
/-- The rows of the wanted positions. -/
abbrev AWI : ℕ := 6
/-- The columns of the wanted positions. -/
abbrev AWJ : ℕ := 7
/-- The table BAND, followed by the table BLOCK. -/
abbrev BAND : ℕ := 8
/-- The base-3 digits of the offsets. -/
abbrev DIG3 : ℕ := 9
/-- The masks of the subsets. -/
abbrev MASK : ℕ := 10
/-- Where the numbers of the tiles, the codes and the digits are written. -/
abbrev TID : ℕ := 11
/-- The number i of the position. -/
abbrev CI : ℕ := 12
/-- The row I. -/
abbrev PI : ℕ := 13
/-- The column J. -/
abbrev PJ : ℕ := 14
/-- The address of the mask. -/
abbrev AM : ℕ := 15
/-- The address of the next digit of the offset of I. -/
abbrev AI : ℕ := 16
/-- The address of the next digit of the offset of J. -/
abbrev AJ : ℕ := 17
/-- The number formed so far. -/
abbrev ACC : ℕ := 18
/-- The level. -/
abbrev LEV : ℕ := 19
/-- The address of the row of digits. -/
abbrev ROW : ℕ := 20
/-- The digit. -/
abbrev DIG : ℕ := 21
/-- The number of the tile. -/
abbrev TILE : ℕ := 22

end Local

open Local

/-- The digit is stored and appended to the number, and the level moves on. -/
def levelTail : Stmt :=
  .store (v ROW +' v LEV) (v DIG) ;;
  .set ACC (v ACC *' k 10 +' v DIG) ;;
  .set LEV (v LEV +' k 1)

/-- The digit of the level: 9 at a level of the subset, and otherwise 3 x + y for the next digits
x, y of the two offsets. -/
def levelDigit : Stmt :=
  .ite (M (v AM +' v LEV) <' k 1)
    (.set DIG (k 3 *' M (v AI) +' M (v AJ)) ;; .set AI (v AI +' k 1) ;; .set AJ (v AJ +' k 1))
    (.set DIG (k 9))

/-- One level of the walk along the mask. -/
def levelRound : Stmt :=
  levelDigit ;; levelTail

/-- The walk along the mask. -/
def levelLoop : Stmt :=
  .while (v LEV <' v LL) levelRound

/-- Before the walk: the position, the number of its tile, and the three addresses. -/
def prepBlock : Stmt :=
  .set PI (M (v AWI +' v CI)) ;; .set PJ (M (v AWJ +' v CI)) ;;
  .set TILE (M (v BAND +' v PI) *' v NB +' M (v BAND +' v PJ)) ;;
  .set AM (v MASK +' (M (v BAND +' v NN +' v PI) *' v KK +' M (v BAND +' v NN +' v PJ)) *' v LL) ;;
  .set AI (v DIG3 +' v PI *' v LO) ;; .set AJ (v DIG3 +' v PJ *' v LO) ;;
  .set ACC (k 0) ;; .set LEV (k 0)

/-- After the walk: the number of the tile and the code are stored, and the counters move on. -/
def finishBlock : Stmt :=
  .store (v TID +' v CI) (v TILE) ;;
  .store (v TID +' v WW +' v CI) (v ACC) ;;
  .set CI (v CI +' k 1) ;; .set ROW (v ROW +' v LL)

/-- wanted(w, L, Lo, N, K0, nB, aWI, aWJ, band, dig3, mask, tid). -/
def wantedBody : Stmt :=
  .set CI (k 0) ;; .set ROW (v TID +' v WW +' v WW) ;;
  .while (v CI <' v WW) (prepBlock ;; levelLoop ;; finishBlock)

/-- The time of wanted. -/
def tWanted (w L : ℕ) : ℕ := w * (42 * L + 86) + 12

/-- The twelve arguments of wanted. -/
structure Args where
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The number of levels. -/
  L : ℕ
  /-- The number of base-3 digits of an offset. -/
  Lo : ℕ
  /-- The size. -/
  N : ℕ
  /-- The number of blocks along the side of a tile. -/
  K₀ : ℕ
  /-- The number of bands. -/
  nB : ℕ
  /-- The rows of the wanted positions. -/
  aWI : ℕ
  /-- The columns of the wanted positions. -/
  aWJ : ℕ
  /-- The tables BAND and BLOCK. -/
  band : ℕ
  /-- The base-3 digits of the offsets. -/
  dig3 : ℕ
  /-- The masks. -/
  mask : ℕ
  /-- The output. -/
  tid : ℕ

/-- The state of wanted: the arguments, the number i of the position, the address row of its row of
digits, and what the other locals hold. -/
abbrev wstate (a : Args) (i : ℕ) (pI pJ am aI aJ acc lev : ℤ) (row : ℕ) (dig tile : ℤ)
    (μ : ℕ → ℤ) : State :=
  ⟨frame [a.w, a.L, a.Lo, a.N, a.K₀, a.nB, a.aWI, a.aWJ, a.band, a.dig3, a.mask, a.tid, i, pI, pJ,
    am, aI, aJ, acc, lev, row, dig, tile], μ⟩

/-! ## The walk along one mask -/

/-- What the walk along one mask needs: the mask `mk` at `am`, with `m` levels in the subset and
`Lo` outside it, and the base-3 digits `rI` and `rJ` of the two offsets at `aI` and `aJ`, all below
the row of digits that it writes. -/
structure LevelPre (lim : Limits) (μ : ℕ → ℤ) (m : ℕ) (mk : List Bool) (rI rJ : List ℕ)
    (L Lo am aI aJ row : ℕ) : Prop where
  len : mk.length = L
  cntIn : mk.count true = m
  cnt : mk.count false = Lo
  hmk : ∀ l < L, μ (am + l) = if mk.getD l false then 1 else 0
  segI : SegN μ aI rI
  segJ : SegN μ aJ rJ
  lenI : rI.length = Lo
  lenJ : rJ.length = Lo
  ltI : ∀ x ∈ rI, x < 3
  ltJ : ∀ x ∈ rJ, x < 3
  am_le : am + L ≤ row
  aI_le : aI + Lo ≤ row
  aJ_le : aJ + Lo ≤ row
  row_le : row + L ≤ lim.space
  pow_le : ((10 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word

variable {μ μ' : ℕ → ℤ} {m : ℕ} {mk : List Bool} {rI rJ : List ℕ} {L Lo am aI aJ row l : ℕ}

/-- The order of the regions of the memory. -/
theorem LevelPre.sizes (pre : LevelPre lim μ m mk rI rJ L Lo am aI aJ row) :
    am + L ≤ row ∧ aI + Lo ≤ row ∧ aJ + Lo ≤ row ∧ row + L ≤ lim.space :=
  ⟨pre.am_le, pre.aI_le, pre.aJ_le, pre.row_le⟩

/-- The number of levels outside the subset among the first `l` levels: so many digits of each
offset have been used. -/
def usedAt (mk : List Bool) (l : ℕ) : ℕ := (mk.take l).count false

/-- The number formed by Horner's rule from the first `l` digits of the output string. -/
def accAt (m : ℕ) (mk : List Bool) (rI rJ : List ℕ) (l : ℕ) : ℕ :=
  ThreeSumApsp.ofDigitList 10 ((Spec.outDigits m mk rI rJ).take l)

/-- The digit of the output string at level `l`. -/
def digitAt (m : ℕ) (mk : List Bool) (rI rJ : List ℕ) (l : ℕ) : ℕ :=
  (Spec.outDigits m mk rI rJ).getD l 0

/-- The first l digits have been written, and nothing else has changed. -/
structure LevelMem (μ μ' : ℕ → ℤ) (m : ℕ) (mk : List Bool) (rI rJ : List ℕ) (L row l : ℕ) :
    Prop where
  done : SegN μ' row ((Spec.outDigits m mk rI rJ).take l)
  rest : SameOutside μ μ' row L

/-- One more digit is written. -/
theorem LevelMem.write (h : LevelMem μ μ' m mk rI rJ L row l) (hlen : mk.length = L) (hl : l < L) :
    LevelMem μ (Function.update μ' (row + l) (digitAt m mk rI rJ l)) m mk rI rJ L row (l + 1) :=
  ⟨h.done.take_succ (by rw [Spec.length_outDigits, hlen]; exact hl),
    h.rest.update ⟨by omega, by omega⟩ _⟩

/-- One more digit, and the number formed from `l + 1` digits fits in a word. -/
theorem LevelPre.accAt_succ (pre : LevelPre lim μ m mk rI rJ L Lo am aI aJ row) (hl : l < L) :
    accAt m mk rI rJ (l + 1) = accAt m mk rI rJ l * 10 + digitAt m mk rI rJ l ∧
      (accAt m mk rI rJ (l + 1) : ℤ) ≤ lim.word := by
  have hlen : l + 1 ≤ (Spec.outDigits m mk rI rJ).length := by
    rw [Spec.length_outDigits, pre.len]
    exact hl
  have hlt := ThreeSumApsp.ofDigitList_lt ((Spec.outDigits m mk rI rJ).take (l + 1)) fun d hd =>
    Spec.lt_of_mem_outDigits pre.ltI pre.ltJ d (List.mem_of_mem_take hd)
  rw [List.length_take, Nat.min_eq_left hlen] at hlt
  have hpow : 10 ^ (l + 1) ≤ 10 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨ThreeSumApsp.ofDigitList_take_succ 10 _ hlen,
    le_trans (by exact_mod_cast (hlt.le.trans hpow)) pre.pow_le⟩

/-- The invariant of the walk, before level l. -/
def LevelInv (a : Args) (i : ℕ) (pI pJ tile : ℤ) (μ : ℕ → ℤ) (m : ℕ) (mk : List Bool)
    (rI rJ : List ℕ) (am aI aJ row l : ℕ) (σ : State) : Prop :=
  ∃ (dig : ℤ) (μ' : ℕ → ℤ),
    σ = wstate a i pI pJ am (aI + usedAt mk l : ℕ) (aJ + usedAt mk l : ℕ) (accAt m mk rI rJ l) l row
      dig tile μ' ∧
    LevelMem μ μ' m mk rI rJ a.L row l

variable {a : Args} {i : ℕ} {pI pJ tile : ℤ}

/-- The end of a level: the digit of level l is in DIG, and the two addresses have moved. -/
theorem levelTail_ends (std : Std lim) (pre : LevelPre lim μ m mk rI rJ a.L Lo am aI aJ row)
    (h : LevelMem μ μ' m mk rI rJ a.L row l) (hl : l < a.L) :
    Ends lim P d levelTail
      (wstate a i pI pJ am (aI + usedAt mk (l + 1) : ℕ) (aJ + usedAt mk (l + 1) : ℕ)
        (accAt m mk rI rJ l) l row (digitAt m mk rI rJ l) tile μ') 15
      (LevelInv a i pI pJ tile μ m mk rI rJ am aI aJ row (l + 1)) := by
  have hw := std.space_le
  have h100 := std.const_le
  have hsizes := pre.sizes
  obtain ⟨hnext, hacc⟩ := pre.accAt_succ hl
  rw [hnext] at hacc
  push_cast at hacc
  unfold levelTail
  -- mem[row + lev] := dig
  light_store (row + l) (digitAt m mk rI rJ l)
  -- acc := acc * 10 + dig
  refine Ends.setToThen (accAt m mk rI rJ (l + 1) : ℕ) ?_ (by rw [hnext]; simp [abs_le]; omega)
  -- lev := lev + 1
  light_set (l + 1 : ℕ)
  exact ⟨_, _, rfl, h.write pre.len hl⟩

/-- The mask can be read at any time. -/
theorem LevelPre.readMask (pre : LevelPre lim μ m mk rI rJ L Lo am aI aJ row)
    (h : LevelMem μ μ' m mk rI rJ L row l) (hl : l < L) :
    μ' (am + l) = if mk.getD l false then 1 else 0 := by
  have hsizes := pre.sizes
  rw [h.rest _ (by omega)]
  exact pre.hmk l hl

/-- A level outside the subset: the digit is 3 x + y for the next digits x, y of the two offsets,
and the two addresses move on. -/
theorem levelDigit_outside (std : Std lim) (pre : LevelPre lim μ m mk rI rJ a.L Lo am aI aJ row)
    (h : LevelMem μ μ' m mk rI rJ a.L row l) (hl : l < a.L) (hout : mk.getD l false = false)
    (dig : ℤ) :
    Ends lim P d
      (.set DIG (k 3 *' M (v AI) +' M (v AJ)) ;; .set AI (v AI +' k 1) ;; .set AJ (v AJ +' k 1))
      (wstate a i pI pJ am (aI + usedAt mk l : ℕ) (aJ + usedAt mk l : ℕ) (accAt m mk rI rJ l) l row
        dig tile μ') 16
      (· = wstate a i pI pJ am (aI + usedAt mk (l + 1) : ℕ) (aJ + usedAt mk (l + 1) : ℕ)
        (accAt m mk rI rJ l) l row (digitAt m mk rI rJ l) tile μ') := by
  have hw := std.space_le
  have h100 := std.const_le
  have hsizes := pre.sizes
  have hlen : l < mk.length := pre.len ▸ hl
  have hlt : usedAt mk l < Lo := pre.cnt ▸ List.count_take_lt hlen false hout
  have hnext : usedAt mk (l + 1) = usedAt mk l + 1 := by
    unfold usedAt
    rw [List.count_take_succ_getD mk false hlen false, if_pos hout]
  have hreadI : μ' (aI + usedAt mk l) = (rI.getD (usedAt mk l) 0 : ℕ) := by
    rw [h.rest _ (by omega)]
    exact pre.segI.read (pre.lenI ▸ hlt)
  have hreadJ : μ' (aJ + usedAt mk l) = (rJ.getD (usedAt mk l) 0 : ℕ) := by
    rw [h.rest _ (by omega)]
    exact pre.segJ.read (pre.lenJ ▸ hlt)
  have hI3 : rI.getD (usedAt mk l) 0 < 3 := List.getD_of_forall_mem (by norm_num) pre.ltI _
  have hJ3 : rJ.getD (usedAt mk l) 0 < 3 := List.getD_of_forall_mem (by norm_num) pre.ltJ _
  have hdigit : digitAt m mk rI rJ l = 3 * rI.getD (usedAt mk l) 0 + rJ.getD (usedAt mk l) 0 :=
    Spec.getD_outDigits_of_false (pre.lenI.trans pre.cnt.symm) (pre.lenJ.trans pre.cnt.symm) hlen
      hout
  generalize rI.getD (usedAt mk l) 0 = x at hreadI hI3 hdigit
  generalize rJ.getD (usedAt mk l) 0 = y at hreadJ hJ3 hdigit
  -- dig := 3 * mem[ai] + mem[aj]
  light_set (digitAt m mk rI rJ l : ℕ) using hreadI, hreadJ, hdigit
  -- ai := ai + 1; aj := aj + 1
  light_set (aI + usedAt mk (l + 1) : ℕ) using hnext
  light_set (aJ + usedAt mk (l + 1) : ℕ) using hnext
  rfl

/-- The digit of level l is formed. -/
theorem levelDigit_ends (std : Std lim) (pre : LevelPre lim μ m mk rI rJ a.L Lo am aI aJ row)
    (h : LevelMem μ μ' m mk rI rJ a.L row l) (hl : l < a.L) (dig : ℤ) :
    Ends lim P d levelDigit
      (wstate a i pI pJ am (aI + usedAt mk l : ℕ) (aJ + usedAt mk l : ℕ) (accAt m mk rI rJ l) l row
        dig tile μ') 23
      (· = wstate a i pI pJ am (aI + usedAt mk (l + 1) : ℕ) (aJ + usedAt mk (l + 1) : ℕ)
        (accAt m mk rI rJ l) l row (digitAt m mk rI rJ l) tile μ') := by
  have hw := std.space_le
  have h100 := std.const_le
  have hsizes := pre.sizes
  have hmask := pre.readMask h hl
  have hlen : l < mk.length := pre.len ▸ hl
  unfold levelDigit
  -- if mem[am + lev] < 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · replace hc : μ' (am + l) < 1 := by simpa using hc
    have hout : mk.getD l false = false := by
      by_contra hin
      rw [hmask, if_pos (by simpa using hin)] at hc
      omega
    exact levelDigit_outside std pre h hl hout dig
  · -- a level of the subset
    replace hc : ¬ μ' (am + l) < 1 := by simpa using hc
    have hin : mk.getD l false = true := by
      by_contra hout
      rw [hmask, if_neg hout] at hc
      omega
    have hdigit : digitAt m mk rI rJ l = 9 := Spec.getD_outDigits_of_true pre.cntIn hlen hin
    have hnext : usedAt mk (l + 1) = usedAt mk l := by
      unfold usedAt
      rw [List.count_take_succ_getD mk false hlen false, if_neg (by rw [hin]; decide), Nat.add_zero]
    -- dig := 9
    rw [hnext]
    light_set (digitAt m mk rI rJ l : ℕ) using hdigit
    rfl

/-- **One level of the walk.** -/
theorem levelRound_ends (std : Std lim) (pre : LevelPre lim μ m mk rI rJ a.L Lo am aI aJ row)
    (hl : l < a.L) {σ : State} (hσ : LevelInv a i pI pJ tile μ m mk rI rJ am aI aJ row l σ) :
    Ends lim P d levelRound σ 38 (LevelInv a i pI pJ tile μ m mk rI rJ am aI aJ row (l + 1)) := by
  obtain ⟨dig, μ', rfl, h⟩ := hσ
  refine Ends.next _ ((levelDigit_ends std pre h hl dig).mono le_rfl ?_)
  rintro _ rfl
  exact levelTail_ends std pre h hl

/-- **The walk along one mask** writes the digits and leaves the number in ACC. -/
theorem levelLoop_ends (std : Std lim) (pre : LevelPre lim μ m mk rI rJ a.L Lo am aI aJ row)
    (dig : ℤ) :
    Ends lim P d levelLoop (wstate a i pI pJ am aI aJ 0 0 row dig tile μ) (42 * a.L + 4)
      (LevelInv a i pI pJ tile μ m mk rI rJ am aI aJ row a.L) := by
  -- while lev < L
  refine Ends.whileConst (LevelInv a i pI pJ tile μ m mk rI rJ am aI aJ row) a.L 38 ?start ?round
    ?done (by simp; omega)
  case start => exact ⟨dig, μ, by simp [usedAt, accAt], by simp [SegN, Seg], .refl⟩
  case round =>
    intro l σ hl hσ
    obtain ⟨dig', μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using hl, levelRound_ends std pre hl hσ⟩
  case done =>
    intro σ hσ
    obtain ⟨dig', μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simp, hσ⟩

/-! ## Before and after the walk -/

/-- What the block before the walk needs: the values it reads, and room for the numbers it forms.
(In, Jn) is the position, bI and bJ are its bands, gI and gJ its blocks. -/
structure PrepPre (lim : Limits) (μ : ℕ → ℤ) (a : Args) (i In Jn bI bJ gI gJ : ℕ) : Prop where
  vI : μ (a.aWI + i) = In
  vJ : μ (a.aWJ + i) = Jn
  vbI : μ (a.band + In) = bI
  vbJ : μ (a.band + Jn) = bJ
  vgI : μ (a.band + a.N + In) = gI
  vgJ : μ (a.band + a.N + Jn) = gJ
  hWI : a.aWI + i < lim.space
  hWJ : a.aWJ + i < lim.space
  hbI : a.band + a.N + In < lim.space
  hbJ : a.band + a.N + Jn < lim.space
  htile : ((bI * a.nB + bJ : ℕ) : ℤ) ≤ lim.word
  hsub : ((gI * a.K₀ + gJ : ℕ) : ℤ) ≤ lim.word
  hmask : ((a.mask + (gI * a.K₀ + gJ) * a.L : ℕ) : ℤ) ≤ lim.space
  hdI : ((a.dig3 + In * a.Lo : ℕ) : ℤ) ≤ lim.space
  hdJ : ((a.dig3 + Jn * a.Lo : ℕ) : ℤ) ≤ lim.space

/-- **The block before the walk.** -/
theorem prepBlock_ends {In Jn bI bJ gI gJ : ℕ} (std : Std lim)
    (pre : PrepPre lim μ a i In Jn bI bJ gI gJ) (x₁ x₂ x₃ x₄ x₅ x₆ x₇ dig x₈ : ℤ) :
    Ends lim P d prepBlock (wstate a i x₁ x₂ x₃ x₄ x₅ x₆ x₇ row dig x₈ μ) 58
      (· = wstate a i In Jn (a.mask + (gI * a.K₀ + gJ) * a.L : ℕ) (a.dig3 + In * a.Lo : ℕ)
        (a.dig3 + Jn * a.Lo : ℕ) 0 0 row dig (bI * a.nB + bJ : ℕ) μ) := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := And.intro pre.hWI (And.intro pre.hWJ (And.intro pre.hbI pre.hbJ))
  have hnumbers := And.intro pre.htile (And.intro pre.hsub (And.intro pre.hmask
    (And.intro pre.hdI pre.hdJ)))
  push_cast at hnumbers
  have hpos₁ : (0 : ℤ) ≤ bI * a.nB := by positivity
  have hpos₂ : (0 : ℤ) ≤ gI * a.K₀ := by positivity
  have hpos₃ : (0 : ℤ) ≤ (gI * a.K₀ + gJ) * a.L := by positivity
  have hpos₄ : (0 : ℤ) ≤ In * a.Lo := by positivity
  have hpos₅ : (0 : ℤ) ≤ Jn * a.Lo := by positivity
  have haddrI : ((a.band : ℤ) + a.N + In).toNat = a.band + a.N + In := by omega
  have haddrJ : ((a.band : ℤ) + a.N + Jn).toNat = a.band + a.N + Jn := by omega
  unfold prepBlock
  -- pi := mem[awi + i]; pj := mem[awj + i]
  light_set In using pre.vI
  light_set Jn using pre.vJ
  -- tile := mem[band + pi] * nb + mem[band + pj]
  light_set (bI * a.nB + bJ : ℕ) using pre.vbI, pre.vbJ
  -- am := mask + (mem[band + n + pi] * k0 + mem[band + n + pj]) * L
  light_set (a.mask + (gI * a.K₀ + gJ) * a.L : ℕ) using haddrI, haddrJ, pre.vgI, pre.vgJ
  -- ai := dig3 + pi * lo; aj := dig3 + pj * lo
  light_set (a.dig3 + In * a.Lo : ℕ)
  light_set (a.dig3 + Jn * a.Lo : ℕ)
  -- acc := 0; lev := 0
  light_set 0
  light_set 0
  rfl

/-- **The block after the walk.** -/
theorem finishBlock_ends (std : Std lim) (hcode : a.tid + a.w + i < lim.space)
    (hrow : row + a.L ≤ lim.space) (x₁ x₂ x₃ x₄ x₅ acc x₇ dig tile : ℤ) :
    Ends lim P d finishBlock (wstate a i x₁ x₂ x₃ x₄ x₅ acc x₇ row dig tile μ) 20
      (· = wstate a (i + 1) x₁ x₂ x₃ x₄ x₅ acc x₇ (row + a.L) dig tile
        (Function.update (Function.update μ (a.tid + i) tile) (a.tid + a.w + i) acc)) := by
  have hw := std.space_le
  have h100 := std.const_le
  unfold finishBlock
  -- mem[tid + i] := tile
  light_store (a.tid + i) tile
  -- mem[tid + w + i] := acc
  light_store (a.tid + a.w + i) acc
  -- i := i + 1; row := row + L
  light_set (i + 1 : ℕ)
  light_set (row + a.L : ℕ)
  rfl

/-! ## One position -/

/-- The arguments of wanted. -/
abbrev wargs (p : Par) (w aWI aWJ band dig3 mask tid : ℕ) : Args :=
  ⟨w, p.L, p.Lo, p.N, p.K0, p.nB, aWI, aWJ, band, dig3, mask, tid⟩

/-- The number, among the K₀² subsets of the table, of the subset of the position (I, J). -/
def subsetNo (p : Par) (I J : ℕ) : ℕ := Spec.maskNo p.L p.m I J

/-- What wanted leaves for the position number i. -/
def Row (p : Par) (w tid : ℕ) (I J : ℕ → ℕ) (μ : ℕ → ℤ) (i : ℕ) : Prop :=
  μ (tid + i) = (I i / (p.K0 * p.N0) * p.nB + J i / (p.K0 * p.N0) : ℕ) ∧
  μ (tid + w + i) = (Spec.outCodeOfPos p.L p.m (I i) (J i) : ℕ) ∧
  SegN μ (tid + 2 * w + i * p.L) (Spec.outDigitsOfPos p.L p.m (I i) (J i))

/-- The first i positions are done, and only the output has changed. -/
structure WantedMem (p : Par) (w tid : ℕ) (I J : ℕ → ℕ) (μ μ' : ℕ → ℤ) (i : ℕ) : Prop where
  done : ∀ i' < i, Row p w tid I J μ' i'
  rest : SameOutside μ μ' tid (2 * w + w * p.L)

section Position

variable {p : Par} {w aWI aWJ band dig3 mask tid : ℕ} {I J : ℕ → ℕ}
  (pre : WantedPre lim p w aWI aWJ band dig3 mask tid I J μ)
  (mem : WantedMem p w tid I J μ μ' i) (hi : i < w)
include pre

/-- The subset of a position is one of the K₀² subsets of the table. -/
theorem WantedPre.subsetNo_lt (In Jn : ℕ) : subsetNo p In Jn < p.K0 * p.K0 :=
  Nat.mul_add_lt_mul (Nat.mod_lt _ (K0_pos pre.hmL)) (Nat.mod_lt _ (K0_pos pre.hmL))

omit pre in
/-- K₀² is at most 10^(L+1), which fits in a word by the hypothesis of wanted. -/
theorem K0_mul_K0_le (p : Par) : p.K0 * p.K0 ≤ 10 ^ (p.L + 1) :=
  calc p.K0 * p.K0 ≤ p.L.choose p.m := Nat.sqrt_le _
    _ ≤ 2 ^ p.L := Nat.choose_le_two_pow _ _
    _ ≤ 10 ^ p.L := Nat.pow_le_pow_left (by norm_num) _
    _ ≤ 10 ^ (p.L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

include hi

/-- The order of the regions of the memory, as far as the position number i is concerned. -/
theorem WantedPre.sizes :
    tid + (2 * w + w * p.L) ≤ lim.space ∧ aWI + w ≤ tid ∧ aWJ + w ≤ tid ∧ band + 2 * p.N ≤ tid ∧
      dig3 + p.N * p.Lo ≤ tid ∧ mask + p.K0 * p.K0 * p.L ≤ tid ∧ I i < p.N ∧ J i < p.N ∧
      i * p.L + p.L ≤ w * p.L ∧ I i * p.Lo + p.Lo ≤ p.N * p.Lo ∧ J i * p.Lo + p.Lo ≤ p.N * p.Lo ∧
      subsetNo p (I i) (J i) * p.L + p.L ≤ p.K0 * p.K0 * p.L :=
  ⟨pre.room, pre.hWI, pre.hWJ, pre.tab.band_le, pre.tab.dig3_le, pre.tab.mask_le, (pre.hI i hi).2,
    (pre.hJ i hi).2, Nat.mul_add_le_mul hi le_rfl, Nat.mul_add_le_mul (pre.hI i hi).2 le_rfl,
    Nat.mul_add_le_mul (pre.hJ i hi).2 le_rfl, Nat.mul_add_le_mul (pre.subsetNo_lt _ _) le_rfl⟩

include mem

/-- The block before the walk finds what it assumes. -/
theorem WantedPre.prep :
    PrepPre lim μ' (wargs p w aWI aWJ band dig3 mask tid) i (I i) (J i) (I i / (p.K0 * p.N0))
      (J i / (p.K0 * p.N0)) (I i / p.N0 % p.K0) (J i / p.N0 % p.K0) := by
  have hsizes := pre.sizes hi
  have hread : ∀ c, c < tid → μ' c = μ c := fun c hc => mem.rest c (Or.inl hc)
  have hsub := pre.subsetNo_lt (I i) (J i)
  have hKK := K0_mul_K0_le p
  have htile : I i / (p.K0 * p.N0) * p.nB + J i / (p.K0 * p.N0) < p.nB * p.nB :=
    Nat.mul_add_lt_mul (bandOf_lt_numBands pre.hmL p.N _ (pre.hI i hi).2)
      (bandOf_lt_numBands pre.hmL p.N _ (pre.hJ i hi).2)
  have hsquare : p.nB * p.nB ≤ (p.nB + 1) * (p.nB + 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [subsetNo, Spec.maskNo, show N0 p.L p.m = p.N0 from rfl, show K0 p.L p.m = p.K0 from rfl]
    at hsub hsizes
  exact
    { vI := (hread _ (by dsimp only; omega)).trans (pre.hI i hi).1
      vJ := (hread _ (by dsimp only; omega)).trans (pre.hJ i hi).1
      vbI := by rw [hread _ (by dsimp only; omega)]; exact pre.tab.hband _ (pre.hI i hi).2
      vbJ := by rw [hread _ (by dsimp only; omega)]; exact pre.tab.hband _ (pre.hJ i hi).2
      vgI := by rw [hread _ (by dsimp only; omega)]; exact pre.tab.hblock _ (pre.hI i hi).2
      vgJ := by rw [hread _ (by dsimp only; omega)]; exact pre.tab.hblock _ (pre.hJ i hi).2
      hWI := by dsimp only; omega
      hWJ := by dsimp only; omega
      hbI := by dsimp only; omega
      hbJ := by dsimp only; omega
      htile := le_trans (by exact_mod_cast (htile.le.trans hsquare)) pre.hnB
      hsub := le_trans (by exact_mod_cast (hsub.le.trans hKK)) pre.hpow
      hmask := by exact_mod_cast (by omega :
        mask + (I i / p.N0 % p.K0 * p.K0 + J i / p.N0 % p.K0) * p.L ≤ lim.space)
      hdI := by exact_mod_cast (by omega : dig3 + I i * p.Lo ≤ lim.space)
      hdJ := by exact_mod_cast (by omega : dig3 + J i * p.Lo ≤ lim.space) }

/-- The walk finds what it assumes. -/
theorem WantedPre.level :
    LevelPre lim μ' p.m (Spec.unrank p.L p.m (subsetNo p (I i) (J i)))
      (ThreeSumApsp.digitList 3 p.Lo (I i % p.N0)) (ThreeSumApsp.digitList 3 p.Lo (J i % p.N0)) p.L
          p.Lo
      (mask + subsetNo p (I i) (J i) * p.L) (dig3 + I i * p.Lo) (dig3 + J i * p.Lo)
      (tid + 2 * w + i * p.L) := by
  have hsizes := pre.sizes hi
  have hread : ∀ c, c < tid → μ' c = μ c := fun c hc => mem.rest c (Or.inl hc)
  have hsub := pre.subsetNo_lt (I i) (J i)
  have hlen := Spec.length_unrank p.L p.m (subsetNo p (I i) (J i))
  exact
    { len := hlen
      cntIn := Spec.count_unrank (hsub.trans_le (Nat.sqrt_le _))
      cnt := Spec.count_false_unrank (hsub.trans_le (Nat.sqrt_le _))
      hmk := fun l hl => by
        rw [hread _ (by omega), pre.tab.hmask _ hsub l (by simpa [hlen] using hl),
          List.getElem_map, List.getD_eq_getElem _ _ (by rw [hlen]; exact hl)]
      segI := (pre.tab.hdig3 _ (pre.hI i hi).2).of_sameOutside mem.rest
        (Or.inl (by rw [ThreeSumApsp.length_digitList]; omega))
      segJ := (pre.tab.hdig3 _ (pre.hJ i hi).2).of_sameOutside mem.rest
        (Or.inl (by rw [ThreeSumApsp.length_digitList]; omega))
      lenI := ThreeSumApsp.length_digitList ..
      lenJ := ThreeSumApsp.length_digitList ..
      ltI := fun _ => ThreeSumApsp.lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => ThreeSumApsp.lt_of_mem_digitList (by norm_num)
      am_le := by omega
      aI_le := by omega
      aJ_le := by omega
      row_le := by omega
      pow_le := pre.hpow }

/-- After the walk and the two stores the position number i is done. -/
theorem WantedMem.next {μ₂ : ℕ → ℤ}
    (lm : LevelMem μ' μ₂ p.m (Spec.unrank p.L p.m (subsetNo p (I i) (J i)))
      (ThreeSumApsp.digitList 3 p.Lo (I i % p.N0)) (ThreeSumApsp.digitList 3 p.Lo (J i % p.N0)) p.L
      (tid + 2 * w + i * p.L) p.L) :
    WantedMem p w tid I J μ
      (Function.update (Function.update μ₂ (tid + i)
          ((I i / (p.K0 * p.N0) * p.nB + J i / (p.K0 * p.N0) : ℕ) : ℤ)) (tid + w + i)
        (accAt p.m (Spec.unrank p.L p.m (subsetNo p (I i) (J i)))
          (ThreeSumApsp.digitList 3 p.Lo (I i % p.N0)) (ThreeSumApsp.digitList 3 p.Lo (J i % p.N0))
              p.L : ℤ))
      (i + 1) := by
  have hsizes := pre.sizes hi
  -- After all levels the digits are those of the output string of the position.
  have hall : (Spec.outDigitsOfPos p.L p.m (I i) (J i)).take p.L
      = Spec.outDigitsOfPos p.L p.m (I i) (J i) :=
    List.take_of_length_le (Spec.length_outDigitsOfPos ..).le
  have hdone : SegN μ₂ (tid + 2 * w + i * p.L)
      ((Spec.outDigitsOfPos p.L p.m (I i) (J i)).take p.L) := lm.done
  rw [hall] at hdone
  -- Only two cells and the row of digits of this position have changed since the round began.
  have hsame : ∀ (x y : ℤ) (c : ℕ), c ≠ tid + i → c ≠ tid + w + i →
      (c < tid + 2 * w + i * p.L ∨ tid + 2 * w + i * p.L + p.L ≤ c) →
      Function.update (Function.update μ₂ (tid + i) x) (tid + w + i) y c = μ' c :=
    fun x y c h₁ h₂ h₃ => by
      rw [Function.update_of_ne h₂, Function.update_of_ne h₁]
      exact lm.rest c h₃
  refine ⟨fun i' hi' => ?_, fun c hc => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · obtain ⟨htile, hcode, hdigits⟩ := mem.done i' hlt
      have hrows : i' * p.L + p.L ≤ i * p.L := Nat.mul_add_le_mul hlt le_rfl
      refine ⟨?_, ?_, fun l hl => ?_⟩
      · rw [hsame _ _ _ (by omega) (by omega) (by omega)]
        exact htile
      · rw [hsame _ _ _ (by omega) (by omega) (by omega)]
        exact hcode
      · have hlL : l < p.L := by simpa using hl
        rw [hsame _ _ _ (by omega) (by omega) (by omega)]
        exact hdigits l hl
    · refine ⟨?_, ?_, fun l hl => ?_⟩
      · rw [Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_self, Spec.outCodeOfPos, ← hall]
        rfl
      · have hlL : l < p.L := by simpa using hl
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hdone l hl
  · rw [hsame _ _ c (by omega) (by omega) (by omega)]
    exact mem.rest c hc

end Position

/-- The invariant of the loop over the positions, before the position number i. -/
def WantedInv (p : Par) (w aWI aWJ band dig3 mask tid : ℕ) (I J : ℕ → ℕ) (μ : ℕ → ℤ) (i : ℕ)
    (σ : State) : Prop :=
  ∃ (x₁ x₂ x₃ x₄ x₅ x₆ x₇ dig x₈ : ℤ) (μ' : ℕ → ℤ),
    σ = wstate (wargs p w aWI aWJ band dig3 mask tid) i x₁ x₂ x₃ x₄ x₅ x₆ x₇
      (tid + 2 * w + i * p.L) dig x₈ μ' ∧
    WantedMem p w tid I J μ μ' i

variable {p : Par} {w aWI aWJ band dig3 mask tid : ℕ} {I J : ℕ → ℕ}

/-- **One position.** -/
theorem wantedRound_ends (std : Std lim)
    (pre : WantedPre lim p w aWI aWJ band dig3 mask tid I J μ) (hi : i < w) {σ : State}
    (hσ : WantedInv p w aWI aWJ band dig3 mask tid I J μ i σ) :
    Ends lim P d (prepBlock ;; levelLoop ;; finishBlock) σ (42 * p.L + 82)
      (WantedInv p w aWI aWJ band dig3 mask tid I J μ (i + 1)) := by
  obtain ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇, dig, x₈, μ', rfl, mem⟩ := hσ
  have hsizes := pre.sizes hi
  -- the position, its tile and the three addresses
  light_piece (prepBlock_ends std (pre.prep mem hi) x₁ x₂ x₃ x₄ x₅ x₆ x₇ dig x₈) with _ rfl
  -- the walk along the mask
  light_piece (levelLoop_ends std (pre.level mem hi) dig) with _ ⟨dig', μ₂, rfl, lm⟩
  -- the tile and the code are stored
  light_piece (finishBlock_ends std (by dsimp only; omega) (by dsimp only; omega) _ _ _ _ _ _ _ _
    _) with _ rfl
  exact ⟨_, _, _, _, _, _, _, _, _, _, by rw [Nat.succ_mul i p.L, ← Nat.add_assoc],
    mem.next pre hi lm⟩

/-- **wanted** writes tile numbers, codes and digits, changes nothing else, and takes at most
tWanted w L steps. -/
theorem wantedBody_ends (std : Std lim)
    (pre : WantedPre lim p w aWI aWJ band dig3 mask tid I J μ) :
    Ends lim P d wantedBody
      ⟨frame [w, p.L, p.Lo, p.N, p.K0, p.nB, aWI, aWJ, band, dig3, mask, tid], μ⟩ (tWanted w p.L)
      fun σ' => WantedMem p w tid I J μ σ'.mem w := by
  have hw := std.space_le
  have h100 := std.const_le
  have hroom := pre.room
  unfold wantedBody tWanted
  -- i := 0; row := tid + w + w
  light_set (0 : ℕ)
  light_set (tid + 2 * w + 0 * p.L : ℕ)
  -- while i < w
  refine Ends.whileConst (WantedInv p w aWI aWJ band dig3 mask tid I J μ) w (42 * p.L + 82) ?start
    ?round ?done (by simp; exact Nat.mul_le_mul_left _ (by omega))
  case start =>
    exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, μ, by rw [wstate, ← frame_append_zeros _ 2]; rfl,
      fun _ h => absurd h (by omega), .refl⟩
  case round =>
    intro i σ hi hσ
    obtain ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇, dig, x₈, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using hi, wantedRound_ends std pre hi hσ⟩
  case done =>
    rintro _ ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇, dig, x₈, μ', rfl, mem⟩
    exact ⟨⟨trivial, trivial⟩, by simp, mem⟩

end Light.Sec2.Wanted

namespace Light.Sec2

open ThreeSumApsp Wanted

variable {lim : Limits} {P : Program}

/-- **wanted**: in a program that has Wanted.wantedBody as procedure number pWanted, a call writes
the tile, the code and the digits of the code of each wanted position, changes no other cell, and
takes at most 86 (w + 1) (L + 1) steps. -/
theorem wanted_entry (std : Std lim) (hP : P[pWanted]? = some wantedBody) {c : ℕ} (hc : 86 ≤ c) :
    WantedSpec lim P c := by
  intro p w aWI aWJ band dig3 mask tid μ I J pre d _
  refine .mono_const (.of_body hP ((wantedBody_ends std pre).mono ?_ ?_)) hc
  · have hleft : w * (42 * p.L + 86) = 42 * (w * p.L) + 86 * w := by ring
    have hright : 86 * ((w + 1) * (p.L + 1)) = 86 * (w * p.L) + 86 * w + 86 * p.L + 86 := by ring
    unfold tWanted
    omega
  · rintro σ' ⟨hrows, hrest⟩
    refine ⟨fun i hi => ?_, hrest⟩
    obtain ⟨htile, hcode, hdigits⟩ := hrows i hi
    exact ⟨htile, hcode, (Spec.digitList_outCodeOfPos ..).symm ▸ hdigits⟩

end Light.Sec2
