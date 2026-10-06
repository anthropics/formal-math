/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The tries of all tiles

Proof of Theorem 30, "Preprocessing": "Finally, we compute the values of all the boxes of each of
the at most 4N²/M tiles". The routine `tile` builds the trie of a tile, and this routine calls it
for every tile. The tiles are taken in row-major order. Three pointers move along: the address of
the encoding of the row band, that of the column band, and the cell for the root of the tile. The
text has three parts, one inside the other: one tile (`allTilesStep`), one row of tiles
(`allTilesRow`), all rows (`allTilesBody`). The invariant `AllTiles.Inv` says what the memory holds
before the tile (β, β'); there is one lemma for each part.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace AllTiles

/-- The local variables of `allTiles`: the arguments aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L,
mt; the row band β, the column band β', the cell for the root of the tile, the address of the
encoding of the row band, that of the column band, and a local for a result that is not used. -/
abbrev EncA : ℕ := 0
@[inherit_doc EncA] abbrev EncB : ℕ := 1
@[inherit_doc EncA] abbrev Bands : ℕ := 2
@[inherit_doc EncA] abbrev Leaves : ℕ := 3
@[inherit_doc EncA] abbrev RootTab : ℕ := 4
@[inherit_doc EncA] abbrev Tries : ℕ := 5
@[inherit_doc EncA] abbrev Free : ℕ := 6
@[inherit_doc EncA] abbrev Cur : ℕ := 7
@[inherit_doc EncA] abbrev Box : ℕ := 8
@[inherit_doc EncA] abbrev Levels : ℕ := 9
@[inherit_doc EncA] abbrev Last : ℕ := 10
@[inherit_doc EncA] abbrev RowBand : ℕ := 11
@[inherit_doc EncA] abbrev ColBand : ℕ := 12
@[inherit_doc EncA] abbrev RootPtr : ℕ := 13
@[inherit_doc EncA] abbrev RowEnc : ℕ := 14
@[inherit_doc EncA] abbrev ColEnc : ℕ := 15
@[inherit_doc EncA] abbrev Void : ℕ := 16

end AllTiles

open AllTiles in
/-- One tile, and on to the next column band. -/
def allTilesStep : Stmt :=
  .call Proc.tile [v RowEnc, v ColEnc, v RootPtr, v Tries, v Free, v Cur, v Box, v Levels, v Last]
    Void ;;
  .set RootPtr (v RootPtr +' k 1) ;;
  .set ColEnc (v ColEnc +' v Leaves) ;;
  .set ColBand (v ColBand +' k 1)

open AllTiles in
/-- One row of tiles, and on to the first tile of the next row band. -/
def allTilesRow : Stmt :=
  .while (v ColBand <' v Bands) allTilesStep ;;
  .set RowEnc (v RowEnc +' v Leaves) ;;
  .set RowBand (v RowBand +' k 1) ;;
  .set ColBand (k 0) ;;
  .set ColEnc (v EncB)

open AllTiles in
/-- allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt). -/
def allTilesBody : Stmt :=
  .set RowBand (k 0) ;;
  .set ColBand (k 0) ;;
  .set RootPtr (v RootTab) ;;
  .set RowEnc (v EncA) ;;
  .set ColEnc (v EncB) ;;
  .set Void (k 0) ;;
  .while (v RowBand <' v Bands) allTilesRow

namespace AllTiles

/-! ## The invariant and one tile -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The tries and the roots of the tiles before the tile (β, β'). -/
def triesBefore (x : AllTilesArgs) (β β' : ℕ) : TrieStore :=
  allTries x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')

/-- What the memory μ' holds before the tile (β, β'): the tries and the roots of the tiles before
it; nothing below cur or behind the trie area has changed since μ. -/
structure Mem (μ μ' : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp (triesBefore x β β').cells
  roots : SegN μ' x.aR (triesBefore x β β').roots
  same : SameOn x.Kept μ μ'

/-- The state before the tile (β, β'): the three pointers stand at this tile, and the memory is as
Mem says. -/
def Inv (μ : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), β, β', (x.aR + (β * x.nB + β') : ℕ), (x.aENCA + β * 10 ^ x.L : ℕ),
      (x.aENCB + β' * 10 ^ x.L : ℕ), void], μ'⟩ ∧
    Mem μ μ' x β β'

/-- The arguments of the call of `tile` for the tile (β, β'), and the data behind them. -/
def tileArgs (x : AllTilesArgs) (β β' : ℕ) : TileArgs where
  L := x.L
  m := x.m
  t := x.t
  encA := x.encA β
  encB := x.encB β'
  aA := x.aENCA + β * 10 ^ x.L
  aB := x.aENCB + β' * 10 ^ x.L
  tr := x.tr
  cap := x.cap
  fp := x.fp
  cur := x.cur
  box := x.box
  aR := x.aR
  s := triesBefore x β β'
  old := storedAll x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  lo := 1

/-- The surroundings of the tile (β, β'). -/
private theorem tileCtx (C : AllTilesPre lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB) :
    TileCtx lim x.L x.m x.t (x.encA β) (x.encB β') (x.aENCA + β * 10 ^ x.L)
      (x.aENCB + β' * 10 ^ x.L) x.tr x.cap x.fp x.cur x.box := by
  have horder := C.order
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  obtain ⟨A, B, hA, hB, hAB⟩ := C.value_le
  generalize β * 10 ^ x.L = a at *
  generalize β' * 10 ^ x.L = b at *
  generalize x.nB * 10 ^ x.L = z at *
  generalize x.nB * x.nB = q at *
  exact
    { std := C.std, ht := C.t_le, hmL := C.m_le, value_le := ⟨A, B, hA β, hB β', hAB⟩
      pow_le := C.pow_le, layout := by light_order }

/-- Each tile before (β, β') has one root. -/
private theorem length_roots_triesBefore (x : AllTilesArgs) (β β' : ℕ) :
    (triesBefore x β β').roots.length = β * x.nB + β' := by
  rw [triesBefore, length_roots_allTries, length_tilesBefore]

/-- Before the tile (β, β') the memory holds what tile assumes. -/
private theorem tileArgs_pre (C : AllTilesPre lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB)
    {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') : TilePre lim μ' (tileArgs x β β') := by
  light_facts C
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hlenR := length_roots_triesBefore x β β'
  have hlenT := length_allTries_le x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  rw [length_tilesBefore] at hlenT
  have hroom := Nat.mul_add_le_mul hi (le_refl (11 * (1 + x.L * (boxes x.L x.m x.t).card)))
  have hA : Seg μ' (x.aENCA + β * 10 ^ x.L) (arrT (x.encA β)) :=
    (C.segA β hβ).keep (by light_keep [M.same, length_arrT (x.encA β)])
  have hB : Seg μ' (x.aENCB + β' * 10 ^ x.L) (arrT (x.encB β')) :=
    (C.segB β' hβ').keep (by light_keep [M.same, length_arrT (x.encB β')])
  have hlenT' : (triesBefore x β β').cells.length
      ≤ 1 + (β * x.nB + β') * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) := hlenT
  exact
    { ctx := tileCtx C hβ hβ'
      rep := allTries_rep x.L x.m x.t _
      trie := M.trie
      roots := M.roots
      segA := hA
      segB := hB
      room := by simp only [tileArgs]; omega
      rootsPlace := by simp only [tileArgs, TileArgs.cells]; omega }

/-- The tries after the tile (β, β'). -/
private theorem tries_tileArgs (x : AllTilesArgs) (β β' : ℕ) :
    (tileArgs x β β').tries = triesBefore x β (β' + 1) := by
  rw [triesBefore, tilesBefore_succ, allTries_snoc]
  rfl

/-- The call of `tile` for the tile (β, β') leads from the memory before this tile to the memory
before the next one. -/
private theorem tile_meets (hTile : TileSpec lim P) (C : AllTilesPre lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 3 ≤ lim.depth) {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') :
    Meets lim P Proc.tile d [(x.aENCA + β * 10 ^ x.L : ℕ), (x.aENCB + β' * 10 ^ x.L : ℕ),
      (x.aR + (β * x.nB + β') : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ'
      (tTile x.L x.m x.t) fun _ μ'' => Mem μ μ'' x β (β' + 1) := by
  have horder := C.order
  have hlenR := length_roots_triesBefore x β β'
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hmeets := hTile _ μ' (tileArgs_pre C hβ hβ' M) _ hd
  rw [← hlenR]
  refine hmeets.mono le_rfl fun _ μ'' ⟨htrie, hroots, same⟩ =>
    ⟨tries_tileArgs x β β' ▸ htrie, tries_tileArgs x β β' ▸ hroots,
      M.same.then same fun c hc => ⟨hc, ?_⟩⟩
  -- a cell below cur or behind the trie area is none of those that tile may change
  have hc' : c < x.cur ∨ x.tr + x.cap ≤ c := hc
  simp only [TileArgs.Kept, tileArgs, Outside]
  omega

/-- One tile: the call, and the pointers move on. -/
private theorem step_spec (hTile : TileSpec lim P) (C : AllTilesPre lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 4 ≤ lim.depth) (h : Inv μ x β β' σ) :
    Ends lim P d allTilesStep σ (tTile x.L x.m x.t + 23) (Inv μ x β (β' + 1)) := by
  obtain ⟨void, μ₁, rfl, M⟩ := h
  light_facts C C.std
  -- tile(rowEnc, colEnc, rootPtr, …)
  light_call (tile_meets hTile C hβ hβ' (by omega) M) with void' μ₂ M₂
  -- rootPtr := rootPtr + 1; colEnc := colEnc + leaves; colBand := colBand + 1
  have hptr : x.aR + (β * x.nB + (β' + 1)) = x.aR + (β * x.nB + β') + 1 := by ring
  have hcol : x.aENCB + (β' + 1) * 10 ^ x.L = x.aENCB + β' * 10 ^ x.L + 10 ^ x.L := by ring
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hcolS := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hbands : x.nB ≤ x.nB * 10 ^ x.L := Nat.le_mul_of_pos_right _ (by positivity)
  unfold Inv
  rw [hptr, hcol]
  -- names for the products
  generalize β * x.nB + β' = ptr at *
  generalize x.aENCA + β * 10 ^ x.L = row at *
  generalize β' * 10 ^ x.L = off at *
  generalize x.nB * 10 ^ x.L = all at *
  generalize 10 ^ x.L = leaves at *
  light_set (x.aR + ptr + 1 : ℕ)
  light_set (x.aENCB + off + leaves : ℕ)
  light_set (β' + 1 : ℕ)
  exact ⟨void', μ₂, rfl, M₂⟩

/-! ## One row, and all rows -/

/-- One row of tiles. -/
private theorem row_spec (hTile : TileSpec lim P) (C : AllTilesPre lim μ x) (hβ : β < x.nB)
    (hd : d + 4 ≤ lim.depth) (h : Inv μ x β 0 σ) :
    Ends lim P d allTilesRow σ (x.nB * (tTile x.L x.m x.t + 27) + 16) (Inv μ x (β + 1) 0) := by
  light_facts C C.std
  -- while β' < nB: one tile
  refine Ends.next _ (Ends.whileConst (Inv μ x β) x.nB (tTile x.L x.m x.t + 23) h ?round ?done
    le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro β' σ hβ' hI
    have hstep := step_spec hTile C hβ hβ' hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by simp, by simpa using hβ', hstep⟩
  case done =>
    rintro _ ⟨void, μ', rfl, M⟩
    refine ⟨by simp, by simp, ?_⟩
    -- rowEnc := rowEnc + leaves; rowBand := rowBand + 1; colBand := 0; colEnc := encB
    have hptr : x.aR + ((β + 1) * x.nB + 0) = x.aR + (β * x.nB + x.nB) := by ring
    have hrow : x.aENCA + (β + 1) * 10 ^ x.L = x.aENCA + β * 10 ^ x.L + 10 ^ x.L := by ring
    have hcol : x.aENCB + 0 * 10 ^ x.L = x.aENCB := by ring
    have hrowS := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
    have hbands : x.nB ≤ x.nB * 10 ^ x.L := Nat.le_mul_of_pos_right _ (by positivity)
    have hbefore : triesBefore x β x.nB = triesBefore x (β + 1) 0 := by
      rw [triesBefore, tilesBefore_row, triesBefore]
    have M' : Mem μ μ' x (β + 1) 0 := ⟨hbefore ▸ M.trie, hbefore ▸ M.roots, M.same⟩
    unfold Inv
    rw [hptr, hrow, hcol]
    -- names for the products
    generalize x.aR + (β * x.nB + x.nB) = ptr at *
    generalize β * 10 ^ x.L = off at *
    generalize x.nB * 10 ^ x.L = all at *
    generalize 10 ^ x.L = leaves at *
    light_set (x.aENCA + off + leaves : ℕ)
    light_set (β + 1 : ℕ)
    light_set (0 : ℕ)
    light_set (x.aENCB : ℕ)
    exact ⟨void, μ', rfl, M'⟩

/-- The time of all rows. -/
private theorem time_le (nB T : ℕ) : 12 + (nB * (4 + (nB * (T + 27) + 16)) + 4)
    ≤ nB * (nB * (T + 80) + 40) + 30 := by
  have hrow : nB * (T + 27) ≤ nB * (T + 80) := Nat.mul_le_mul_left _ (by omega)
  have hall : nB * (4 + (nB * (T + 27) + 16)) ≤ nB * (nB * (T + 80) + 40) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end AllTiles

open AllTiles in
/-- **`allTiles`** meets its specification. -/
theorem allTiles_spec {lim : Limits} {P : Program} (hP : P[Proc.allTiles]? = some allTilesBody)
    (hTile : TileSpec lim P) : AllTilesSpec lim P := by
  intro x μ C
  refine fun d hd => ⟨allTilesBody, hP, ?_⟩
  light_facts C.std
  have htime := time_le x.nB (tTile x.L x.m x.t)
  unfold tAllTiles
  -- β := 0; β' := 0; the three pointers at the first tile
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (x.aR : ℕ)
  light_set (x.aENCA : ℕ)
  light_set (x.aENCB : ℕ)
  light_set 0
  -- while β < nB: one row
  refine Ends.whileConst (fun β => Inv μ x β 0) x.nB (x.nB * (tTile x.L x.m x.t + 27) + 16) ?start
    ?round ?done (by simp; omega)
  case start =>
    refine ⟨0, μ, by simp, ?_, ?_, .refl⟩
    · rw [triesBefore, tilesBefore_zero]
      exact C.trie
    · rw [triesBefore, tilesBefore_zero]
      simp [allTries, SegN, Seg]
  case round =>
    rintro β σ hβ hI
    have hrow := row_spec hTile C hβ hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by simp, by simpa using hβ, hrow⟩
  case done =>
    rintro _ ⟨void, μ', rfl, M⟩
    have hall : triesBefore x x.nB 0 = x.tries := by
      rw [triesBefore, tilesBefore_all, AllTilesArgs.tries]
    exact ⟨by simp, by simp, hall ▸ M.trie, hall ▸ M.roots, M.same⟩

end Light.Sec4
