/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The trie of one tile

Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile". Its proof: "We compute the values of the boxes in increasing
order of their number of stars." The routine takes a root for the trie of the tile and writes it
into the table of roots (Tile.Mem.newRoot). Then, for e = 0, …, m - t, it puts the boxes with e
stars into the trie (tileRound); for e ≥ 1 their values are sums of values looked up in the trie.
The invariant Tile.Inv says what the memory holds before the boxes with e stars; Tile.round takes it
from e to e + 1, and tile_spec is the root and the loop.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace Tile

/-- The local variables of tile: the arguments aA, aB, ra, tr, fp, cur, box, L, mt; the number e of
stars, the root of the trie of the tile, and a local for a result that is not used. -/
abbrev EncA : ℕ := 0
@[inherit_doc EncA] abbrev EncB : ℕ := 1
@[inherit_doc EncA] abbrev RootCell : ℕ := 2
@[inherit_doc EncA] abbrev Tries : ℕ := 3
@[inherit_doc EncA] abbrev Free : ℕ := 4
@[inherit_doc EncA] abbrev Cur : ℕ := 5
@[inherit_doc EncA] abbrev Box : ℕ := 6
@[inherit_doc EncA] abbrev Levels : ℕ := 7
@[inherit_doc EncA] abbrev Last : ℕ := 8
@[inherit_doc EncA] abbrev Stars : ℕ := 9
@[inherit_doc EncA] abbrev Root : ℕ := 10
@[inherit_doc EncA] abbrev Void : ℕ := 11

end Tile

open Tile in
/-- The boxes with e stars go into the trie; on to the next number of stars. -/
def tileRound : Stmt :=
  .call Proc.fillList [v Stars, v Root, v EncA, v EncB, v Tries, v Free, v Cur, v Box, v Levels,
    v Last] Void ;;
  .set Stars (v Stars +' k 1)

open Tile in
/-- tile(aA, aB, ra, tr, fp, cur, box, L, mt): a root for the trie of the tile, noted in the cell
ra; then the boxes with 0, 1, …, mt stars. The number of stars starts at 0, as all locals that are
not arguments. -/
def tileBody : Stmt :=
  .call Proc.newRoot [v Tries, v Free] Root ;;
  .store (v RootCell) (v Root) ;;
  .while (v Stars ≤' v Last) tileRound

namespace Tile

/-! ## The pure side -/

/-- Behind the root and the boxes with fewer than e stars there is room for the boxes with e
stars. -/
theorem room (a b : List ℤ) (L m t root : ℕ) (T : List ℤ) {e : ℕ} (he : e ≤ m - t) :
    (fillUpTo a b L m t root e (trieNew T)).length + 11 * L * (starBoxes L m t e).length
      ≤ T.length + 11 * (1 + L * (boxes L m t).card) := by
  have hused := length_fillUpTo_le_sum a b L m t root e (trieNew T)
  rw [length_trieNew] at hused
  have hlists := List.sum_map_range_mono (fun e => (starBoxes L m t e).length)
    (show e + 1 ≤ m - t + 1 by omega)
  rw [sum_length_starBoxes, List.range_succ, List.map_append, List.sum_append] at hlists
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hlists
  have hmul := Nat.mul_le_mul_left (11 * L) hlists
  rw [Nat.mul_add] at hmul
  have hsplit : 11 * (1 + L * (boxes L m t).card) = 11 + 11 * L * (boxes L m t).card := by ring
  omega

/-- The time: the sum over the rounds, each with the test of the loop (6 steps). -/
theorem time_le (L m t n : ℕ) :
    ∑ i ∈ Finset.range n, (6 + (tFillList L (starBoxes L m t i).length + 30))
      ≤ ((List.range n).map fun e => tFillList L (starBoxes L m t e).length + 60).sum := by
  rw [List.sum_map_range]
  exact Finset.sum_le_sum fun _ _ => by omega

/-! ## The memory during the loop -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ₁ μ₂ : ℕ → ℤ} {x : TileArgs} {e : ℕ} {σ : State}
  {T T' : List ℤ}

/-- What the memory μ' holds during the loop: the trie array T, the roots, with that of the tile
behind the older ones, and the two encodings; the cells that the routine does not own are as in
μ. -/
structure Mem (μ μ' : ℕ → ℤ) (x : TileArgs) (T : List ℤ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp T
  roots : SegN μ' x.aR (x.s.roots ++ [x.s.cells.length])
  segA : Seg μ' x.aA (arrT x.encA)
  segB : Seg μ' x.aB (arrT x.encB)
  same : SameOn x.Kept μ μ'

/-- After the root of the tile has been taken and written behind the older roots. -/
theorem Mem.newRoot (C : TilePre lim μ x) (hs : SameOutsideTrie μ μ₁ x.tr x.cap x.fp)
    (ht : TrieMem μ₁ x.tr x.cap x.fp T) :
    Mem μ (Function.update μ₁ (x.aR + x.s.roots.length) (x.s.cells.length : ℤ)) x T := by
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  have hlayout := C.ctx.layout
  have hroots := C.rootsPlace
  exact
    { trie := ht.keep
      roots := SegN.snoc C.roots.keep _
      segA := C.segA.keep
      segB := C.segB.keep
      same := by light_keep }

/-- After the boxes with some number of stars have been put into the trie. -/
theorem Mem.fill (C : TilePre lim μ x) (h : Mem μ μ₁ x T)
    (hs : SameOutsideTile μ₁ μ₂ x.L x.tr x.cap x.fp x.cur x.box)
    (ht : TrieMem μ₂ x.tr x.cap x.fp T') : Mem μ μ₂ x T' := by
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  have hlayout := C.ctx.layout
  have hroots := C.rootsPlace
  have hsame := h.same
  exact { trie := ht, roots := h.roots.keep, segA := h.segA.keep, segB := h.segB.keep
          same := by light_keep }

/-! ## The invariant and one round -/

/-- The trie array once the root of the tile has been taken and the boxes with fewer than e stars
are in the trie. -/
def trieAt (x : TileArgs) (e : ℕ) : List ℤ :=
  fillUpTo (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length e (trieNew x.s.cells)

/-- The arguments of the call of fillList for the boxes with e stars. -/
def fillArgs (x : TileArgs) (e : ℕ) : FillListArgs :=
  { x with e := e, tile := x.s.roots.length, roots := x.s.new.root, T := trieAt x e }

/-- The state before the boxes with e stars: the root is in its local and in its cell, and the trie
holds the boxes with fewer stars. -/
def Inv (μ : ℕ → ℤ) (x : TileArgs) (e : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), e, x.s.cells.length, void], μ'⟩ ∧
    Mem μ μ' x (trieAt x e)

/-- One round puts the boxes with e stars into the trie. -/
theorem round (hFill : FillListSpec lim P) (C : TilePre lim μ x) (hd : d + 3 ≤ lim.depth)
    (he : e ≤ x.m - x.t) (h : Inv μ x e σ) :
    Ends lim P d tileRound σ (tFillList x.L (starBoxes x.L x.m x.t e).length + 30)
      (Inv μ x (e + 1)) := by
  obtain ⟨void, μ₁, rfl, hM⟩ := h
  have hlayout := C.ctx.layout
  light_facts C.ctx C.ctx.std
  -- the trie of the tile has the number s.roots.length, and its root is the last one
  have hroot := x.s.root_new
  have hfill := hFill (fillArgs x e) μ₁
    { ctx := C.ctx, stars_le := he, root_ne := hroot.trans_ne C.rep.length_pos.ne'
      rep := fillUpTo_rep (arrT x.encA) (arrT x.encB) x.m x.t x.s C.rep e
      trie := hM.trie, segA := hM.segA, segB := hM.segB
      room := (room (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length x.s.cells he).trans
        C.room }
  simp only [fillArgs, FillListArgs.vals, FillListArgs.root, FillListArgs.boxes, hroot] at hfill
  -- fillList(e, root, …)
  light_call (hfill _ (by omega)) with void' μ₂ ⟨htrie, same⟩
  -- e := e + 1
  light_set (e + 1 : ℕ)
  exact ⟨void', μ₂, rfl, hM.fill C same htrie⟩

end Tile

open Tile in
/-- **tile** meets its specification. -/
theorem tile_spec {lim : Limits} {P : Program} (hP : P[Proc.tile]? = some tileBody)
    (hNew : NewRootSpec lim P) (hFill : FillListSpec lim P) : TileSpec lim P := by
  intro x μ C
  refine fun d hd => ⟨tileBody, hP, ?_⟩
  have hlayout := C.ctx.layout
  light_facts C C.ctx C.ctx.std
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hroom := C.room
  unfold tTile
  -- root := newRoot(tr, fp)
  light_call (hNew x.tr x.cap x.fp x.s.cells μ C.trie (by omega) (by omega) (by omega) _
    (by omega)) with _ μ₁ ⟨rfl, htrie, same⟩
  -- mem[ra] := root
  light_store (x.aR + x.s.roots.length) x.s.cells.length
  -- while e ≤ mt
  refine (Ends.while (Inv μ x) (x.m - x.t + 1)
    (fun e => tFillList x.L (starBoxes x.L x.m x.t e).length + 30)
    ?start ?round ?done).mono ?time fun _ h => h
  case start => exact ⟨0, _, congrArg (State.mk · _) (frame_append_zeros _ 1).symm,
    Mem.newRoot C same htrie⟩
  case round =>
    rintro e σ he hI
    have hround := round hFill C hd (by omega) hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by light_side, by simp; omega, hround⟩
  case done =>
    rintro _ ⟨void, μ', rfl, hM'⟩
    exact ⟨by light_side, by simp, hM'.trie, hM'.roots, hM'.same⟩
  case time =>
    have hsum := time_le x.L x.m x.t (x.m - x.t + 1)
    -- the test of the loop and the jump cost 6 steps
    have htest : ∀ y : ℕ, 1 + (1 + 1 + 1) + 1 + 1 + y = 6 + y := fun y => by omega
    simp only [Cond.cost, Expr.cost, htest]
    light_time

end Light.Sec4
