/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.SliceFacts

/-!
# Theorem 5 as a program: the pruned recursion on every tile

Section 2.4.4: "for each tile T with W_T ≠ ∅, we run Pruned(W_T)".

The wanted positions have been sorted by tile and, within a tile, by code.  The codes of the tile
number t = β nB + β' are the cells START[t], …, START[t+1] - 1 of SC.  runTiles walks over all
tiles; for each tile with START[t] < START[t+1] it calls the pruned recursion on the encodings of
the row band β and of the column band β', and the values land in the same cells of SV.

* The memory.  `TilesInv` says which tiles are done.  What the call for a tile assumes holds
  (`TilesPre.tile`), and the call finishes the tile (`TilesInv.of_call`); a tile without wanted
  positions is finished as it is (`TilesInv.of_empty`).
* The program.  `runTile_ends` treats one tile, `runTilesInner_ends` the tiles of a row band,
  `runBand_ends` a row band, and `runTiles_entry` all of them.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## What the callers may assume

`RunTilesSpec` says what a call of procedure `pRunTiles` does, and in how many steps: a constant c
times a shape that depends on the sizes. -/

/-- The work of the pruned recursion on a tile: nothing if the tile has no wanted position. -/
def tileWork (L : ℕ) (codes : List ℕ) : ℕ := if codes = [] then 0 else Spec.prunedWork L codes

/-- The shape of the running time of runTiles. -/
def tilesShape (nB L : ℕ) (codes : ℕ → List ℕ) : ℕ :=
  nB * nB + nB + 1 + ∑ β ∈ Finset.range nB, ∑ β' ∈ Finset.range nB, tileWork L (codes (β * nB + β'))

/-- The arguments of runTiles, with the data behind them.  EA β and EB β' are the encodings of the
bands, which stand at enca and encb, one behind the other; s t = START[t]; codes t are the codes of
tile t; w is the number of wanted positions; A and B bound the numbers in the encodings. -/
structure TilesArgs : Type where
  (nB L enca encb start sc sv sp p10 : ℕ)
  (w : ℕ) (EA EB : ℕ → List ℤ) (s : ℕ → ℕ) (codes : ℕ → List ℕ) (A B : ℤ)

/-- The values of the arguments of runTiles. -/
abbrev TilesArgs.vals (x : TilesArgs) : List ℤ :=
  [x.nB, x.L, (10 ^ x.L : ℕ), x.enca, x.encb, x.start, x.sc, x.sv, x.sp, x.p10]

/-- What runTiles assumes.  Everything that is read lies below SV; then come the w cells of SV and,
from sp on, the stack of the pruned recursion. -/
structure TilesPre (lim : Limits) (μ : ℕ → ℤ) (x : TilesArgs) : Prop where
  hp10 : Seg μ x.p10 (powList 10 (x.L + 1))
  hea : ∀ β < x.nB, Seg μ (x.enca + β * 10 ^ x.L) (x.EA β)
  heb : ∀ β < x.nB, Seg μ (x.encb + β * 10 ^ x.L) (x.EB β)
  lea : ∀ β < x.nB, (x.EA β).length = 10 ^ x.L
  leb : ∀ β < x.nB, (x.EB β).length = 10 ^ x.L
  hstart : ∀ t ≤ x.nB * x.nB, μ (x.start + t) = x.s t
  mono : ∀ t < x.nB * x.nB, x.s t ≤ x.s (t + 1)
  s_le : x.s (x.nB * x.nB) ≤ x.w
  hcodes : ∀ t < x.nB * x.nB, SegN μ (x.sc + x.s t) (x.codes t)
  lcodes : ∀ t < x.nB * x.nB, (x.codes t).length = x.s (t + 1) - x.s t
  sorted : ∀ t < x.nB * x.nB, (x.codes t).Pairwise (· < ·)
  small : ∀ t < x.nB * x.nB, ∀ c ∈ x.codes t, c < 10 ^ x.L
  boundA : ∀ β < x.nB, AbsLe (x.EA β) x.A
  boundB : ∀ β < x.nB, AbsLe (x.EB β) x.B
  room : 10 ^ x.L * (x.A * x.B) ≤ lim.word
  ten : ((10 ^ (x.L + 1) : ℕ) : ℤ) ≤ lim.word
  p10_le : x.p10 + (x.L + 1) ≤ x.sc := by light_arith
  enca_le : x.enca + x.nB * 10 ^ x.L ≤ x.sc := by light_arith
  encb_le : x.encb + x.nB * 10 ^ x.L ≤ x.sc := by light_arith
  start_le : x.start + (x.nB * x.nB + 1) ≤ x.sc := by light_arith
  sc_le : x.sc + x.w ≤ x.sv := by light_arith
  sv_le : x.sv + x.w ≤ x.sp := by light_arith
  sp_le : x.sp + x.L * (3 * x.w + 11) ≤ lim.space := by light_arith

/-- runTiles(nB, L, T, enca, encb, start, sc, sv, sp, p10), with T = 10^L: for every tile (β, β')
the values of the pruned recursion at the codes of the tile, in the cells of SV that correspond to
the cells of SC with these codes.  Only the w cells of SV and the stack may have changed. -/
def RunTilesSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (x : TilesArgs) (μ : ℕ → ℤ), TilesPre lim μ x →
    ∀ d, d + (x.L + 2) ≤ lim.depth →
    Meets lim P pRunTiles d x.vals μ (c * tilesShape x.nB x.L x.codes) fun _ μ' =>
      (∀ β < x.nB, ∀ β' < x.nB, Seg μ' (x.sv + x.s (β * x.nB + β'))
        (Spec.prunedList (x.EA β) (x.EB β') x.L 0 (x.codes (β * x.nB + β'))))
      ∧ SameOutside2 μ μ' x.sv x.w x.sp (x.L * (3 * x.w + 11))

/-! ## The program -/

namespace TilesLocal

/-- The number nB of bands. -/
abbrev NB : ℕ := 0
/-- The number L of levels. -/
abbrev LL : ℕ := 1
/-- T = 10^L, the length of an encoding. -/
abbrev TT : ℕ := 2
/-- The encoding of the row band β. -/
abbrev PEA : ℕ := 3
/-- The encodings of the column bands. -/
abbrev ENCB : ℕ := 4
/-- The address of START[t]. -/
abbrev PST : ℕ := 5
/-- The codes, sorted. -/
abbrev SC : ℕ := 6
/-- The values. -/
abbrev SV : ℕ := 7
/-- The stack of the pruned recursion. -/
abbrev SP : ℕ := 8
/-- The table of the powers of ten. -/
abbrev P10 : ℕ := 9
/-- The row band β. -/
abbrev CB : ℕ := 10
/-- The column band β'. -/
abbrev CC : ℕ := 11
/-- The encoding of the column band β'. -/
abbrev PEB : ℕ := 12
/-- START[t]. -/
abbrev S0 : ℕ := 13
/-- START[t + 1]. -/
abbrev S1 : ℕ := 14
/-- A result that is not used. -/
abbrev RES : ℕ := 15

end TilesLocal

open TilesLocal

/-- One tile: the pruned recursion is called if the tile has wanted positions; then the column band,
its encoding and the address of START[t] move on. -/
def runTile : Stmt :=
  .set S0 (M (v PST)) ;; .set S1 (M (v PST +' k 1)) ;;
  .ite (v S0 <' v S1)
    (.call pPruned [v LL, v PEA, v PEB, v SC +' v S0, v S1 -' v S0, v SV +' v S0, v SP, v P10] RES)
    .skip ;;
  .set CC (v CC +' k 1) ;; .set PEB (v PEB +' v TT) ;; .set PST (v PST +' k 1)

/-- The tiles of one row band. -/
def runTilesInner : Stmt :=
  .while (v CC <' v NB) runTile

/-- One row band. -/
def runBand : Stmt :=
  .set CC (k 0) ;; .set PEB (v ENCB) ;; runTilesInner ;; .set CB (v CB +' k 1) ;;
  .set PEA (v PEA +' v TT)

/-- runTiles(nB, L, T, enca, encb, start, sc, sv, sp, p10). -/
def runTilesBody : Stmt :=
  .set CB (k 0) ;;
  .while (v CB <' v NB) runBand

/-! ## The memory -/

variable {lim : Limits} {x : TilesArgs} {μ μ' : ℕ → ℤ} {β i : ℕ}

namespace TilesPre

/-- The table START increases. -/
theorem s_mono (pre : TilesPre lim μ x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ x.nB * x.nB) :
    x.s a ≤ x.s b := by
  induction hab with
  | refl => exact le_rfl
  | step h ih => exact (ih (by omega)).trans (pre.mono _ (by omega))

/-- The entries of START are at most w. -/
theorem s_le_w (pre : TilesPre lim μ x) {a : ℕ} (ha : a ≤ x.nB * x.nB) : x.s a ≤ x.w :=
  (pre.s_mono ha le_rfl).trans pre.s_le

/-- What runTiles reads lies below SV. -/
theorem keep (pre : TilesPre lim μ x) (hs : Kept μ μ' x.sv := by light_keep) :
    TilesPre lim μ' x := by
  light_facts pre
  have band : ∀ β < x.nB, β * 10 ^ x.L + 10 ^ x.L ≤ x.nB * 10 ^ x.L := fun β hβ =>
    Nat.mul_add_le_mul hβ le_rfl
  exact
    { pre with
      hp10 := pre.hp10.keep
      hea := fun β hβ => by have := band β hβ; have := pre.lea β hβ; exact (pre.hea β hβ).keep
      heb := fun β hβ => by have := band β hβ; have := pre.leb β hβ; exact (pre.heb β hβ).keep
      hstart := fun t ht => (hs _ (by omega)).trans (pre.hstart t ht)
      hcodes := fun t ht => by
        have := pre.lcodes t ht
        have := pre.s_le_w (a := t + 1) (by omega)
        exact (pre.hcodes t ht).keep }

/-- The list of the values of a tile is as long as the list of its codes. -/
theorem lvals (pre : TilesPre lim μ x) {b b' : ℕ} (hb : b < x.nB) (hb' : b' < x.nB) :
    (Spec.prunedList (x.EA b) (x.EB b') x.L 0 (x.codes (b * x.nB + b'))).length
      = x.s (b * x.nB + b' + 1) - x.s (b * x.nB + b') := by
  rw [length_prunedList (x.EA b) (x.EB b') x.L 0 (pre.sorted _ (Nat.mul_add_lt_mul hb hb'))
    (pre.small _ (Nat.mul_add_lt_mul hb hb')), pre.lcodes _ (Nat.mul_add_lt_mul hb hb')]

/-- The window of a tile that comes before the tile (β, i) ends at or before the window of that
tile. -/
theorem window_le (pre : TilesPre lim μ x) (hβ : β < x.nB) (hi : i < x.nB) {b b' : ℕ}
    (hb' : b' < x.nB) (h : b < β ∨ (b = β ∧ b' < i)) :
    x.s (b * x.nB + b' + 1) ≤ x.s (β * x.nB + i) := by
  have ht := Nat.mul_add_lt_mul hβ hi
  refine pre.s_mono ?_ ht.le
  rcases h with h | ⟨rfl, h⟩
  · have := Nat.mul_add_lt_mul (n := x.nB) h hb'
    omega
  · omega

end TilesPre

/-- The memory when the tiles before (β, i) are done: only SV and the stack have changed, and the
windows of the tiles that are done hold their values. -/
structure TilesInv (x : TilesArgs) (μ : ℕ → ℤ) (β i : ℕ) (μ' : ℕ → ℤ) : Prop where
  frame : SameOutside2 μ μ' x.sv x.w x.sp (x.L * (3 * x.w + 11))
  done : ∀ b < x.nB, ∀ b' < x.nB, (b < β ∨ (b = β ∧ b' < i)) →
    Seg μ' (x.sv + x.s (b * x.nB + b'))
      (Spec.prunedList (x.EA b) (x.EB b') x.L 0 (x.codes (b * x.nB + b')))

/-- What is read has not changed. -/
theorem TilesPre.unchanged (pre : TilesPre lim μ x) (inv : TilesInv x μ β i μ') :
    TilesPre lim μ' x := by
  light_facts pre inv
  exact pre.keep

/-- The arguments of the call of pruned for the tile (β, i). -/
@[simp]
def TilesArgs.tile (x : TilesArgs) (β i : ℕ) : PrunedArgs where
  aEA := x.enca + β * 10 ^ x.L
  aEB := x.encb + i * 10 ^ x.L
  base := 0
  l := x.sc + x.s (β * x.nB + i)
  out := x.sv + x.s (β * x.nB + i)
  sp := x.sp
  p10 := x.p10
  Lmax := x.L
  EA := x.EA β
  EB := x.EB i
  codes := x.codes (β * x.nB + i)
  A := x.A
  B := x.B

/-- The arithmetic of the tile (β, i): its window lies within the w cells, its two encodings within
the encodings of all bands, and its stack within the stack for w codes. -/
structure TileSizes (x : TilesArgs) (β i : ℕ) : Prop where
  tile_lt : β * x.nB + i < x.nB * x.nB
  len : (x.codes (β * x.nB + i)).length = x.s (β * x.nB + i + 1) - x.s (β * x.nB + i)
  mono : x.s (β * x.nB + i) ≤ x.s (β * x.nB + i + 1)
  last : x.s (β * x.nB + i + 1) ≤ x.w
  lenA : (x.EA β).length = 10 ^ x.L
  lenB : (x.EB i).length = 10 ^ x.L
  bandA : β * 10 ^ x.L + 10 ^ x.L ≤ x.nB * 10 ^ x.L
  bandB : i * 10 ^ x.L + 10 ^ x.L ≤ x.nB * 10 ^ x.L
  stack : x.L * (3 * (x.codes (β * x.nB + i)).length + 11) ≤ x.L * (3 * x.w + 11)

/-- The inequalities of the tile (β, i) follow from what runTiles assumes. -/
theorem TilesPre.sizes (pre : TilesPre lim μ x) (hβ : β < x.nB) (hi : i < x.nB) :
    TileSizes x β i := by
  have ht := Nat.mul_add_lt_mul hβ hi
  have hlen := pre.lcodes _ ht
  have hlast := pre.s_le_w (a := β * x.nB + i + 1) (by omega)
  exact ⟨ht, hlen, pre.mono _ ht, hlast, pre.lea β hβ, pre.leb i hi, Nat.mul_add_le_mul hβ le_rfl,
    Nat.mul_add_le_mul hi le_rfl, Nat.mul_le_mul_left _ (by omega)⟩

section Tile

variable (pre : TilesPre lim μ x) (inv : TilesInv x μ β i μ') (hβ : β < x.nB) (hi : i < x.nB)
include pre inv hβ hi

/-- What the call for the tile (β, i) assumes holds. -/
theorem TilesPre.tile : PrunedPre lim μ' x.L (x.tile β i) := by
  have pre' := pre.unchanged inv
  light_facts pre (pre.sizes hβ hi)
  exact
    { powers := pre'.hp10
      encA := pre'.hea β hβ
      encB := pre'.heb i hi
      list := pre'.hcodes _ (Nat.mul_add_lt_mul hβ hi)
      sorted := pre.sorted _ (Nat.mul_add_lt_mul hβ hi)
      lt := pre.small _ (Nat.mul_add_lt_mul hβ hi)
      boundA := pre.boundA β hβ
      boundB := pre.boundB i hi
      word := pre.room
      pow := pre.ten }

/-- After the call the tile (β, i) is done. -/
theorem TilesInv.of_call {μ'' : ℕ → ℤ}
    (hvalues : Seg μ'' (x.sv + x.s (β * x.nB + i))
      (Spec.prunedList (x.EA β) (x.EB i) x.L 0 (x.codes (β * x.nB + i))))
    (hframe : SameOutside2 μ' μ'' (x.sv + x.s (β * x.nB + i)) (x.codes (β * x.nB + i)).length x.sp
      (x.L * (3 * (x.codes (β * x.nB + i)).length + 11))) :
    TilesInv x μ β (i + 1) μ'' := by
  light_facts pre (pre.sizes hβ hi) inv
  refine ⟨by light_keep, fun b hb b' hb' h => ?_⟩
  by_cases hnew : b = β ∧ b' = i
  · obtain ⟨rfl, rfl⟩ := hnew
    exact hvalues
  · have hold : b < β ∨ (b = β ∧ b' < i) := by omega
    have hwindow := pre.window_le hβ hi hb' hold
    have hlen := pre.lvals hb hb'
    exact (inv.done b hb b' hb' hold).keep

/-- A tile without wanted positions is done as it is. -/
theorem TilesInv.of_empty (hempty : x.s (β * x.nB + i + 1) = x.s (β * x.nB + i)) :
    TilesInv x μ β (i + 1) μ' := by
  refine ⟨inv.frame, fun b hb b' hb' h => ?_⟩
  by_cases hnew : b = β ∧ b' = i
  · obtain ⟨rfl, rfl⟩ := hnew
    intro j hj
    rw [pre.lvals hb hb'] at hj
    omega
  · exact inv.done b hb b' hb' (by omega)

end Tile

/-- When the tiles of the row band β are done, the next row band begins. -/
theorem TilesInv.next_band (inv : TilesInv x μ β x.nB μ') : TilesInv x μ (β + 1) 0 μ' :=
  ⟨inv.frame, fun b hb b' hb' _ => inv.done b hb b' hb' (by omega)⟩

/-! ## One tile -/

variable {P : Program} {c e : ℕ}

/-- The state of runTiles: pa, pt and pb are the addresses of the encoding of the row band, of
START[t] and of the encoding of the column band; s0, s1 and res are what the locals S0, S1 and RES
hold. -/
abbrev tilesState (x : TilesArgs) (pa pt β i pb : ℕ) (s0 s1 res : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [x.nB, x.L, (10 ^ x.L : ℕ), pa, x.encb, pt, x.sc, x.sv, x.sp, x.p10, β, i, pb, s0, s1,
    res], μ'⟩

/-- The invariant of the loop over the tiles of the row band β, before the tile (β, i). -/
def TileLoop (x : TilesArgs) (μ : ℕ → ℤ) (β i : ℕ) (σ : State) : Prop :=
  ∃ (s0 s1 res : ℤ) (μ' : ℕ → ℤ),
    σ = tilesState x (x.enca + β * 10 ^ x.L) (x.start + (β * x.nB + i)) β i
      (x.encb + i * 10 ^ x.L) s0 s1 res μ' ∧
    TilesInv x μ β i μ'

/-- The end of a round: the column band, its encoding and the address of START[t] move on. -/
theorem runTileTail_ends (std : Std lim) (pre : TilesPre lim μ x) (hβ : β < x.nB) (hi : i < x.nB)
    (s0 s1 res : ℤ) (inv : TilesInv x μ β (i + 1) μ') :
    Ends lim P e (.set CC (v CC +' k 1) ;; .set PEB (v PEB +' v TT) ;; .set PST (v PST +' k 1))
      (tilesState x (x.enca + β * 10 ^ x.L) (x.start + (β * x.nB + i)) β i
        (x.encb + i * 10 ^ x.L) s0 s1 res μ') 12
      (TileLoop x μ β (i + 1)) := by
  light_facts std pre (pre.sizes hβ hi)
  have hnB : x.nB ≤ x.nB * x.nB := Nat.le_mul_self x.nB
  -- β' := β' + 1
  light_set (i + 1 : ℕ)
  -- peb := peb + T
  refine Ends.setToThen (x.encb + (i + 1) * 10 ^ x.L : ℕ) ?_
    (by rw [Nat.succ_mul]; generalize 10 ^ x.L = T at *; simp [abs_le]; omega)
  -- pst := pst + 1
  light_set (x.start + (β * x.nB + (i + 1)) : ℕ)
  exact ⟨s0, s1, res, μ', rfl, inv⟩

/-- **One tile.** -/
theorem runTile_ends (std : Std lim) (pruned : PrunedSpec lim P c) (he : e + x.L + 2 ≤ lim.depth)
    (pre : TilesPre lim μ x) (hβ : β < x.nB) (hi : i < x.nB) {σ : State}
    (hσ : TileLoop x μ β i σ) :
    Ends lim P e runTile σ (40 + c * tileWork x.L (x.codes (β * x.nB + i)))
      (TileLoop x μ β (i + 1)) := by
  obtain ⟨s0, s1, res, μ', rfl, inv⟩ := hσ
  light_facts std pre (pre.sizes hβ hi)
  have pre' := pre.unchanged inv
  have ht := Nat.mul_add_lt_mul hβ hi
  have hlen := pre.lcodes _ ht
  have hread₀ := pre'.hstart (β * x.nB + i) ht.le
  have hread₁ := pre'.hstart (β * x.nB + i + 1) ht
  have haddr₀ : ((x.start : ℤ) + (β * x.nB + i)).toNat = x.start + (β * x.nB + i) := by omega
  have haddr₁ : ((x.start : ℤ) + (β * x.nB + i) + 1).toNat = x.start + (β * x.nB + i + 1) := by
    omega
  unfold runTile
  -- s0 := mem[pst]; s1 := mem[pst + 1]
  light_set (x.s (β * x.nB + i) : ℕ) using haddr₀, hread₀
  light_set (x.s (β * x.nB + i + 1) : ℕ) using haddr₁, hread₁
  -- if s0 < s1
  refine Ends.iteThen (fun hlt => ?_) (fun hge => ?_)
  · replace hlt : x.s (β * x.nB + i) < x.s (β * x.nB + i + 1) := by simpa using hlt
    have hne : x.codes (β * x.nB + i) ≠ [] := fun h => by simp [h] at hlen; omega
    rw [tileWork, if_neg hne]
    -- res := pruned(L, pea, peb, sc + s0, s1 - s0, sv + s0, sp, p10)
    light_call (pruned x.L (x.tile β i) μ' (pre.tile inv hβ hi) _ (by omega)) using hlen
      with r μ'' ⟨hvalues, hframe⟩
    light_piece (runTileTail_ends std pre hβ hi _ _ r (inv.of_call pre hβ hi hvalues hframe))
  · replace hge : x.s (β * x.nB + i + 1) = x.s (β * x.nB + i) := by
      have : ¬ x.s (β * x.nB + i) < x.s (β * x.nB + i + 1) := by simpa using hge
      omega
    -- skip
    refine Ends.next 0 (Ends.skip ?_)
    light_piece (runTileTail_ends std pre hβ hi _ _ res (inv.of_empty pre hβ hi hge))

/-! ## The two loops -/

/-- The time of the tiles of one row band. -/
def innerTime (c nB L : ℕ) (codes : ℕ → List ℕ) (β : ℕ) : ℕ :=
  ∑ i ∈ Finset.range nB, (4 + (40 + c * tileWork L (codes (β * nB + i)))) + 4

/-- The tiles of one row band. -/
theorem runTilesInner_ends (std : Std lim) (pruned : PrunedSpec lim P c)
    (he : e + x.L + 2 ≤ lim.depth) (pre : TilesPre lim μ x) (hβ : β < x.nB) {σ : State}
    (hσ : TileLoop x μ β 0 σ) :
    Ends lim P e runTilesInner σ (innerTime c x.nB x.L x.codes β) (TileLoop x μ β x.nB) := by
  -- while β' < nB
  refine (Ends.while (TileLoop x μ β) x.nB
    (fun i => 40 + c * tileWork x.L (x.codes (β * x.nB + i))) hσ ?round ?done).mono
    (le_of_eq (by simp only [Cond.cost, Expr.cost, innerTime])) fun _ h => h
  case round =>
    intro i σ hi hσ
    obtain ⟨s0, s1, res, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using hi, runTile_ends std pruned he pre hβ hi hσ⟩
  case done =>
    intro σ hσ
    obtain ⟨s0, s1, res, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simp, hσ⟩

/-- The invariant of the loop over the row bands, before the row band β. -/
def BandLoop (x : TilesArgs) (μ : ℕ → ℤ) (β : ℕ) (σ : State) : Prop :=
  ∃ (i pb : ℕ) (s0 s1 res : ℤ) (μ' : ℕ → ℤ),
    σ = tilesState x (x.enca + β * 10 ^ x.L) (x.start + β * x.nB) β i pb s0 s1 res μ' ∧
    TilesInv x μ β 0 μ'

/-- **One row band.** -/
theorem runBand_ends (std : Std lim) (pruned : PrunedSpec lim P c) (he : e + x.L + 2 ≤ lim.depth)
    (pre : TilesPre lim μ x) (hβ : β < x.nB) {σ : State} (hσ : BandLoop x μ β σ) :
    Ends lim P e runBand σ (12 + innerTime c x.nB x.L x.codes β) (BandLoop x μ (β + 1)) := by
  obtain ⟨i, pb, s0, s1, res, μ', rfl, inv⟩ := hσ
  light_facts std pre
  have hband : β * 10 ^ x.L + 10 ^ x.L ≤ x.nB * 10 ^ x.L := Nat.mul_add_le_mul hβ le_rfl
  have hnB : x.nB ≤ x.nB * x.nB := Nat.le_mul_self x.nB
  unfold runBand
  -- β' := 0; peb := encb
  light_set (0 : ℕ)
  light_set (x.encb + 0 * 10 ^ x.L : ℕ)
  -- the tiles of the row band
  light_piece (runTilesInner_ends std pruned he pre hβ
    ⟨s0, s1, res, μ', rfl, inv⟩) with _ ⟨s0', s1', res', μ'', rfl, inv'⟩
  -- β := β + 1
  light_set (β + 1 : ℕ)
  -- pea := pea + T
  refine Ends.setTo (x.enca + (β + 1) * 10 ^ x.L : ℕ) ?_
    (by rw [Nat.succ_mul]; generalize 10 ^ x.L = T at *; simp [abs_le]; omega)
  exact ⟨x.nB, x.encb + x.nB * 10 ^ x.L, s0', s1', res', μ'', by rw [Nat.succ_mul β x.nB]; rfl,
    inv'.next_band⟩

/-- The time of the loop over the row bands is within the shape. -/
theorem sum_innerTime_le (c nB L : ℕ) (codes : ℕ → List ℕ) :
    2 + (∑ β ∈ Finset.range nB, (4 + (12 + innerTime c nB L codes β)) + 4)
      ≤ (c + 60) * tilesShape nB L codes := by
  simp only [innerTime, tilesShape, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum]
  generalize ∑ β ∈ Finset.range nB, ∑ i ∈ Finset.range nB, tileWork L (codes (β * nB + i)) = S
  have hsplit : (c + 60) * (nB * nB + nB + 1 + S)
      = c * (nB * nB + nB + 1) + c * S + 60 * (nB * nB + nB + 1 + S) := by ring
  have hfour : nB * (nB * 4) = 4 * (nB * nB) := by ring
  have hforty : nB * (nB * 40) = 40 * (nB * nB) := by ring
  have hnonneg := Nat.zero_le (c * (nB * nB + nB + 1))
  omega

/-- **runTiles** does what `RunTilesSpec` says: for every tile the values of the pruned recursion
stand in SV, and only SV and the stack have changed.  The constant of the time is that of the pruned
recursion plus 60. -/
theorem runTiles_entry (std : Std lim) (hP : P[pRunTiles]? = some runTilesBody)
    (pruned : PrunedSpec lim P c) {c' : ℕ} (hc : c + 60 ≤ c') : RunTilesSpec lim P c' := by
  intro x μ pre d hd
  have h100 := std.const_le
  have hT := sum_innerTime_le c x.nB x.L x.codes
  refine .mono_const (.of_body hP ?_) hc
  unfold runTilesBody
  -- β := 0
  light_set (0 : ℕ)
  -- while β < nB
  refine (Ends.while (BandLoop x μ) x.nB (fun β => 12 + innerTime c x.nB x.L x.codes β) ?start
    ?round ?done).mono ?time fun _ h => h
  case start =>
    refine ⟨0, 0, 0, 0, 0, μ, ?_, .refl, fun _ _ _ _ h => by omega⟩
    rw [tilesState, Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero,
      ← frame_append_zeros _ 5]
    rfl
  case round =>
    intro β σ hβ hσ
    obtain ⟨i, pb, s0, s1, res, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using hβ,
      runBand_ends std pruned (e := d) (by omega) pre hβ hσ⟩
  case done =>
    rintro _ ⟨i, pb, s0, s1, res, μ', rfl, inv⟩
    exact ⟨⟨trivial, trivial⟩, by simp, fun b hb b' hb' => inv.done b hb b' hb' (Or.inl hb),
      inv.frame⟩
  case time =>
    simp only [Cond.cost, Expr.cost, Nat.reduceAdd]
    omega

end Light.Sec2
