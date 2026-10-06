/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout
public import ThreeSumApsp.Spec.Sec4.Theorem30.TileTries

/-!
# Theorem 30 in the light language: procedure numbers, time functions, specifications

This file contains no program, and its only proof is a short remark on the trie area when other
cells change. It states the specifications of the procedures 40 to 53 (`nineFirst` to `queryCore`).
The proof of a routine uses only the specifications of the routines that it calls.

* A routine takes its scalars and the base addresses of its arrays as arguments; no routine but
  `preCore` and `queryAt` knows the memory map. The routines for a tile assume the order in which
  their areas lie (`TileCtx.layout`).
* The specification of a routine is a proposition XSpec lim P: "procedure number Proc.x of the
  program P, started on these arguments in a memory that satisfies this, ends within tX steps with
  this result in a memory that satisfies that". The file of x proves XSpec for every program P that
  holds the body of x at the number Proc.x and meets the specifications of the routines that x
  calls. A caller assumes XSpec and feeds it to the rule for calls. XSpec holds at every depth d of
  calls that leaves the levels which x needs below itself.
* Conventions of the programs: the result of a procedure is what it leaves in its local 0; locals
  that are not arguments start at 0. In the proofs, lines such as "have hw := C.std.space_le" or
  "obtain ⟨⟩ := areas p t b0" state the facts on the limits and on the map that the later steps use.
* The larger routines have two records: XArgs holds the arguments and the data behind them, and
  XPre lim μ x says what the routine assumes about the limits and the memory.
* The pure models are those of the specifications of Section 4 (strings are lists of digits, level 1
  first: P_ij is 3(i - 1) + (j - 1), P₀ is 9, the star is 10).
* Time functions are definitions. The time function of a caller is written in terms of the time
  functions of its callees. Their constants are upper bounds, some with room to spare; only the
  shape matters. The lemmas `within8_tAllTiles` and `exists_tQueryCore_le` compare `tAllTiles` and
  `tQueryCore` with the expressions (8) and L ∑ α_d of the paper.
* Tries use addresses relative to the base tr of the trie area: the cell tr + a of the memory is the
  cell a of the trie array T. The area has cap cells, of which the first T.length are in use;
  nothing is assumed about the others (a new vertex clears its eleven cells); the number T.length
  is kept in the cell fp outside the area.

The routines, the pure functions that model them, and the lemmas that say what the models compute:

| number | routine | model | what is proved about the model |
|---|---|---|---|
| 40 | `nineFirst` | `nineFirst` | `head?_nineStrs`: it is the first string of `nineStrs` |
| 41 | `nineNext` | `nineNext` | `nineNext_getElem`: from string i of `nineStrs` to string i + 1 |
| 42 | `scatter` | `scatter`, `starRunIf` | `lowList` and `boxesOf` are built from them |
| 43 | `starFirst` | `starFirst`, `lastStar` | `starBoxes` is `nineStrs` mapped by `starFirst` |
| 44 | `horner` | `ofDigitList 10` | `ofDigitList_digitsT`: the code of a leaf |
| 45 | `lookup` | `trieLookup` | `TrieRep.lookup`, `TrieRep.walkOK` |
| 46 | `insert` | `trieInsert` | `TrieRep.insert`, `TrieRep.insertOK` |
| 47 | `newRoot` | `trieNew` | `TrieRep.new` |
| 48 | `sumTen` | sum of `tenValues` | `exists_lastStar_of_mem_starBoxes`, `abs_dp_partial_sum_le` |
| 49 | `fillList` | `fillTrie` | `fillTrie_rep`, `length_fillTrie_le` |
| 50 | `tile` | `tileTrie` | `fillUpTo_rep`, `length_tileTrie_le` |
| 51 | `allTiles` | `allTries` | `allTries_rep`, `length_allTries_le`, `lookup_allTries` |
| 52 | `outDigits` | `OutDigitsArgs.digits` | `digitsO_outStrOfPos`: the string of a position |
| 53 | `queryCore` | `trieQuery`, `queryTerms` | `trieQuery_allTries`, `abs_query_partial_sum_le` |

The last line of the table continues with `Theorem30.correct`. The model `boxValue` is computed by a
part of `fillList`, which calls `sumTen` for a box with stars.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## Vocabulary -/

/-- The trie area of cap cells from tr: its first cells hold the array T, and the cell fp holds the
length of T. Nothing is assumed about the rest of the area. -/
structure TrieMem (μ : ℕ → ℤ) (tr cap fp : ℕ) (T : List ℤ) : Prop where
  seg : Seg μ tr T
  free : μ fp = T.length
  le_cap : T.length ≤ cap
  fp_out : fp < tr ∨ tr + cap ≤ fp

/-- The trie area stays as it is if its cells and the cell fp do not change. -/
theorem TrieMem.keep {μ μ' : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ} (h : TrieMem μ tr cap fp T)
    (hs : SameOn (fun b => Inside tr cap b ∨ b = fp) μ μ' := by light_keep) :
    TrieMem μ' tr cap fp T :=
  have hle := h.le_cap
  ⟨h.seg.keep, (hs fp (.inr rfl)).trans h.free, hle, h.fp_out⟩

/-- The memory μ' agrees with μ outside the trie area and the cell fp. -/
abbrev SameOutsideTrie (μ μ' : ℕ → ℤ) (tr cap fp : ℕ) : Prop :=
  SameOn (fun b => Outside tr cap b ∧ b ≠ fp) μ μ'

/-! ## Procedure numbers

The numbers 0 to 39 belong to Section 2, the numbers from 40 on to Section 4. This file fixes 40 to
53; the files of the other routines of Section 4 fix theirs. -/

namespace Proc
/-- The numbers of the fourteen routines, in the order in which they call each other. -/
abbrev nineFirst : ℕ := 40
@[inherit_doc nineFirst] abbrev nineNext : ℕ := 41
@[inherit_doc nineFirst] abbrev scatter : ℕ := 42
@[inherit_doc nineFirst] abbrev starFirst : ℕ := 43
@[inherit_doc nineFirst] abbrev horner : ℕ := 44
@[inherit_doc nineFirst] abbrev lookup : ℕ := 45
@[inherit_doc nineFirst] abbrev insert : ℕ := 46
@[inherit_doc nineFirst] abbrev newRoot : ℕ := 47
@[inherit_doc nineFirst] abbrev sumTen : ℕ := 48
@[inherit_doc nineFirst] abbrev fillList : ℕ := 49
@[inherit_doc nineFirst] abbrev tile : ℕ := 50
@[inherit_doc nineFirst] abbrev allTiles : ℕ := 51
@[inherit_doc nineFirst] abbrev outDigits : ℕ := 52
@[inherit_doc nineFirst] abbrev queryCore : ℕ := 53
end Proc

/-! ## Time functions -/

/-- The routines with one loop over a string of n or L digits: a constant number of steps for each
digit. -/
def tNineFirst (n : ℕ) : ℕ := 30 * n + 30
@[inherit_doc tNineFirst] def tNineNext (n : ℕ) : ℕ := 90 * n + 60
@[inherit_doc tNineFirst] def tScatter (L : ℕ) : ℕ := 60 * L + 30
@[inherit_doc tNineFirst] def tStarFirst (L : ℕ) : ℕ := 50 * L + 30
@[inherit_doc tNineFirst] def tHorner (L : ℕ) : ℕ := 20 * L + 10
@[inherit_doc tNineFirst] def tLookup (L : ℕ) : ℕ := 20 * L + 12
@[inherit_doc tNineFirst] def tInsert (L : ℕ) : ℕ := 220 * L + 20
/-- Eleven cells are cleared. -/
def tNewRoot : ℕ := 160
/-- Ten times: write a digit, look up, add. -/
def tSumTen (L : ℕ) : ℕ := 10 * (tLookup L + 40) + 30
/-- A round for one box: stars, value (both branches are paid for), insertion, next leaf. -/
def tFillRound (L : ℕ) : ℕ :=
  tStarFirst L + tHorner L + tSumTen L + tInsert L + tNineNext L + 116
/-- One box: the test of the loop and a round. -/
def tFillStep (L : ℕ) : ℕ := tFillRound L + 4
/-- The boxes with a given number of stars, cnt of them. -/
def tFillList (L cnt : ℕ) : ℕ := tNineFirst L + cnt * tFillStep L + 60
/-- The trie of a tile: its root, then the boxes with 0, …, m - t stars. -/
def tTile (L m t : ℕ) : ℕ :=
  tNewRoot + ((List.range (m - t + 1)).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
    + 60
/-- All tiles. -/
def tAllTiles (L m t nB : ℕ) : ℕ := nB * (nB * (tTile L m t + 80) + 40) + 30
@[inherit_doc tNineFirst] def tOutDigits (L : ℕ) : ℕ := 70 * L + 40
/-- A query, once the digits of its output string are known. -/
def tQueryCore (L m t : ℕ) : ℕ :=
  2 * tNineFirst m + (lowList m t []).length * (tScatter L + tHorner L + tNineNext m + 90)
    + (boxesOf m t []).length * (tScatter L + tLookup L + tNineNext m + 90) + 120

/-! ## The enumeration of the strings with a bounded number of nines -/

/-- nineFirst(a, n, lo) writes the least string of n digits with lo nines. -/
def NineFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo : ℕ) (μ : ℕ → ℤ), lo ≤ n → a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineFirst d [a, n, lo] μ (tNineFirst n) fun _ μ' =>
      SegN μ' a (nineFirst n lo) ∧ SameOutside μ μ' a n

/-- nineNext(a, n, lo, hi) replaces the string at a by the next one and returns 1, or leaves it and
returns 0 if it is the last one. -/
def NineNextSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l ∈ nineStrs n lo hi →
    a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineNext d [a, n, lo, hi] μ (tNineNext n) fun r μ' =>
      SegN μ' a ((nineNext lo hi l).getD l) ∧ r = (if (nineNext lo hi l).isSome then 1 else 0) ∧
        SameOutside μ μ' a n

/-! ## Strings -/

/-- scatter(w, s, out, L, star) writes at out the string at w with its nines replaced by the digits
of the string at s, whose leading nines are first turned into stars if star = 1. -/
def ScatterSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (w s out L : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ), SegN μ w wl → SegN μ s sl →
    wl.length = L → sl.length = wl.count 9 → Apart out L w L → Apart out L s sl.length →
    w + L < lim.space → s + sl.length < lim.space → out + L < lim.space →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.scatter d [w, s, out, L, if star then 1 else 0] μ (tScatter L) fun _ μ' =>
      SegN μ' out (scatter wl (starRunIf star sl)) ∧ SameOutside μ μ' out L

/-- starFirst(cur, box, L, e) writes at box the string at cur with its first e nines turned into
stars; it returns the position of the last star (0 if e = 0). -/
def StarFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (cur box L e : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ cur l → l.length = L → Apart box L cur L →
    cur + L < lim.space → box + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.starFirst d [cur, box, L, e] μ (tStarFirst L) fun r μ' =>
      SegN μ' box (starFirst e l) ∧ r = ((lastStar (starFirst e l)).getD 0 : ℕ) ∧
        SameOutside μ μ' box L

/-- horner(a, L) returns the number with the L decimal digits at a, most significant first. -/
def HornerSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a L : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l.length = L → (∀ d ∈ l, d < 10) →
    a + L < lim.space →
    (10 : ℤ) ^ L ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.horner d [a, L] μ (tHorner L) fun r μ' => r = (ofDigitList 10 l : ℕ) ∧
      μ' = μ

/-! ## Tries -/

/-- lookup(tr, root, key, L) returns the value stored for the string at key in the trie with the
given root. -/
def LookupSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (tr root key L : ℕ) (T : List ℤ) (kl : List ℕ) (μ : ℕ → ℤ), Seg μ tr T → SegN μ key kl →
    kl.length = L →
    (∀ d ∈ kl, d < 11) → WalkOK T root kl → tr + T.length < lim.space → key + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.lookup d [tr, root, key, L] μ (tLookup L) fun r μ' =>
      r = trieLookup T root kl ∧ μ' = μ

/-- The arguments of insert(tr, root, key, L, val, fp), and the data behind them: the trie area of
cap cells at tr holds the array T, the cell fp holds its length, and the string kl is at key. -/
structure InsertArgs where
  (tr root key L : ℕ) (val : ℤ) (fp : ℕ)
  (cap : ℕ) (T : List ℤ) (kl : List ℕ)

/-- The values of the arguments of `insert`. -/
abbrev InsertArgs.vals (x : InsertArgs) : List ℤ := [x.tr, x.root, x.key, x.L, x.val, x.fp]

/-- What `insert` assumes: the tries and the string are in the memory, the walk down the string is
safe, there is room for one new vertex at each level, the string lies apart from the trie area and
from the free pointer, and everything lies within the memory. -/
structure InsertPre (lim : Limits) (μ : ℕ → ℤ) (x : InsertArgs) : Prop where
  trie : TrieMem μ x.tr x.cap x.fp x.T
  seg : SegN μ x.key x.kl
  len : x.kl.length = x.L
  digits : ∀ d ∈ x.kl, d < 11
  walk : InsertOK x.T x.root x.kl
  room : x.T.length + 11 * x.kl.length ≤ x.cap
  apart : Apart x.key x.kl.length x.tr x.cap := by light_arith
  free_out : Outside x.key x.kl.length x.fp := by light_arith
  area_in : x.tr + x.cap < lim.space := by light_arith
  key_in : x.key + x.kl.length < lim.space := by light_arith
  free_in : x.fp < lim.space := by light_arith

/-- insert(tr, root, key, L, val, fp) stores val for the string at key in the trie with the given
root. A new vertex is taken from the free part of the trie area, and its eleven cells are
cleared. -/
def InsertSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : InsertArgs) (μ : ℕ → ℤ), InsertPre lim μ x →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.insert d x.vals μ (tInsert x.L) fun _ μ' =>
      TrieMem μ' x.tr x.cap x.fp (trieInsert x.T x.root x.kl x.val) ∧
        SameOutsideTrie μ μ' x.tr x.cap x.fp

/-- newRoot(tr, fp) takes a new vertex from the free part of the trie area, clears its eleven cells,
and returns its address. -/
def NewRootSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (tr cap fp : ℕ) (T : List ℤ) (μ : ℕ → ℤ), TrieMem μ tr cap fp T → T.length + 11 ≤ cap →
    tr + cap < lim.space →
    fp < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.newRoot d [tr, fp] μ tNewRoot fun r μ' =>
      r = T.length ∧ TrieMem μ' tr cap fp (trieNew T) ∧ SameOutsideTrie μ μ' tr cap fp

/-! ## The dynamic program of Lemma 29 -/

/-- The arguments of sumTen(tr, root, box, L, p), and the data behind them: the array T of the tries
is at tr, and the string l, which has a star at the position p, is at box. -/
structure SumTenArgs where
  (tr root box L p : ℕ)
  (T : List ℤ) (l : List ℕ)

/-- The values of the arguments of `sumTen`. -/
abbrev SumTenArgs.vals (x : SumTenArgs) : List ℤ := [x.tr, x.root, x.box, x.L, x.p]

/-- The ten values that `sumTen` adds up. -/
abbrev SumTenArgs.values (x : SumTenArgs) : List ℤ := tenValues (trieLookup x.T x.root) x.l x.p

/-- What `sumTen` assumes: the array of the tries and the box, which do not meet and lie within the
memory, the position of the star, that the ten strings are stored, and that the partial sums of
their values fit in a word. -/
structure SumTenPre (lim : Limits) (μ : ℕ → ℤ) (x : SumTenArgs) : Prop where
  area : Seg μ x.tr x.T
  seg : SegN μ x.box x.l
  len : x.l.length = x.L
  star : x.p < x.l.length
  digits : ∀ d ∈ x.l, d < 11
  walk : ∀ d < 10, WalkOK x.T x.root (x.l.set x.p d)
  sums : ∀ j ≤ 10, |(x.values.take j).sum| ≤ lim.word
  apart : Apart x.box x.l.length x.tr x.T.length := by light_arith
  area_in : x.tr + x.T.length < lim.space := by light_arith
  box_in : x.box + x.l.length < lim.space := by light_arith

/-- sumTen(tr, root, box, L, p) returns the sum of the ten values, looked up in the trie with the
given root, of the strings obtained from the string at box by writing 0, …, 9 at the position p; it
leaves the memory as it was. -/
def SumTenSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : SumTenArgs) (μ : ℕ → ℤ), SumTenPre lim μ x →
    ∀ d, d + 1 ≤ lim.depth → Meets lim P Proc.sumTen d x.vals μ (tSumTen x.L) fun r μ' =>
      r = x.values.sum ∧ μ' = μ

/-- What the routines for a tile assume about their surroundings: the parameters, the two encodings
of the tile and where they are, the trie area, two scratch strings, and the limits. -/
structure TileCtx (lim : Limits) (L m t : ℕ) (encA encB : Leaf L → ℤ)
    (aA aB tr cap fp cur box : ℕ) : Prop where
  std : Std lim
  ht : t ≤ m
  hmL : m ≤ L
  /-- Every value and every partial sum fits in a word. -/
  value_le : ∃ A B : ℤ, (∀ τ, |encA τ| ≤ A) ∧ (∀ τ, |encB τ| ≤ B) ∧ 10 ^ m * (A * B) ≤ lim.word
  pow_le : (10 : ℤ) ^ L ≤ lim.word
  /-- The two encodings, the two scratch strings, the cell fp and the trie area lie in this order,
  and the last cell of the memory lies behind them. -/
  layout : InOrder (lim.space - 1)
    [(aA, 10 ^ L), (aB, 10 ^ L), (cur, L), (box, L), (fp, 1), (tr, cap)]

/-- The memory μ' agrees with μ outside the trie area, the cell fp, and the two scratch strings. -/
abbrev SameOutsideTile (μ μ' : ℕ → ℤ) (L tr cap fp cur box : ℕ) : Prop :=
  SameOn (fun b => Outside tr cap b ∧ b ≠ fp ∧ Outside cur L b ∧ Outside box L b) μ μ'

/-- The arguments of fillList(e, root, aA, aB, tr, fp, cur, box, L, mt), with mt = m - t, and the
data behind them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap
cells at tr holds the array T, and fp holds its length; cur and box (L cells each) are scratch. The
array is described as in `fillTrie_rep`: tile is the number of the trie (the number of the tile),
roots tile its root, old what the other tries hold, and lo the address from which the tries stand
in the array. -/
structure FillListArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box e tile lo : ℕ)
  roots : ℕ → ℕ
  old : ℕ × List ℕ → Option ℤ
  T : List ℤ

namespace FillListArgs

variable (x : FillListArgs)

/-- The root of the trie of the tile. -/
abbrev root : ℕ := x.roots x.tile

/-- The values of the arguments of `fillList`. -/
abbrev vals : List ℤ :=
  [x.e, x.root, x.aA, x.aB, x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)]

/-- The boxes that `fillList` inserts. -/
abbrev boxes : List (List ℕ) := starBoxes x.L x.m x.t x.e

/-- What the tries hold when the boxes in pre have been inserted. -/
abbrev stored (pre : List (List ℕ)) : ℕ × List ℕ → Option ℤ :=
  storedUpTo x.old x.tile (arrT x.encA) (arrT x.encB) x.L x.m x.t x.e pre

end FillListArgs

/-- What `fillList` assumes: the surroundings of a tile, a trie that holds the boxes with fewer
stars, the tries and the two encodings in the memory, and room for L vertices for each box. -/
structure FillListPre (lim : Limits) (μ : ℕ → ℤ) (x : FillListArgs) : Prop where
  ctx : TileCtx lim x.L x.m x.t x.encA x.encB x.aA x.aB x.tr x.cap x.fp x.cur x.box
  stars_le : x.e ≤ x.m - x.t
  root_ne : x.root ≠ 0
  rep : TrieRep x.L x.lo x.T x.roots (x.stored [])
  trie : TrieMem μ x.tr x.cap x.fp x.T
  segA : Seg μ x.aA (arrT x.encA)
  segB : Seg μ x.aB (arrT x.encB)
  room : x.T.length + 11 * x.L * x.boxes.length ≤ x.cap

/-- fillList(e, root, aA, aB, tr, fp, cur, box, L, mt), with mt = m - t, inserts the boxes with e
stars, with their values, into the trie of the tile, which has the given root and holds the boxes
with fewer stars; for e ≥ 1 the values are sums of ten values looked up in it. -/
def FillListSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : FillListArgs) (μ : ℕ → ℤ), FillListPre lim μ x →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.fillList d x.vals μ (tFillList x.L x.boxes.length) fun _ μ' =>
      TrieMem μ' x.tr x.cap x.fp (fillTrie (arrT x.encA) (arrT x.encB) x.root x.e x.boxes x.T) ∧
        SameOutsideTile μ μ' x.L x.tr x.cap x.fp x.cur x.box

/-- The arguments of tile(aA, aB, ra, tr, fp, cur, box, L, mt), with mt = m - t, and the data behind
them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap cells at tr
holds the tries s.cells of the earlier tiles, in which the values old are stored, and fp holds their
length; their roots s.roots, one for each tile, are in the cells from aR, and ra is the address of
the cell behind them; cur and box (L cells each) are scratch; the tries stand in the trie array from
the address lo on. -/
structure TileArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box aR : ℕ)
  s : TrieStore
  old : ℕ × List ℕ → Option ℤ
  lo : ℕ

/-- The trie array and the roots after the trie of the tile has been built. -/
def TileArgs.tries (x : TileArgs) : TrieStore :=
  tileTrie (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s

/-- The number of cells for the roots, the older ones and the new one. -/
def TileArgs.cells (x : TileArgs) : ℕ := x.s.roots.length + 1

/-- The cells that `tile` keeps: those outside the trie area, the cell fp, the two scratch strings
and the cell of the new root. -/
abbrev TileArgs.Kept (x : TileArgs) (b : ℕ) : Prop :=
  Outside x.tr x.cap b ∧ b ≠ x.fp ∧ Outside x.cur x.L b ∧ Outside x.box x.L b ∧
    b ≠ x.aR + x.s.roots.length

/-- What `tile` assumes: the surroundings of a tile, the older tries and roots and the two encodings
in the memory, room for the new trie, and the place of the cells of the roots. -/
structure TilePre (lim : Limits) (μ : ℕ → ℤ) (x : TileArgs) : Prop where
  ctx : TileCtx lim x.L x.m x.t x.encA x.encB x.aA x.aB x.tr x.cap x.fp x.cur x.box
  rep : x.s.Holds x.L x.lo x.old
  trie : TrieMem μ x.tr x.cap x.fp x.s.cells
  roots : SegN μ x.aR x.s.roots
  segA : Seg μ x.aA (arrT x.encA)
  segB : Seg μ x.aB (arrT x.encB)
  room : x.s.cells.length + 11 * (1 + x.L * (boxes x.L x.m x.t).card) ≤ x.cap
  /-- The cells of the roots lie between the cell fp and the trie area. -/
  rootsPlace : x.fp < x.aR ∧ x.aR + x.cells ≤ x.tr

/-- `tile` builds the trie of one tile, with the values of all its boxes, on top of the older tries,
and writes its root into the cell behind the older roots. It changes only the trie area, the cell
fp, the two scratch strings and this cell. -/
def TileSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : TileArgs) (μ : ℕ → ℤ), TilePre lim μ x →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.tile d
      [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ
      (tTile x.L x.m x.t) fun _ μ' =>
        TrieMem μ' x.tr x.cap x.fp x.tries.cells ∧ SegN μ' x.aR x.tries.roots ∧ SameOn x.Kept μ μ'

/-- The arguments of allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt), with T = 10^L and
mt = m - t, and the data behind them: the encodings of the nB row bands from aENCA and of the nB
column bands from aENCB (band β at the offset β 10^L), the cells of the roots from aR (one for each
tile), the trie area of cap cells from tr, the cell fp for its length, and two scratch strings cur
and box. -/
structure AllTilesArgs where
  (L m t nB : ℕ)
  (encA encB : ℕ → Leaf L → ℤ)
  (aENCA aENCB aR tr cap fp cur box : ℕ)

/-- The tries of all tiles, and their roots. -/
def AllTilesArgs.tries (x : AllTilesArgs) : TrieStore :=
  allTries x.L x.m x.t (tileList x.nB x.encA x.encB)

/-- The cells that `allTiles` keeps: those below cur and those behind the trie area. -/
abbrev AllTilesArgs.Kept (x : AllTilesArgs) (b : ℕ) : Prop := b < x.cur ∨ x.tr + x.cap ≤ b

/-- What `allTiles` assumes: the limits, room in the trie area for the tries of all tiles, the order
of the areas, the encodings in the memory, and the trie array [0]. -/
structure AllTilesPre (lim : Limits) (μ : ℕ → ℤ) (x : AllTilesArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  m_le : x.m ≤ x.L
  /-- Every value and every partial sum fits in a word. -/
  value_le : ∃ A B : ℤ, (∀ β τ, |x.encA β τ| ≤ A) ∧ (∀ β τ, |x.encB β τ| ≤ B) ∧
    10 ^ x.m * (A * B) ≤ lim.word
  pow_le : (10 : ℤ) ^ x.L ≤ lim.word
  cap_ge : 1 + x.nB * x.nB * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) ≤ x.cap
  /-- The areas lie in this order, without overlap, below the end of the memory. -/
  order : x.aENCA + x.nB * 10 ^ x.L ≤ x.aENCB ∧ x.aENCB + x.nB * 10 ^ x.L ≤ x.cur ∧
    x.cur + x.L ≤ x.box ∧ x.box + x.L ≤ x.fp ∧ x.fp < x.aR ∧
    x.aR + x.nB * x.nB ≤ x.tr ∧ x.tr + x.cap < lim.space
  segA : ∀ β < x.nB, Seg μ (x.aENCA + β * 10 ^ x.L) (arrT (x.encA β))
  segB : ∀ β < x.nB, Seg μ (x.aENCB + β * 10 ^ x.L) (arrT (x.encB β))
  trie : TrieMem μ x.tr x.cap x.fp [0]

/-- `allTiles` builds the tries of all tiles, starting from the trie array [0], and changes nothing
below cur or behind the trie area. -/
def AllTilesSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : AllTilesArgs) (μ : ℕ → ℤ), AllTilesPre lim μ x →
    ∀ d, d + 4 ≤ lim.depth →
    Meets lim P Proc.allTiles d [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp,
      x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ (tAllTiles x.L x.m x.t x.nB) fun _ μ' =>
        TrieMem μ' x.tr x.cap x.fp x.tries.cells ∧ SegN μ' x.aR x.tries.roots ∧ SameOn x.Kept μ μ'

/-! ## A query -/

/-- The arguments of outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) and the data behind them: gI and gJ
are the numbers of the blocks of I and J within their bands, dI and dJ the addresses of the base-3
digits rI and rJ of their offsets, aMASK the address of the list of the subsets (a mask of L cells
for each), k0 the number of blocks of a band, L the number of levels, m of which belong to a subset,
and wd the address of the result. -/
structure OutDigitsArgs where
  (gI gJ dI dJ aMASK k0 L wd m : ℕ)
  (rI rJ : List ℕ)

namespace OutDigitsArgs

variable (x : OutDigitsArgs)

/-- The mask of the subset of the block product (gI, gJ). -/
def mask : List Bool := unrank x.L x.m (x.gI * x.k0 + x.gJ)

/-- The address of that mask in the list of the subsets. -/
def base : ℕ := x.aMASK + (x.gI * x.k0 + x.gJ) * x.L

/-- The digits of the output string: 9 at the levels of the subset, and elsewhere 3 a + b for the
next digits a of rI and b of rJ. -/
def digits : List ℕ := outDigits x.m x.mask x.rI x.rJ

end OutDigitsArgs

/-- What `outDigits` assumes: the mask of the subset and the digits of the two offsets stand in the
memory, and the L cells from wd are apart from all three. -/
structure OutDigitsPre (lim : Limits) (μ : ℕ → ℤ) (x : OutDigitsArgs) : Prop where
  std : Std lim
  m_le : x.m ≤ x.L
  gI_lt : x.gI < x.k0
  gJ_lt : x.gJ < x.k0
  index_lt : x.gI * x.k0 + x.gJ < x.L.choose x.m
  segMask : SegN μ x.base (x.mask.map fun b => if b then 1 else 0)
  segI : SegN μ x.dI x.rI
  segJ : SegN μ x.dJ x.rJ
  lenI : x.rI.length = x.L - x.m
  lenJ : x.rJ.length = x.L - x.m
  ltI : ∀ a ∈ x.rI, a < 3
  ltJ : ∀ a ∈ x.rJ, a < 3
  apartMask : Apart x.wd x.L x.base x.L
  apartI : Apart x.wd x.L x.dI (x.L - x.m)
  apartJ : Apart x.wd x.L x.dJ (x.L - x.m)
  spaceMasks : x.aMASK + x.k0 * x.k0 * x.L < lim.space
  spaceI : x.dI + x.L < lim.space
  spaceJ : x.dJ + x.L < lim.space
  spaceDest : x.wd + x.L < lim.space

/-- `outDigits` writes the digits of the output string at wd and changes nothing else. -/
def OutDigitsSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : OutDigitsArgs) (μ : ℕ → ℤ), OutDigitsPre lim μ x →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.outDigits d [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd] μ
      (tOutDigits x.L) fun _ μ' => SegN μ' x.wd x.digits ∧ SameOutside μ μ' x.wd x.L

/-- The arguments of queryCore(aA, aB, tr, root, wd, ss, box, L, m, t) and the data behind them: the
encodings encA and encB of the tile are at aA and aB, the trie array T at tr, root is the root of
the trie of the tile, the digits of the output string η are at wd; ss (m cells) and box (L cells)
are scratch. -/
structure QueryCoreArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  η : OutStr L
  (aA aB tr root wd ss box : ℕ)
  T : List ℤ

/-- The numbers that the query adds up, in the order in which it adds them. -/
def QueryCoreArgs.terms (x : QueryCoreArgs) : List ℤ :=
  queryTerms x.m x.t (arrT x.encA) (arrT x.encB) (trieLookup x.T x.root) (digitsO x.η)

/-- What `queryCore` assumes: the data stand in the memory, every box of the query is found in the
trie of the tile, all partial sums fit in a word, and the two scratch strings are apart from each
other and from the data. -/
structure QueryCorePre (lim : Limits) (μ : ℕ → ℤ) (x : QueryCoreArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  card : (innerSetO x.η).card = x.m
  segA : Seg μ x.aA (arrT x.encA)
  segB : Seg μ x.aB (arrT x.encB)
  segT : Seg μ x.tr x.T
  segDigits : SegN μ x.wd (digitsO x.η)
  walk : ∀ l ∈ boxesOf x.m x.t (digitsO x.η), WalkOK x.T x.root l
  sums : ∀ j, |(x.terms.take j).sum| ≤ lim.word
  prod : ∀ τ, |x.encA τ * x.encB τ| ≤ lim.word
  pow : (10 : ℤ) ^ x.L ≤ lim.word
  ss_wd : Apart x.ss x.m x.wd x.L
  box_wd : Apart x.box x.L x.wd x.L
  ss_box : Apart x.ss x.m x.box x.L
  ss_aA : Apart x.ss x.m x.aA (10 ^ x.L)
  ss_aB : Apart x.ss x.m x.aB (10 ^ x.L)
  box_aA : Apart x.box x.L x.aA (10 ^ x.L)
  box_aB : Apart x.box x.L x.aB (10 ^ x.L)
  ss_tr : Apart x.ss x.m x.tr x.T.length
  box_tr : Apart x.box x.L x.tr x.T.length
  aA_lt : x.aA + 10 ^ x.L < lim.space
  aB_lt : x.aB + 10 ^ x.L < lim.space
  tr_lt : x.tr + x.T.length < lim.space
  wd_lt : x.wd + x.L < lim.space
  ss_lt : x.ss + x.m < lim.space
  box_lt : x.box + x.L < lim.space

/-- `queryCore` returns the sum `trieQuery` for the output string whose digits are at wd: the
products at its leaves of order below t, read from the two encodings, and what the trie with the
given root holds for its boxes. This is the sum of Lemma 28 if the trie holds the values of the
boxes (`trieQuery_allTries`). The routine changes only the two scratch strings. -/
def QueryCoreSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : QueryCoreArgs) (μ : ℕ → ℤ), QueryCorePre lim μ x →
    ∀ d, d + 1 ≤ lim.depth →
    Meets lim P Proc.queryCore d [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t] μ
      (tQueryCore x.L x.m x.t) fun r μ' =>
        r = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
          SameOutside2 μ μ' x.ss x.m x.box x.L

end Light.Sec4
