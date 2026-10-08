/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec4.Theorem30.QueryLists
public import ThreeSumApsp.Spec.Sec4.Theorem30.StarBoxes
public import ThreeSumApsp.Spec.Sec4.Theorem30.Trie
public import ThreeSumApsp.Util.Index

/-!
# The trie of a tile, and the tries of all tiles (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  `tileTrie` builds this trie.

"We compute the values of the boxes in increasing order of their number of stars": `fillUpTo` goes
through the boxes with 0, 1, … stars (`starBoxes`), and `fillTrie` inserts the boxes with e stars
with their values (`boxValue`): the value of a box without stars is "the product of its two numbers
in the encodings", the value of a box with stars is computed "with ten lookups in the trie" of the
tile.  `allTries` does this for all tiles, in one array; the number of a trie is the number of its
tile.  The array and the list of the roots form a record `TrieStore`.

What the array holds at a moment is a function from pairs (the number of a trie, a box) to values:
`storedUpTo` in the middle of a tile, `storedAll` between two tiles.
1. One more box is one more entry, the state after all boxes with k stars is the state before the
   first box with k + 1 stars, and a complete tile adds its boxes to `storedAll`
   (`storedUpTo_snoc`, `storedUpTo_succ`, `storedAll_snoc`).
2. Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars
   (`exists_lastStar_of_mem_starBoxes`); so, once the boxes with e stars are stored, the value
   computed for the box is that of the dynamic program (`boxValue_eq`).
3. So the array represents these functions, in the sense of `TrieRep`, after some boxes with e stars
   (`fillTrie_rep`), after all boxes with fewer than k stars (`fillUpTo_rep`) and after some tiles
   (`allTries_rep`).
4. Hence a lookup returns the value of the dynamic program of Lemma 29 (`lookup_allTries`), which is
   the value of the box: the array holds "for every tile, the values of all its boxes"
   (`lookup_allTries_eq_val`).  Every box that a query reads is there (`boxesOf_mem_starBoxes`).
5. Space: "O(L) […] space per box" (`length_tileTrie_le`, `length_allTries_le`).
6. The bottom line, for any list of tiles: the query that reads the values of its boxes from the
   trie of its tile (`trieQuery`) returns `queryValue` (`trieQuery_allTries`), and all its walks
   down the trie are safe (`walkOK_allTries`).  The tiles of the product are `tileList`, and
   `tilesBefore` is its part before a tile.

Two ladders lead from the arrays to the paper.
* A query: `trieQuery` adds up `queryTerms` with the values read from the trie; these are the values
  of the dynamic program (`queryTerms_allTries`), with which the sum is `queryValue` on cubes
  (`sum_queryTerms_storedD`), which is `querySum`, the sum of Lemma 28 (`lemma_29_values`, inside
  `Theorem30.correct`), which is the entry `(X * Y) I J` (`Theorem30.query`).
* The value of a box: `boxValue` reads from the trie; it is `dpValueD` on lists of digits
  (`boxValue_eq`), which is `dpValue` on cubes (`dpValueD_digitsC`), which is `Cube.val`
  (`lemma_29_values`).  `lookup_allTries_eq_val` is the whole ladder; no other proof rests on it.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Building the tries -/

/-- A tile, given by the arrays of its two encodings. -/
structure TileEnc where
  encA : List ℤ
  encB : List ℤ

/-- The tries of some tiles in one array: the array, and the addresses of the roots.  The trie of
tile number i has the root number i. -/
structure TrieStore where
  cells : List ℤ
  roots : List ℕ

namespace TrieStore

/-- The address of the root of trie number i, or 0 if there is no such trie. -/
def root (s : TrieStore) (i : ℕ) : ℕ := s.roots.getD i 0

/-- The value stored for the string l in trie number i. -/
def lookup (s : TrieStore) (i : ℕ) (l : List ℕ) : ℤ := trieLookup s.cells (s.root i) l

/-- The tries hold the entries of f, in the sense of `TrieRep`. -/
def Holds (L lo : ℕ) (s : TrieStore) (f : ℕ × List ℕ → Option ℤ) : Prop :=
  TrieRep L lo s.cells s.root f

/-- A new, empty trie behind the others. -/
def new (s : TrieStore) : TrieStore := ⟨trieNew s.cells, s.roots ++ [s.cells.length]⟩

/-- The new trie has the next number, and its root is at the old end of the array. -/
theorem root_new (s : TrieStore) : s.new.root s.roots.length = s.cells.length := by
  simp [root, new]

/-- A new, empty trie changes no entry. -/
theorem Holds.new {L lo : ℕ} {s : TrieStore} {f : ℕ × List ℕ → Option ℤ} (h : s.Holds L lo f) :
    s.new.Holds L lo f := by
  have hroot : s.new.root = Function.update s.root s.roots.length s.cells.length :=
    List.getD_append_singleton _ _ _
  rw [Holds, hroot]
  exact TrieRep.new h _ (List.getD_eq_default _ _ le_rfl)

end TrieStore

/-- The value of a box l (the paper's π) with e stars, computed from the array T: for e = 0 "the
product of its two numbers in the encodings"; for e ≥ 1 the sum val(π) = ∑_λ val(π[ℓ ← λ]), where ℓ
is "the highest level at which π has a star", computed "with ten lookups in the trie" of the tile,
which has the given root.  The function looks only at whether e = 0. -/
def boxValue (encA encB T : List ℤ) (root : ℕ) : ℕ → List ℕ → ℤ
  | 0, l => leafProduct encA encB (starsToNines l)
  | _ + 1, l => sumAtLastStar (trieLookup T root) l

/-- The value of a box without stars is the product at the leaf with its digits. -/
theorem boxValue_zero (encA encB T : List ℤ) (root : ℕ) {l : List ℕ} (hl : ∀ d ∈ l, d < 10) :
    boxValue encA encB T root 0 l = leafProduct encA encB l := by
  rw [boxValue, starsToNines_of_notMem fun h => absurd (hl 10 h) (lt_irrefl 10)]

/-- "Generating the boxes with e stars and inserting them into the trie": the array after some boxes
with e stars have been inserted into the trie of the tile, which has the given root, each with its
value, computed from the array as it is before the box is inserted. -/
def fillTrie (encA encB : List ℤ) (root e : ℕ) (boxes : List (List ℕ)) (T : List ℤ) : List ℤ :=
  boxes.foldl (fun T l => trieInsert T root l (boxValue encA encB T root e l)) T

/-- "We compute the values of the boxes in increasing order of their number of stars": the array
after the boxes with 0, …, k - 1 stars have been inserted, in this order, into the trie with the
given root. -/
def fillUpTo (encA encB : List ℤ) (L m t root : ℕ) : ℕ → List ℤ → List ℤ
  | 0, T => T
  | k + 1, T => fillTrie encA encB root k (starBoxes L m t k) (fillUpTo encA encB L m t root k T)

/-- The tries s with a new trie that holds the boxes with fewer than k stars. -/
def tileTrieUpTo (encA encB : List ℤ) (L m t : ℕ) (s : TrieStore) (k : ℕ) : TrieStore :=
  { s.new with cells := fillUpTo encA encB L m t s.cells.length k s.new.cells }

/-- Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile".  The trie is added to an array that may hold the tries of
other tiles already: a new root, and then all the boxes, which have at most m - t stars. -/
def tileTrie (encA encB : List ℤ) (L m t : ℕ) (s : TrieStore) : TrieStore :=
  tileTrieUpTo encA encB L m t s (m - t + 1)

/-- The tries of all tiles in one array: the trie of tile number i has the number i.  Cell 0 is left
unused, since the address 0 means: no vertex. -/
def allTries (L m t : ℕ) (tiles : List TileEnc) : TrieStore :=
  tiles.foldl (fun s ab => tileTrie ab.encA ab.encB L m t s) ⟨[0], []⟩

/-- The query of Theorem 30.  For every box of the output string "we look up its value in the trie
of the tile", which has the given root. -/
def trieQuery (m t : ℕ) (encA encB T : List ℤ) (root : ℕ) (w : List ℕ) : ℤ :=
  (queryTerms m t encA encB (trieLookup T root) w).sum

private theorem fillTrie_cons (encA encB : List ℤ) (root e : ℕ) (l : List ℕ)
    (boxes : List (List ℕ)) (T : List ℤ) :
    fillTrie encA encB root e (l :: boxes) T
      = fillTrie encA encB root e boxes (trieInsert T root l (boxValue encA encB T root e l)) := rfl

/-- The trie of one more tile is built on top of the tries of the tiles before it. -/
theorem allTries_snoc (L m t : ℕ) (tiles : List TileEnc) (ab : TileEnc) :
    allTries L m t (tiles ++ [ab]) = tileTrie ab.encA ab.encB L m t (allTries L m t tiles) := by
  simp [allTries, List.foldl_append]

/-- Every box that a query reads is a box of the tile. -/
private theorem boxesOf_mem_starBoxes {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) (l : List ℕ) (hl : l ∈ boxesOf m t (digitsO η)) :
    IsBoxDigits L m t l := by
  obtain ⟨π, hπ, rfl⟩ := exists_of_mem_boxesOf ht hη l hl
  obtain ⟨V, hV, hπ⟩ := Finset.mem_biUnion.mp hπ
  exact (isBoxDigits_digitsC m t π).mpr (Theorem30.lookup hV hπ)

/-! ## What the tries hold -/

/-- What the tries hold in the middle of tile number i: on top of the entries old, trie number i
holds the boxes with fewer than k stars and the boxes in pre (some boxes with k stars).  The entry
for the key (i, l) is the value `storedD encA encB l` of the dynamic program. -/
def storedUpTo (old : ℕ × List ℕ → Option ℤ) (i : ℕ) (encA encB : List ℤ) (L m t k : ℕ)
    (pre : List (List ℕ)) : ℕ × List ℕ → Option ℤ
  | (n, l) =>
    if n = i ∧ ((starCount l < k ∧ IsBoxDigits L m t l) ∨ l ∈ pre) then
      some (storedD encA encB l)
    else old (n, l)

/-- What the tries of all tiles hold, the third component of the data structure: "for every tile,
the values of all its boxes (the boxes are the same strings in every tile, but their values depend
on the input arrays of the tile)".  Trie number i holds the values of all boxes for tile number i.
The array holds at least these entries (`allTries_rep`, in the sense of `TrieRep`). -/
def storedAll (L m t : ℕ) (tiles : List TileEnc) : ℕ × List ℕ → Option ℤ
  | (n, l) =>
    if IsBoxDigits L m t l then tiles[n]?.map fun ab => storedD ab.encA ab.encB l else none

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L m t : ℕ}

/-- The boxes with fewer than k stars are stored with the values of the dynamic program. -/
theorem storedUpTo_of_lt {k e : ℕ} (pre : List (List ℕ)) {l : List ℕ} (he : e < k)
    (hl : l ∈ starBoxes L m t e) :
    storedUpTo old i encA encB L m t k pre (i, l) = some (dpValueD encA encB e l) := by
  obtain rfl := starCount_of_mem_starBoxes hl
  simp [storedUpTo, storedD, he, hl]

/-- Before the first box, there are the old entries only. -/
private theorem storedUpTo_zero (x : ℕ × List ℕ) (v : ℤ)
    (h : storedUpTo old i encA encB L m t 0 [] x = some v) : old x = some v := by
  simpa [storedUpTo] using h

/-- One more box is one more entry. -/
private theorem storedUpTo_snoc {e : ℕ} (pre : List (List ℕ)) {l : List ℕ}
    (hl : l ∈ starBoxes L m t e) :
    storedUpTo old i encA encB L m t e (pre ++ [l]) =
      Function.update (storedUpTo old i encA encB L m t e pre) (i, l)
        (some (dpValueD encA encB e l)) := by
  funext ⟨n, l'⟩
  by_cases hx : (n, l') = (i, l)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    simp [storedUpTo, storedD, starCount_of_mem_starBoxes hl]
  · rw [Function.update_of_ne hx]
    have hne : ¬ (n = i ∧ l' = l) := fun ⟨hn, hl'⟩ => hx (by rw [hn, hl'])
    simp only [storedUpTo, List.mem_append, List.mem_singleton]
    -- the two conditions differ only at the key (i, l)
    exact if_congr (by tauto) rfl rfl

/-- The state after all boxes with k stars is the state before the first box with k + 1 stars. -/
private theorem storedUpTo_succ (k : ℕ) :
    storedUpTo old i encA encB L m t (k + 1) [] =
      storedUpTo old i encA encB L m t k (starBoxes L m t k) := by
  funext ⟨n, l⟩
  simp only [storedUpTo, List.not_mem_nil, or_false]
  refine if_congr (and_congr_right fun _ => ?_) rfl rfl
  rw [Nat.lt_succ_iff_lt_or_eq, or_and_right]
  exact or_congr_right
    ⟨fun h => h.1 ▸ h.2, fun h => ⟨starCount_of_mem_starBoxes h, isBoxDigits_of_mem_starBoxes h⟩⟩

end

/-- The boxes of tile number i are stored with the values of its dynamic program. -/
private theorem storedAll_of_mem {L m t : ℕ} {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
    {l : List ℕ} (hi : tiles[i]? = some ab) (hl : IsBoxDigits L m t l) :
    storedAll L m t tiles (i, l) = some (storedD ab.encA ab.encB l) := by
  simp [storedAll, hl, hi]

/-- One more tile: what is stored then was stored before or belongs to the new tile. -/
private theorem storedAll_snoc {L m t : ℕ} (tiles : List TileEnc) (ab : TileEnc)
    (x : ℕ × List ℕ) (v : ℤ) (h : storedAll L m t (tiles ++ [ab]) x = some v) :
    storedUpTo (storedAll L m t tiles) tiles.length ab.encA ab.encB L m t (m - t + 1) [] x
      = some v := by
  obtain ⟨n, l⟩ := x
  simp only [storedAll] at h
  split_ifs at h with hl
  simp only [storedUpTo]
  rcases Nat.lt_trichotomy n tiles.length with hn | hn | hn
  · -- an older tile
    rw [if_neg (by omega), ← h, List.getElem?_append_left hn]
    exact if_pos hl
  · -- the new tile
    rw [if_pos ⟨hn, Or.inl ⟨Nat.lt_succ_of_le (le_of_mem_starBoxes hl), hl⟩⟩, ← h, hn]
    simp
  · -- there is no such tile
    rw [List.getElem?_eq_none (by simp; omega)] at h
    simp at h

/-! ## The array represents what it should hold -/

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L lo m t e : ℕ}
  {roots : ℕ → ℕ}

/-- With the boxes with fewer stars stored, the value computed for a box is the value of the dynamic
program. -/
private theorem boxValue_eq {T : List ℤ} {pre : List (List ℕ)} {l : List ℕ}
    (h : TrieRep L lo T roots (storedUpTo old i encA encB L m t e pre))
    (hl : l ∈ starBoxes L m t e) : boxValue encA encB T (roots i) e l = dpValueD encA encB e l := by
  cases e with
  | zero => rfl
  | succ e =>
    obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hl
    exact sumAtLastStar_congr hp fun d hd => h.lookup i _ (starBoxes_digits (hset d hd)).2 _
      (storedUpTo_of_lt pre (Nat.lt_succ_self e) (hset d hd))

/-- Inserting boxes with e stars into the trie of the tile: if the array represents the state after
the boxes of pre, then after inserting the boxes of rest it represents the state after
pre ++ rest. -/
theorem fillTrie_rep (hi : roots i ≠ 0) (rest pre : List (List ℕ)) (T : List ℤ)
    (hmem : ∀ l ∈ rest, l ∈ starBoxes L m t e)
    (hrep : TrieRep L lo T roots (storedUpTo old i encA encB L m t e pre)) :
    TrieRep L lo (fillTrie encA encB (roots i) e rest T) roots
      (storedUpTo old i encA encB L m t e (pre ++ rest)) := by
  induction rest generalizing pre T with
  | nil => rwa [List.append_nil]
  | cons l rest ih =>
    have hl : l ∈ starBoxes L m t e := hmem l (by simp)
    have hins := hrep.insert i hi l (starBoxes_digits hl).1 (starBoxes_digits hl).2
      (boxValue encA encB T (roots i) e l)
    rw [boxValue_eq hrep hl, ← storedUpTo_snoc pre hl] at hins
    rw [fillTrie_cons, List.append_cons, boxValue_eq hrep hl]
    exact ih (pre ++ [l]) _ (fun x hx => hmem x (by simp [hx])) hins

end

/-- After k rounds the trie of the tile holds the values of the dynamic program for the boxes with
fewer than k stars, and the older entries are kept. -/
theorem fillUpTo_rep {old : ℕ × List ℕ → Option ℤ} (encA encB : List ℤ) {L lo : ℕ} (m t : ℕ)
    (s : TrieStore) (hs : s.Holds L lo old) (k : ℕ) :
    (tileTrieUpTo encA encB L m t s k).Holds L lo
      (storedUpTo old s.roots.length encA encB L m t k []) := by
  induction k with
  | zero => exact hs.new.mono storedUpTo_zero
  | succ k ih =>
    have hfill := fillTrie_rep (roots := s.new.root) (by rw [s.root_new]; exact hs.length_pos.ne')
      (starBoxes L m t k) [] _ (fun _ hl => hl) ih
    rw [storedUpTo_succ]
    rwa [s.root_new] at hfill

section

variable (L m t : ℕ)

/-- There is one root for each tile. -/
theorem length_roots_allTries (tiles : List TileEnc) :
    (allTries L m t tiles).roots.length = tiles.length := by
  induction tiles using List.reverseRecOn with
  | nil => rfl
  | append_singleton tiles ab ih =>
    rw [allTries_snoc, List.length_append, List.length_singleton, ← ih]
    exact List.length_append

/-- The tries of all tiles hold the values of the dynamic programs of the tiles. -/
theorem allTries_rep (tiles : List TileEnc) :
    (allTries L m t tiles).Holds L 1 (storedAll L m t tiles) := by
  induction tiles using List.reverseRecOn with
  | nil => exact (TrieRep.empty L [0] (by simp)).mono fun x v hx => by simp [storedAll] at hx
  | append_singleton tiles ab ih =>
    have h := fillUpTo_rep ab.encA ab.encB m t _ ih (m - t + 1)
    rw [length_roots_allTries] at h
    rw [allTries_snoc]
    exact h.mono (storedAll_snoc tiles ab)

variable {L m t} {tiles : List TileEnc} {i : ℕ}

/-- Looking up a box of tile number i. -/
theorem lookup_allTries {ab : TileEnc} (hi : tiles[i]? = some ab) {l : List ℕ}
    (hl : IsBoxDigits L m t l) : (allTries L m t tiles).lookup i l = storedD ab.encA ab.encB l :=
  (allTries_rep L m t tiles).lookup i l (starBoxes_digits hl).2 _ (storedAll_of_mem hi hl)

/-- **Lemma 29**, and the third component of the data structure: "for every tile, the values of all
its boxes".  The trie of tile number i, which is given by the encodings of its two input arrays a
and b, holds for every box its value. -/
theorem lookup_allTries_eq_val (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (hi : tiles[i]? = some ⟨arrT (encodingL a), arrT (encodingR b)⟩) {π : Cube L}
    (hπ : π ∈ boxes L m t) : (allTries L m t tiles).lookup i (digitsC π) = Cube.val a b π := by
  rw [lookup_allTries hi ((isBoxDigits_digitsC m t π).mpr hπ), storedD, dpValueD_digitsC,
    ← card_starLevels, dpValue_card_starLevels a b hπ]

end

/-! ## Space -/

section

variable (encA encB : List ℤ)

/-- Inserting boxes "adds at most L vertices per box". -/
theorem length_fillTrie_le (root e L : ℕ) (boxes : List (List ℕ))
    (hb : ∀ l ∈ boxes, l.length = L) (T : List ℤ) :
    (fillTrie encA encB root e boxes T).length ≤ T.length + 11 * L * boxes.length := by
  induction boxes generalizing T with
  | nil => exact le_rfl
  | cons l boxes ih =>
    have hrest := ih (fun x hx => hb x (by simp [hx]))
      (trieInsert T root l (boxValue encA encB T root e l))
    have hins := length_trieInsert_le T root l (boxValue encA encB T root e l)
    rw [hb l (by simp)] at hins
    rw [fillTrie_cons, List.length_cons, Nat.mul_add_one]
    omega

variable (L m t : ℕ)

/-- The boxes with fewer than k stars take at most 11 L n cells, where n is their number. -/
theorem length_fillUpTo_le_sum (root k : ℕ) (T : List ℤ) :
    (fillUpTo encA encB L m t root k T).length
      ≤ T.length + 11 * L * ((List.range k).map fun e => (starBoxes L m t e).length).sum := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [fillUpTo, List.sum_range_succ, Nat.mul_add (11 * L)]
    have hfill := length_fillTrie_le encA encB root k L (starBoxes L m t k)
      (fun l hl => (starBoxes_digits hl).1) (fillUpTo encA encB L m t root k T)
    omega

/-- Lemma 29, space: "O(L) […] space per box"; eleven cells more for the root. -/
theorem length_tileTrie_le (s : TrieStore) :
    (tileTrie encA encB L m t s).cells.length
      ≤ s.cells.length + 11 * (1 + L * (boxes L m t).card) := by
  have h := length_fillUpTo_le_sum encA encB L m t s.cells.length (m - t + 1) (trieNew s.cells)
  rw [sum_length_starBoxes, Nat.mul_assoc, length_trieNew] at h
  exact h.trans (by omega)

/-- All tiles together: cell 0, and for each tile the space of Lemma 29. -/
theorem length_allTries_le (tiles : List TileEnc) :
    (allTries L m t tiles).cells.length
      ≤ 1 + tiles.length * (11 * (1 + L * (boxes L m t).card)) := by
  induction tiles using List.reverseRecOn with
  | nil => simp [allTries]
  | append_singleton tiles ab ih =>
    rw [allTries_snoc]
    refine (length_tileTrie_le _ _ L m t _).trans ?_
    rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

end

/-! ## The list of all tiles -/

section

variable {L : ℕ} (nB : ℕ) (encA encB : ℕ → Leaf L → ℤ)

/-- The tiles in row-major order, each given by the arrays of its two encodings: tile (β, β') has
the number β nB + β'. -/
def tileList : List TileEnc :=
  (List.range nB).flatMap fun β => (List.range nB).map fun β' => ⟨arrT (encA β), arrT (encB β')⟩

/-- There are nB² tiles. -/
theorem length_tileList : (tileList nB encA encB).length = nB * nB :=
  List.length_flatMap_range nB _ fun _ _ => by simp

/-- Tile (β, β') has the number β nB + β'. -/
theorem getElem?_tileList {β β' : ℕ} (hβ : β < nB) (hβ' : β' < nB) :
    (tileList nB encA encB)[β * nB + β']? = some ⟨arrT (encA β), arrT (encB β')⟩ := by
  have hlt : β * nB + β' < (tileList nB encA encB).length :=
    (Nat.mul_add_lt_mul hβ hβ').trans_eq (length_tileList nB encA encB).symm
  rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem _ ⟨[], []⟩ hlt, tileList,
    List.getD_flatMap_range _ (fun _ _ => by simp) hβ hβ', List.getD_map_range _ hβ']

/-- The tiles before the tile (β, β'), in row-major order. -/
def tilesBefore (β β' : ℕ) : List TileEnc :=
  ((List.range β).flatMap fun b => (List.range nB).map fun b' => ⟨arrT (encA b), arrT (encB b')⟩) ++
    (List.range β').map fun b' => ⟨arrT (encA β), arrT (encB b')⟩

/-- No tile stands before the first one. -/
theorem tilesBefore_zero : tilesBefore nB encA encB 0 0 = [] := by
  simp [tilesBefore]

/-- The tiles before the next tile of the row are the tiles before the tile, and the tile. -/
theorem tilesBefore_succ (β β' : ℕ) :
    tilesBefore nB encA encB β (β' + 1)
      = tilesBefore nB encA encB β β' ++ [⟨arrT (encA β), arrT (encB β')⟩] := by
  simp [tilesBefore, List.range_succ]

/-- The end of a row is the beginning of the next one. -/
theorem tilesBefore_row (β : ℕ) :
    tilesBefore nB encA encB β nB = tilesBefore nB encA encB (β + 1) 0 := by
  simp [tilesBefore, List.range_succ, List.flatMap_append]

/-- After the last row all tiles have been taken. -/
theorem tilesBefore_all : tilesBefore nB encA encB nB 0 = tileList nB encA encB := by
  simp [tilesBefore, tileList]

/-- β nB + β' tiles stand before the tile (β, β'). -/
theorem length_tilesBefore (β β' : ℕ) :
    (tilesBefore nB encA encB β β').length = β * nB + β' := by
  simp [tilesBefore, List.length_flatMap]

end

/-! ## What the tries of all tiles give to a query

The query for tile number i gets the root of the trie of this tile. -/

section Query

variable {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
  (hi : tiles[i]? = some ab) {η : OutStr L} (hη : (innerSetO η).card = m)

include ht hi hη

/-- Every box of the query is stored: the walk down the trie is safe. -/
theorem walkOK_allTries {l : List ℕ} (hl : l ∈ boxesOf m t (digitsO η)) :
    WalkOK (allTries L m t tiles).cells ((allTries L m t tiles).root i) l := by
  have hbox := boxesOf_mem_starBoxes m t ht η hη l hl
  exact (allTries_rep L m t tiles).walkOK i l (starBoxes_digits hbox).2 _ (storedAll_of_mem hi hbox)

/-- The numbers that the query adds up, read from the trie, are those of the dynamic program. -/
theorem queryTerms_allTries :
    queryTerms m t ab.encA ab.encB ((allTries L m t tiles).lookup i) (digitsO η)
      = queryTerms m t ab.encA ab.encB (storedD ab.encA ab.encB) (digitsO η) :=
  congrArg _ (List.map_congr_left fun l hl =>
    lookup_allTries hi (boxesOf_mem_starBoxes m t ht η hη l hl))

end Query

/-- **The query on the tries of all tiles** returns the value of the query of the proof of
Theorem 30, which is the entry of the product (`Theorem30.correct`). -/
theorem trieQuery_allTries {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ}
    (encA encB : Leaf L → ℤ) (hi : tiles[i]? = some ⟨arrT encA, arrT encB⟩) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    trieQuery m t (arrT encA) (arrT encB) (allTries L m t tiles).cells
        ((allTries L m t tiles).root i) (digitsO η)
      = queryValue m t encA encB η :=
  (congrArg List.sum (queryTerms_allTries ht hi hη)).trans
    (sum_queryTerms_storedD ht encA encB hη)

end ThreeSumApsp.Spec
