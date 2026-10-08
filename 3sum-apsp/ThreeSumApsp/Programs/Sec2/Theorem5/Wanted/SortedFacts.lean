/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5

/-!
# After the sort: the codes of a tile are a segment (pure)

Section 2.4.4: "locate the output strings, and sort the sets W_T".  The wanted positions are (I i, J
i) for i < w.  Routine wanted gives each of them the number of its tile and the code of its output
string; routine sortWanted gives a permutation π of the numbers 0, …, w - 1 that sorts them by tile
and, within a tile, by code, and the table START of the numbers of positions in earlier tiles.  This
file shows what the rest of the program uses: the codes of tile number z stand, in the order of π,
in the places START[z], …, START[z+1] - 1; they are the strictly increasing list Spec.codesOf W_T;
and the value that the pruned recursion finds at such a place is the wanted entry of X Y.  No
program occurs here.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## A list that is sorted by a key -/

namespace Sorted

/-- A list sorted by t is the entries with t < z followed by the others. -/
theorem eq_filter_append (t : ℕ → ℕ) (z : ℕ) : ∀ (l : List ℕ), (l.Pairwise fun a b => t a ≤ t b) →
    l = (l.filter fun a => t a < z) ++ l.filter fun a => ¬ t a < z
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    by_cases ha : t a < z
    · rw [List.filter_cons_of_pos (by simpa using ha), List.filter_cons_of_neg (by simpa using ha),
        List.cons_append, ← eq_filter_append t z l htail]
    · have hall : ∀ b ∈ l, ¬ t b < z := fun b hb => by have := hhead b hb; omega
      rw [List.filter_cons_of_neg (by simpa using ha), List.filter_cons_of_pos (by simpa using ha),
        List.filter_eq_nil_iff.mpr (fun b hb => by simpa using hall b hb),
        List.filter_eq_self.mpr (fun b hb => by simpa using hall b hb), List.nil_append]

/-- In a list sorted by t, the entries with t = z are a segment. -/
theorem segment_eq_filter (t : ℕ → ℕ) (z : ℕ) (l : List ℕ) (h : l.Pairwise fun a b => t a ≤ t b) :
    (l.drop (l.filter fun a => t a < z).length).take
        ((l.filter fun a => t a < z + 1).length - (l.filter fun a => t a < z).length)
      = l.filter fun a => t a = z := by
  have hbelow := eq_filter_append t z l h
  have hsorted : (l.filter fun a => ¬ t a < z).Pairwise fun a b => t a ≤ t b :=
    h.sublist List.filter_sublist
  have hrest := eq_filter_append t (z + 1) _ hsorted
  have hequal : ((l.filter fun a => ¬ t a < z).filter fun a => t a < z + 1)
      = l.filter fun a => t a = z := by
    rw [List.filter_filter]
    refine List.filter_congr fun a _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [hequal] at hrest
  rw [List.length_filter_lt_succ, Nat.add_sub_cancel_left]
  have key : ∀ A E G : List ℕ, ((A ++ (E ++ G)).drop A.length).take E.length = E := by
    intro A E G
    rw [List.drop_left, List.take_left]
  have hl : l = (l.filter fun a => t a < z) ++ ((l.filter fun a => t a = z) ++
      (l.filter fun a => ¬ t a < z).filter fun a => ¬ t a < z + 1) := by
    rw [← hrest]
    exact hbelow
  have hmiddle := key (l.filter fun a => t a < z) (l.filter fun a => t a = z)
    ((l.filter fun a => ¬ t a < z).filter fun a => ¬ t a < z + 1)
  rw [← hl] at hmiddle
  exact hmiddle

end Sorted

/-! ## The setting -/

/-- The number of the tile of position number i. -/
def tileNo (p : Par) (I J : ℕ → ℕ) (i : ℕ) : ℕ := I i / (p.K0 * p.N0) * p.nB + J i / (p.K0 * p.N0)

/-- The code of the output string of position number i. -/
def codeNo (p : Par) (I J : ℕ → ℕ) (i : ℕ) : ℕ := outCodeOfPos p.L p.m (I i) (J i)

/-- START[z]: the number of positions in tiles with a number below z. -/
def startNo (p : Par) (w : ℕ) (I J : ℕ → ℕ) (z : ℕ) : ℕ :=
  ((List.range w).filter fun i => tileNo p I J i < z).length

/-- The codes in the places START[z], …, START[z+1] - 1 of the sorted order. -/
def tileCodes (p : Par) (w : ℕ) (I J : ℕ → ℕ) (π : List ℕ) (z : ℕ) : List ℕ :=
  ((π.drop (startNo p w I J z)).take (startNo p w I J (z + 1) - startNo p w I J z)).map
    (codeNo p I J)

/-- The set W of the wanted positions. -/
def wantedSet (N w : ℕ) (I J : ℕ → ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => ∃ i < w, I i = q.1 ∧ J i = q.2

/-- What is known after wanted and sortWanted: w different positions, and a permutation that sorts
them by tile and code. -/
structure SortedPre (p : Par) (w : ℕ) (I J : ℕ → ℕ) (π : List ℕ) : Prop where
  hmL : p.m ≤ p.L
  hI : ∀ i < w, I i < p.N
  hJ : ∀ i < w, J i < p.N
  inj : ∀ i < w, ∀ j < w, I i = I j → J i = J j → i = j
  perm : π.Perm (List.range w)
  sorted : (π.map fun i => tileNo p I J i * 10 ^ p.L + codeNo p I J i).Pairwise (· ≤ ·)

variable {p : Par} {w : ℕ} {I J : ℕ → ℕ} {π : List ℕ}

/-- The number of a tile is below nT. -/
theorem tileNo_lt_nT (hmL : p.m ≤ p.L) {i : ℕ} (hI : I i < p.N) (hJ : J i < p.N) :
    tileNo p I J i < p.nT :=
  Nat.mul_add_lt_mul (bandOf_lt_numBands hmL p.N _ hI) (bandOf_lt_numBands hmL p.N _ hJ)

/-- A code is below 10^L. -/
theorem codeNo_lt_pow (hmL : p.m ≤ p.L) (i : ℕ) : codeNo p I J i < 10 ^ p.L := by
  rw [codeNo, ← codeO_outStrOfPos hmL]
  exact codeO_lt _

/-- No position lies in a tile with a number below 0. -/
theorem startNo_zero (p : Par) (w : ℕ) (I J : ℕ → ℕ) : startNo p w I J 0 = 0 := by
  simp [startNo]

/-- START[z + 1] counts the positions of tile z as well. -/
theorem startNo_succ (p : Par) (w : ℕ) (I J : ℕ → ℕ) (z : ℕ) :
    startNo p w I J (z + 1)
      = startNo p w I J z + ((List.range w).filter fun i => tileNo p I J i = z).length :=
  List.length_filter_lt_succ _ z _

/-- The table START increases. -/
theorem startNo_mono (p : Par) (w : ℕ) (I J : ℕ → ℕ) (z : ℕ) :
    startNo p w I J z ≤ startNo p w I J (z + 1) := by
  rw [startNo_succ]
  omega

namespace SortedPre

/-! ## Tiles and codes -/

/-- The number of a band is below nB. -/
theorem band_lt (h : SortedPre p w I J π) {x : ℕ} (hx : x < p.N) : x / (p.K0 * p.N0) < p.nB :=
  bandOf_lt_numBands h.hmL p.N x hx

/-- The number of a tile is below nT. -/
theorem tileNo_lt (h : SortedPre p w I J π) {i : ℕ} (hi : i < w) : tileNo p I J i < p.nT :=
  tileNo_lt_nT h.hmL (h.hI i hi) (h.hJ i hi)

/-- The code of a position is the code of its output string. -/
theorem decodeO_codeNo (h : SortedPre p w I J π) (i : ℕ) :
    decodeO p.L (codeNo p I J i) = outStrOfPos (stdLayout h.hmL) (I i) (J i) := by
  rw [codeNo, ← codeO_outStrOfPos h.hmL, decodeO_codeO]

/-- A code is below 10^L. -/
theorem codeNo_lt (h : SortedPre p w I J π) (i : ℕ) : codeNo p I J i < 10 ^ p.L :=
  codeNo_lt_pow h.hmL i

/-- Two positions of the same tile with the same code have the same number. -/
theorem index_eq (h : SortedPre p w I J π) {i j : ℕ} (hi : i < w) (hj : j < w)
    (ht : tileNo p I J i = tileNo p I J j)
    (hc : codeNo p I J i = codeNo p I J j) : i = j := by
  obtain ⟨hbandI, hbandJ⟩ :=
    Nat.mul_add_inj_of_lt (h.band_lt (h.hJ i hi)) (h.band_lt (h.hJ j hj)) ht
  have hstring : outStrOfPos (stdLayout h.hmL) (I i) (J i)
      = outStrOfPos (stdLayout h.hmL) (I j) (J j) := by
    rw [← h.decodeO_codeNo, ← h.decodeO_codeNo, hc]
  obtain ⟨hrow, hcol⟩ := outStrOfPos_injective (stdLayout h.hmL) _ _ _ _ hbandI hbandJ hstring
  exact h.inj i hi j hj hrow hcol

/-- π lists the numbers below w. -/
theorem mem_iff (h : SortedPre p w I J π) {i : ℕ} : i ∈ π ↔ i < w := by
  rw [h.perm.mem_iff, List.mem_range]

/-- π has w entries. -/
theorem length_eq (h : SortedPre p w I J π) : π.length = w := by
  rw [h.perm.length_eq, List.length_range]

/-- No number occurs twice in π. -/
theorem nodup (h : SortedPre p w I J π) : π.Nodup := h.perm.symm.nodup List.nodup_range

/-- π is sorted by tile. -/
theorem sorted_tile (h : SortedPre p w I J π) :
    π.Pairwise fun a b => tileNo p I J a ≤ tileNo p I J b := by
  refine (List.pairwise_map.mp h.sorted).imp fun {a b} hab => ?_
  by_contra hlt
  have htiles : (tileNo p I J b + 1) * 10 ^ p.L ≤ tileNo p I J a * 10 ^ p.L :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at htiles
  have hcode := h.codeNo_lt b
  omega

/-- START[z] is also the number of entries of π in tiles with a number below z. -/
theorem length_filter_lt (h : SortedPre p w I J π) (z : ℕ) :
    (π.filter fun i => tileNo p I J i < z).length = startNo p w I J z :=
  (h.perm.filter _).length_eq

/-- The numbers of the positions of tile z, in the sorted order, are a segment of π. -/
theorem segment (h : SortedPre p w I J π) (z : ℕ) :
    (π.drop (startNo p w I J z)).take (startNo p w I J (z + 1) - startNo p w I J z)
      = π.filter fun i => tileNo p I J i = z := by
  rw [← h.length_filter_lt, ← h.length_filter_lt]
  exact Sorted.segment_eq_filter _ z π h.sorted_tile

/-- The codes of tile z are the codes of the entries of π in tile z. -/
theorem tileCodes_eq (h : SortedPre p w I J π) (z : ℕ) :
    tileCodes p w I J π z = (π.filter fun i => tileNo p I J i = z).map (codeNo p I J) := by
  rw [tileCodes, h.segment]

/-- The codes of tile z are the codes of the positions in tile z. -/
theorem mem_tileCodes (h : SortedPre p w I J π) {z c : ℕ} :
    c ∈ tileCodes p w I J π z ↔ ∃ i < w, tileNo p I J i = z ∧ codeNo p I J i = c := by
  simp only [h.tileCodes_eq, List.mem_map, List.mem_filter, h.mem_iff, decide_eq_true_eq]
  exact ⟨fun ⟨i, ⟨hi, ht⟩, hc⟩ => ⟨i, hi, ht, hc⟩, fun ⟨i, hi, ht, hc⟩ => ⟨i, ⟨hi, ht⟩, hc⟩⟩

/-! ## The table START -/

/-- All w positions lie in tiles with a number below nT. -/
theorem startNo_last (h : SortedPre p w I J π) : startNo p w I J p.nT = w := by
  rw [startNo, List.filter_eq_self.mpr, List.length_range]
  intro i hi
  simpa using h.tileNo_lt (List.mem_range.mp hi)

/-! ## The codes of a tile -/

/-- Tile z has START[z + 1] - START[z] codes. -/
theorem length_tileCodes (h : SortedPre p w I J π) (z : ℕ) :
    (tileCodes p w I J π z).length = startNo p w I J (z + 1) - startNo p w I J z := by
  rw [h.tileCodes_eq, List.length_map, startNo_succ, Nat.add_sub_cancel_left]
  exact (h.perm.filter _).length_eq

/-- The codes of a tile are below 10^L. -/
theorem tileCodes_lt (h : SortedPre p w I J π) (z : ℕ) :
    ∀ x ∈ tileCodes p w I J π z, x < 10 ^ p.L := by
  intro x hx
  obtain ⟨i, -, -, rfl⟩ := h.mem_tileCodes.mp hx
  exact h.codeNo_lt i

/-- The codes of a tile are strictly increasing. -/
theorem tileCodes_sorted (h : SortedPre p w I J π) (z : ℕ) :
    (tileCodes p w I J π z).Pairwise (· < ·) := by
  rw [h.tileCodes_eq, List.pairwise_map]
  have hpairs : (π.filter fun i => tileNo p I J i = z).Pairwise fun a b =>
      tileNo p I J a * 10 ^ p.L + codeNo p I J a ≤ tileNo p I J b * 10 ^ p.L + codeNo p I J b
        ∧ a ≠ b :=
    ((List.pairwise_map.mp h.sorted).and h.nodup).sublist List.filter_sublist
  refine hpairs.imp_of_mem fun {a b} ha hb hab => ?_
  obtain ⟨haπ, haz⟩ := List.mem_filter.mp ha
  obtain ⟨hbπ, hbz⟩ := List.mem_filter.mp hb
  have htileA : tileNo p I J a = z := by simpa using haz
  have htileB : tileNo p I J b = z := by simpa using hbz
  obtain ⟨hle, hne⟩ := hab
  rw [htileA, htileB] at hle
  have hne' : codeNo p I J a ≠ codeNo p I J b := fun hc =>
    hne (h.index_eq (h.mem_iff.mp haπ) (h.mem_iff.mp hbπ) (htileA.trans htileB.symm) hc)
  omega

/-- The codes of the tile (β, β') are the increasing list of the codes of the set W_T. -/
theorem tileCodes_eq_codesOf (h : SortedPre p w I J π) {β β' : ℕ} (hβ' : β' < p.nB) :
    tileCodes p w I J π (β * p.nB + β')
      = codesOf (wantedStrings (stdLayout h.hmL) (wantedSet p.N w I J) β β') := by
  refine (h.tileCodes_sorted _).eq_of_mem_iff (pairwise_codesOf _) fun c => ?_
  rw [h.mem_tileCodes, mem_codesOf]
  simp only [wantedStrings, Finset.mem_image, Finset.mem_filter, wantedSet, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi, ht, rfl⟩
    obtain ⟨hbandI, hbandJ⟩ := Nat.mul_add_inj_of_lt (h.band_lt (h.hJ i hi)) hβ' ht
    refine ⟨_, ⟨(⟨I i, h.hI i hi⟩, ⟨J i, h.hJ i hi⟩), ⟨⟨i, hi, rfl, rfl⟩, hbandI, hbandJ⟩, rfl⟩, ?_⟩
    exact codeO_outStrOfPos h.hmL (I i) (J i)
  · rintro ⟨s, ⟨⟨I', J'⟩, ⟨⟨i, hi, hrow, hcol⟩, hbandI, hbandJ⟩, rfl⟩, rfl⟩
    simp only at hrow hcol hbandI hbandJ
    refine ⟨i, hi, ?_, ?_⟩
    · rw [tileNo, hrow, hcol]
      change bandOf p.L p.m I' * p.nB + bandOf p.L p.m J' = _
      rw [hbandI, hbandJ]
    · rw [codeNo, hrow, hcol]
      exact (codeO_outStrOfPos h.hmL I' J').symm

/-- The place START[z] + k of the sorted order holds the position whose code is the k-th code of
tile z. -/
theorem getElem_tileCodes (h : SortedPre p w I J π) (z : ℕ) {k : ℕ}
    (hk : k < (tileCodes p w I J π z).length) :
    ∃ hlt : startNo p w I J z + k < π.length,
      (tileCodes p w I J π z)[k] = codeNo p I J π[startNo p w I J z + k] ∧
        tileNo p I J π[startNo p w I J z + k] = z := by
  have hk' : k < ((π.drop (startNo p w I J z)).take
      (startNo p w I J (z + 1) - startNo p w I J z)).length := by
    simpa [tileCodes] using hk
  have hlt : startNo p w I J z + k < π.length := by
    rw [List.length_take, List.length_drop] at hk'
    omega
  have hentry : ((π.drop (startNo p w I J z)).take (startNo p w I J (z + 1) - startNo p w I J z))[k]
      = π[startNo p w I J z + k] := by
    rw [List.getElem_take, List.getElem_drop]
  refine ⟨hlt, ?_, ?_⟩
  · simp only [tileCodes, List.getElem_map, hentry]
  · have hmem : π[startNo p w I J z + k] ∈ π.filter fun i => tileNo p I J i = z := by
      rw [← h.segment, ← hentry]
      exact List.getElem_mem _
    simpa using (List.mem_filter.mp hmem).2

/-! ## The value -/

/-- The value that the pruned recursion on the tile (β, β') finds at the k-th code of the tile is
the entry of X Y at the position whose number stands at the place START[z] + k of the sorted order,
where z = β nB + β' is the number of the tile (β, β'). -/
theorem tile_value (h : SortedPre p w I J π) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) {β β' : ℕ} (hβ' : β' < p.nB) {k i : ℕ}
    (hk : k < (tileCodes p w I J π (β * p.nB + β')).length)
    (hi : π[startNo p w I J (β * p.nB + β') + k]? = some i) (hiw : i < w) :
    (prunedList (arrT (encodingL (bandArrayL (stdLayout h.hmL) X β)))
        (arrT (encodingR (bandArrayR (stdLayout h.hmL) Y β'))) p.L 0
        (tileCodes p w I J π (β * p.nB + β'))).getD k 0
      = (X * Y) ⟨I i, h.hI i hiw⟩ ⟨J i, h.hJ i hiw⟩ := by
  obtain ⟨hlt, hcode, htile⟩ := h.getElem_tileCodes _ hk
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hi
  rw [hi] at hcode htile
  obtain ⟨hbandI, hbandJ⟩ := Nat.mul_add_inj_of_lt (h.band_lt (h.hJ i hiw)) hβ' htile
  have hW : ((⟨I i, h.hI i hiw⟩, ⟨J i, h.hJ i hiw⟩) : Fin p.N × Fin p.N) ∈ wantedSet p.N w I J := by
    simp only [wantedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hiw, rfl, rfl⟩
  have hvalue := Theorem5.correctness (stdLayout h.hmL) X Y (wantedSet p.N w I J) ⟨I i, h.hI i hiw⟩
    ⟨J i, h.hJ i hiw⟩ hW
  have hbandI' : bandOf p.L p.m (I i) = β := hbandI
  have hbandJ' : bandOf p.L p.m (J i) = β' := hbandJ
  simp only [hbandI', hbandJ'] at hvalue
  have hk' : k < (codesOf (wantedStrings (stdLayout h.hmL) (wantedSet p.N w I J) β β')).length := by
    rw [← h.tileCodes_eq_codesOf hβ']
    exact hk
  have hcode' : (codesOf (wantedStrings (stdLayout h.hmL) (wantedSet p.N w I J) β β'))[k]
      = codeNo p I J i := by
    rw [← hcode]
    congr 1
    exact (h.tileCodes_eq_codesOf hβ').symm
  rw [h.tileCodes_eq_codesOf hβ', prunedList_root, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some, hcode', h.decodeO_codeNo]
  exact hvalue

/-- The pruned recursion on a tile returns one value for each code. -/
theorem length_prunedList (h : SortedPre p w I J π) (EA EB : Leaf p.L → ℤ) {β β' : ℕ}
    (hβ' : β' < p.nB) :
    (prunedList (arrT EA) (arrT EB) p.L 0 (tileCodes p w I J π (β * p.nB + β'))).length
      = (tileCodes p w I J π (β * p.nB + β')).length := by
  rw [h.tileCodes_eq_codesOf hβ', prunedList_root, List.length_map]

/-- Every place of the sorted order lies in the segment of one tile. -/
theorem exists_place (h : SortedPre p w I J π) {i : ℕ} (hi : i < w) :
    ∃ β < p.nB, ∃ β' < p.nB, ∃ k < (tileCodes p w I J π (β * p.nB + β')).length,
      i = startNo p w I J (β * p.nB + β') + k := by
  -- START increases from 0 to w, so i lies between two consecutive entries.
  have key : ∀ n, i < startNo p w I J n →
      ∃ z < n, startNo p w I J z ≤ i ∧ i < startNo p w I J (z + 1) := by
    intro n
    induction n with
    | zero =>
      intro hzero
      rw [startNo_zero] at hzero
      omega
    | succ n ih =>
      intro hlt
      by_cases hearlier : i < startNo p w I J n
      · obtain ⟨z, hz, hz'⟩ := ih hearlier
        exact ⟨z, by omega, hz'⟩
      · exact ⟨n, by omega, by omega, hlt⟩
  obtain ⟨z, hz, hfrom, hto⟩ := key p.nT (by rw [h.startNo_last]; exact hi)
  have hz' : z < p.nB * p.nB := hz
  have hnB : 0 < p.nB := by
    rcases Nat.eq_zero_or_pos p.nB with hzero | hzero
    · rw [hzero] at hz'
      omega
    · exact hzero
  have hdec : z / p.nB * p.nB + z % p.nB = z := Nat.div_add_mod' z p.nB
  refine ⟨z / p.nB, Nat.div_lt_of_lt_mul hz', z % p.nB, Nat.mod_lt _ hnB, i - startNo p w I J z, ?_,
    ?_⟩
  · rw [hdec, h.length_tileCodes]
    omega
  · rw [hdec]
    omega

end SortedPre

end Light.Sec2
