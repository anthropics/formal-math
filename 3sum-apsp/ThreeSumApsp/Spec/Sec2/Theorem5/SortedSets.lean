/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Spec.Sec2.Theorem5.Alphabets
public import Mathlib.Data.List.TakeWhile

/-!
# Sets of output strings as increasing lists of codes

Section 2.4.4: "we store the sets as sorted lists, so that a slice is a segment and a union of
slices is a merge".  A set `S` of output strings is stored as the strictly increasing list `codesOf
S` of its codes.  The operations of `Pruned` (Section 2.4.2) on sets become operations on lists.
None of them uses a division; a first digit is removed by a subtraction.

* The slice `S_z` is the segment `sliceList n z` of the list with first digit `z`
  (`codesOf_sliceSet`), and the list is the concatenation of its ten segments, with the first digits
  put back (`flatMap_sliceList`).
* A union is a merge, `mergeUnion` (`codesOf_union`).
* The set `S_λ` passed to the child `λ` in step (2) is `childList` (`codesOf_childSet`).
* The restriction of an array on a set to a subset is one pass, `restrictList`
  (`restrictList_spec`).

Two increasing lists are equal if they have the same elements (`List.Pairwise.eq_of_mem_iff`): the
facts on slices and on unions are proved by describing the elements of both sides.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The list of a set -/

/-- A set of output strings as the strictly increasing list of its codes. -/
def codesOf {n : ℕ} (S : Finset (OutStr n)) : List ℕ := (S.image codeO).sort (· ≤ ·)

section
variable {n : ℕ} (S : Finset (OutStr n))

/-- The list of codes is strictly increasing. -/
theorem pairwise_codesOf : (codesOf S).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

/-- The elements of the list are the codes of the strings of the set. -/
theorem mem_codesOf (c : ℕ) : c ∈ codesOf S ↔ ∃ w ∈ S, codeO w = c := by
  simp [codesOf]

/-- Cardinalities are lengths. -/
theorem length_codesOf : (codesOf S).length = S.card := by
  rw [codesOf, Finset.length_sort, Finset.card_image_of_injective _ (codeO_injective n)]

/-- The codes are below `10^n`. -/
private theorem codesOf_lt : ∀ c ∈ codesOf S, c < 10 ^ n := by
  intro c hc
  obtain ⟨w, -, rfl⟩ := (mem_codesOf S c).mp hc
  exact codeO_lt w

/-- The list is empty exactly if the set is. -/
theorem codesOf_eq_nil : codesOf S = [] ↔ S = ∅ := by
  rw [← List.length_eq_zero_iff, length_codesOf, Finset.card_eq_zero]

end

/-- An increasing list of numbers below `10^n` is the list of codes of a set. -/
theorem exists_codesOf {n : ℕ} (l : List ℕ) (hl : l.Pairwise (· < ·)) (hlt : ∀ c ∈ l, c < 10 ^ n) :
    ∃ S : Finset (OutStr n), codesOf S = l := by
  refine ⟨l.toFinset.image (decodeO n), (pairwise_codesOf _).eq_of_mem_iff hl fun c => ?_⟩
  simp only [mem_codesOf, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨w, ⟨c', hc', rfl⟩, rfl⟩
    rwa [codeO_decodeO (hlt c' hc')]
  · exact fun hc => ⟨decodeO n c, ⟨c, hc, rfl⟩, codeO_decodeO (hlt c hc)⟩

/-! ## Slices are segments -/

/-- The numbers `c` with `a ≤ c < b` of an increasing list: skip the numbers below `a`, then take
the numbers below `b`. -/
def between (a b : ℕ) (l : List ℕ) : List ℕ :=
  (l.dropWhile fun c => c < a).takeWhile fun c => c < b

/-- The segment of an increasing list of codes with first digit `z`: the codes from `z · 10^n` on
that are below `(z+1) · 10^n`, with the first digit removed by a subtraction. -/
def sliceList (n z : ℕ) (l : List ℕ) : List ℕ :=
  (between (z * 10 ^ n) ((z + 1) * 10 ^ n) l).map fun c => c - z * 10 ^ n

/-- For an increasing list `l`, the elements of `between a b l` are the numbers `c` of `l` with
`a ≤ c < b`. -/
private theorem mem_between {a b c : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) :
    c ∈ between a b l ↔ c ∈ l ∧ a ≤ c ∧ c < b := by
  rw [between, List.mem_takeWhile_lt (h.sublist (List.dropWhile_sublist _)),
    List.mem_dropWhile_lt h,
    and_assoc]

/-- The numbers between two bounds of an increasing list form an increasing list. -/
private theorem pairwise_between {l : List ℕ} (h : l.Pairwise (· < ·)) (a b : ℕ) :
    (between a b l).Pairwise (· < ·) :=
  (h.sublist (List.dropWhile_sublist _)).sublist (List.takeWhile_sublist _)

/-- A number belongs to the segment with first digit `z` of an increasing list exactly if it is
below `10^n` and, with the digit `z` before it, belongs to the list. -/
theorem mem_sliceList {n z c : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) :
    c ∈ sliceList n z l ↔ c < 10 ^ n ∧ z * 10 ^ n + c ∈ l := by
  simp only [sliceList, List.mem_map, mem_between h, Nat.succ_mul]
  constructor
  · rintro ⟨c', ⟨hc', hle, hlt⟩, rfl⟩
    exact ⟨by omega, by rwa [Nat.add_sub_cancel' hle]⟩
  · exact fun ⟨hlt, hmem⟩ => ⟨_, ⟨hmem, by omega, by omega⟩, by omega⟩

/-- A segment is strictly increasing. -/
theorem pairwise_sliceList {n z : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) :
    (sliceList n z l).Pairwise (· < ·) := by
  rw [sliceList, List.pairwise_map]
  refine (pairwise_between h _ _).imp_of_mem fun {a b} ha _ hab => ?_
  have hle := ((mem_between h).mp ha).2.1
  omega

/-- A segment of an increasing list, with the first digit put back, is the part of the list from
`z 10^n` up to, but not including, `(z + 1) 10^n`. -/
private theorem map_sliceList {n z : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) :
    ((sliceList n z l).map fun c => z * 10 ^ n + c)
      = between (z * 10 ^ n) ((z + 1) * 10 ^ n) l := by
  rw [sliceList, List.map_map]
  refine (List.map_congr_left fun c hc => ?_).trans (List.map_id _)
  exact Nat.add_sub_cancel' ((mem_between h).mp hc).2.1

/-- The first `k` segments, with the first digits put back, are the codes below `k · 10^n`. -/
theorem flatMap_sliceList_eq_takeWhile {n : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) (k : ℕ) :
    (List.range k).flatMap (fun z => (sliceList n z l).map fun c => z * 10 ^ n + c)
      = l.takeWhile fun c => c < k * 10 ^ n := by
  induction k with
  | zero => cases l <;> simp
  | succ k ih =>
    -- Split `l` at `k · 10^n`.  The first part lies below `(k+1) · 10^n`, so it is taken whole;
    -- what is taken of the rest is segment number `k`.
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, map_sliceList h, between]
    conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun c => c < k * 10 ^ n) (l := l)]
    rw [List.takeWhile_append_of_pos]
    intro a ha
    have hlt := List.mem_takeWhile_imp ha
    simp only [decide_eq_true_eq, Nat.succ_mul] at hlt ⊢
    exact Nat.lt_add_right _ hlt

/-- A slice of a set is a segment of the list. -/
theorem codesOf_sliceSet {n : ℕ} (S : Finset (OutStr (n + 1))) (z : OutVar) :
    codesOf (sliceSet S z) = sliceList n (outIdx z) (codesOf S) := by
  refine (pairwise_codesOf _).eq_of_mem_iff (pairwise_sliceList (pairwise_codesOf _)) fun c => ?_
  rw [mem_sliceList (pairwise_codesOf _), mem_codesOf, mem_codesOf]
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨codeO_lt w', _, (mem_sliceSet S z w').mp hw', codeO_cons z w'⟩
  · rintro ⟨hc, w, hw, hwc⟩
    have hcons : w = Fin.cons z (decodeO n c) := by
      apply codeO_injective
      rw [hwc, codeO_cons, codeO_decodeO hc]
    exact ⟨decodeO n c, (mem_sliceSet S z _).mpr (hcons ▸ hw), codeO_decodeO hc⟩

/-- The list is the concatenation of its ten segments (with the first digits put back). -/
theorem flatMap_sliceList {n : ℕ} (S : Finset (OutStr (n + 1))) :
    (List.range 10).flatMap (fun z => (sliceList n z (codesOf S)).map fun c => z * 10 ^ n + c)
      = codesOf S := by
  rw [flatMap_sliceList_eq_takeWhile (pairwise_codesOf S), List.takeWhile_eq_self_iff]
  intro c hc
  simpa only [decide_eq_true_eq, pow_succ'] using codesOf_lt S c hc

/-- The lengths of the ten segments add up to the length of the list. -/
theorem sum_length_sliceList {n : ℕ} (S : Finset (OutStr (n + 1))) :
    ((List.range 10).map fun z => (sliceList n z (codesOf S)).length).sum = (codesOf S).length := by
  conv_rhs => rw [← flatMap_sliceList S]
  simp [List.length_flatMap]

/-! ## Unions are merges -/

/-- The union of two strictly increasing lists, by merging; a number in both lists is kept once. -/
def mergeUnion : List ℕ → List ℕ → List ℕ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs =>
    if a < b then a :: mergeUnion as (b :: bs)
    else if b < a then b :: mergeUnion (a :: as) bs
    else a :: mergeUnion as bs

/-- A number belongs to a merge exactly if it belongs to one of the two lists. -/
theorem mem_mergeUnion {c : ℕ} {l l' : List ℕ} : c ∈ mergeUnion l l' ↔ c ∈ l ∨ c ∈ l' := by
  -- Along the recursion of `mergeUnion`.  If neither head is smaller, they are equal: nothing is
  -- lost.
  fun_induction mergeUnion l l' <;> grind

/-- A number below all elements of two lists is below all elements of their merge. -/
private theorem lt_of_mem_mergeUnion {x : ℕ} {l l' : List ℕ} (hl : ∀ c ∈ l, x < c)
    (hl' : ∀ c ∈ l', x < c) (c : ℕ) (hc : c ∈ mergeUnion l l') : x < c :=
  (mem_mergeUnion.mp hc).elim (hl c) (hl' c)

/-- The merge of two strictly increasing lists is strictly increasing. -/
theorem pairwise_mergeUnion : ∀ {l l' : List ℕ}, l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (mergeUnion l l').Pairwise (· < ·)
  | [], l', _, h' => by simpa [mergeUnion] using h'
  | a :: as, [], h, _ => by simpa [mergeUnion] using h
  | a :: as, b :: bs, h, h' => by
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp h
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp h'
    rw [mergeUnion]
    split_ifs with hab hba
    · -- `a` comes first: it is below `as`, below `b`, and so below `bs`.
      exact List.pairwise_cons.mpr ⟨lt_of_mem_mergeUnion ha
        (List.forall_mem_cons.mpr ⟨hab, fun c hc => hab.trans (hb c hc)⟩),
        pairwise_mergeUnion has h'⟩
    · -- `b` comes first: it is below `a`, so below `as`, and below `bs`.
      exact List.pairwise_cons.mpr ⟨lt_of_mem_mergeUnion
        (List.forall_mem_cons.mpr ⟨hba, fun c hc => hba.trans (ha c hc)⟩) hb,
        pairwise_mergeUnion h hbs⟩
    · -- `a = b` is kept once.
      obtain rfl : a = b := by omega
      exact List.pairwise_cons.mpr ⟨lt_of_mem_mergeUnion ha hb, pairwise_mergeUnion has hbs⟩

/-- A union of sets is a merge of the lists. -/
theorem codesOf_union {n : ℕ} (S T : Finset (OutStr n)) :
    codesOf (S ∪ T) = mergeUnion (codesOf S) (codesOf T) := by
  refine (pairwise_codesOf _).eq_of_mem_iff
    (pairwise_mergeUnion (pairwise_codesOf _) (pairwise_codesOf _)) fun c => ?_
  simp only [mem_mergeUnion, mem_codesOf, Finset.mem_union, or_and_right, exists_or]

/-- A merge is not longer than the two lists together. -/
theorem length_mergeUnion_le (l l' : List ℕ) : (mergeUnion l l').length ≤ l.length + l'.length := by
  -- Each step of `mergeUnion` puts out one number and removes at least one.
  fun_induction mergeUnion l l' <;> grind

/-- Step (2) of `Pruned` on lists: the set passed to the child with digit `t`.  The digit 9 is that
of `P₀` and of `z₀`: the child `P₀` gets the slice at `z₀`, and the child `P_ij` the union of the
slices at `z_ij` and at `z₀`. -/
def childList (n t : ℕ) (l : List ℕ) : List ℕ :=
  if t = 9 then sliceList n 9 l else mergeUnion (sliceList n t l) (sliceList n 9 l)

/-- The list of the set `S_λ` of step (2) of `Pruned`. -/
theorem codesOf_childSet {n : ℕ} (S : Finset (OutStr (n + 1))) (lam : Term) :
    codesOf (childSet S lam) = childList n (termIdx lam) (codesOf S) := by
  rcases lam with ⟨i, j⟩ | _
  · have hne : ((termIdx (.P i j) : Fin 10) : ℕ) ≠ 9 := by rw [termIdx_P]; omega
    -- `P_ij` and `z_ij` have the same digit, and `z₀` has the digit 9.
    rw [childList, if_neg hne, childSet_P, codesOf_union, codesOf_sliceSet, codesOf_sliceSet,
      outIdx_z, outIdx_z0, termIdx_P]
  · rw [childList, if_pos termIdx_P0, childSet_P0, codesOf_sliceSet, outIdx_z0]

/-! ## Restriction to a subset is one pass -/

/-- Restriction of an array on a set to a subset, on lists: `big` is the increasing list of the set,
`vals` the list of the values in the same order, `small` the increasing list of the subset.  One
pass. -/
def restrictList : List ℕ → List ℤ → List ℕ → List ℤ
  | b :: bs, v :: vs, s :: ss =>
    if b = s then v :: restrictList bs vs ss else restrictList bs vs (s :: ss)
  | _, _, _ => []

/-- On strictly increasing lists, the second contained in the first: from the values of `f` along
`big`, `restrictList` returns the values of `f` along `small`. -/
theorem restrictList_map (f : ℕ → ℤ) : ∀ {big small : List ℕ}, big.Pairwise (· < ·) →
    small.Pairwise (· < ·) → (∀ c ∈ small, c ∈ big) →
    restrictList big (big.map f) small = small.map f
  | [], [], _, _, _ => by simp [restrictList]
  | [], s :: ss, _, _, h => by simpa using h s (List.mem_cons_self ..)
  | b :: bs, [], _, _, _ => by simp [restrictList]
  | b :: bs, s :: ss, hbig, hsmall, h => by
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hbig
    obtain ⟨hs, hss⟩ := List.pairwise_cons.mp hsmall
    rw [List.map_cons, restrictList]
    split_ifs with heq
    · -- `b = s` is picked; the rest of `small` is above `b`, so it lies in `bs`.
      subst heq
      rw [List.map_cons, restrictList_map f hbs hss fun c hc =>
        (List.mem_cons.mp (h c (List.mem_cons_of_mem _ hc))).resolve_left (hs c hc).ne']
    · -- `b` is skipped; `s` lies in `bs`, so all of `small` is above `b` and lies in `bs`.
      have hlt : b < s :=
        hb s ((List.mem_cons.mp (h s (List.mem_cons_self ..))).resolve_left (Ne.symm heq))
      refine restrictList_map f hbs hsmall fun c hc => (List.mem_cons.mp (h c hc)).resolve_left ?_
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hlt.ne'
      · exact (hlt.trans (hs c hc)).ne'

/-- `restrictList` picks the values at the subset. -/
theorem restrictList_spec {n : ℕ} (S T : Finset (OutStr n)) (hTS : T ⊆ S) (f : ℕ → ℤ) :
    restrictList (codesOf S) ((codesOf S).map f) (codesOf T) = (codesOf T).map f := by
  refine restrictList_map f (pairwise_codesOf S) (pairwise_codesOf T) fun c hc => ?_
  obtain ⟨w, hw, rfl⟩ := (mem_codesOf T c).mp hc
  exact (mem_codesOf S _).mpr ⟨w, hTS hw, rfl⟩

end ThreeSumApsp.Spec
