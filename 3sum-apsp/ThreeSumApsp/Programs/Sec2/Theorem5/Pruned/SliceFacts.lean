/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize

/-!
# The pruned recursion: the pure side

What the program for Pruned (Section 2.4.2) needs to know about its model Spec.prunedList, which
works on increasing lists of codes.  A code is an output string read as a number with the digits 0
to 9: the digits 0 to 8 stand for the variables z_ij and the digit 9 for z₀.  The slice at the digit
z is sliceList n z l, the codes of l with first digit z, without that digit.

* The value that belongs to a code does not depend on the list in which the code is passed
  (`prunedValue`, `prunedList_eq_map`).
* The lists passed to the children are increasing lists of codes again, and the lengths add up
  (`segStart_ten`).
* Step (4): the result is made of the slices of the children's results (`prunedList_succ`).
* Step (2): the list of a child is the merge of the slice at the output variable of its term
  (`firstList`, empty for the term P₀) and the slice at z₀ (`childList_eq_mergeUnion`).
* The running time `prunedTime` follows the recursion of the program; it is built from the times of
  a round (`roundTime`) and of steps (3) and (4) (`childTime`).  It is at most a constant times
  prunedWork, one unit for each call and for each code passed to a call (`prunedTime_le`).  One
  round is `roundTime_le`, and the ten rounds are added up by `sum_helper_lengths`.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-- The value of Pruned at the output string with code c, at the vertex whose part of the encodings
begins at position base: the sum of the products at the leaves that contribute to the string. -/
def prunedValue (EA EB : List ℤ) (n base c : ℕ) : ℤ :=
  ∑ τ : Leaf n with Leaf.Contributes τ (decodeO n c),
    EA.getD (base + codeT τ) 0 * EB.getD (base + codeT τ) 0

/-- prunedList lists the values of the codes that are passed to it. -/
theorem prunedList_eq_map (EA EB : List ℤ) (n base : ℕ) {l : List ℕ} (hl : l.Pairwise (· < ·))
    (hlt : ∀ c ∈ l, c < 10 ^ n) :
    prunedList EA EB n base l = l.map (prunedValue EA EB n base) := by
  obtain ⟨S, rfl⟩ := exists_codesOf l hl hlt
  rw [prunedList_spec EA EB base (fun τ => EA.getD (base + codeT τ) 0)
    (fun τ => EB.getD (base + codeT τ) 0) (fun _ => rfl) (fun _ => rfl) S]
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨w, hw, rfl⟩ := (mem_codesOf S _).mp hc
  rw [Pruned_eq_restrictTo_sum, restrictTo, decodeO_codeO, if_pos hw, prunedValue, decodeO_codeO]

/-- prunedList returns one value for each code. -/
theorem length_prunedList (EA EB : List ℤ) (n base : ℕ) {l : List ℕ} (hl : l.Pairwise (· < ·))
    (hlt : ∀ c ∈ l, c < 10 ^ n) :
    (prunedList EA EB n base l).length = l.length := by
  rw [prunedList_eq_map EA EB n base hl hlt, List.length_map]

/-- Section 2.4.4: "every value computed by Pruned is a sum of at most 10^L products of two encoded
numbers". -/
theorem abs_prunedValue_le {EA EB : List ℤ} {A B : ℤ} (hA : ∀ e ∈ EA, |e| ≤ A)
    (hB : ∀ e ∈ EB, |e| ≤ B) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (n base c : ℕ) :
    |prunedValue EA EB n base c| ≤ 10 ^ n * (A * B) := by
  have h := abs_Pruned_le (fun τ : Leaf n => EA.getD (base + codeT τ) 0)
    (fun τ => EB.getD (base + codeT τ) 0) A B (fun τ => AbsLe.abs_getD_le hA0 hA _)
    (fun τ => AbsLe.abs_getD_le hB0 hB _) {decodeO n c} (decodeO n c)
  rwa [Pruned_eq_restrictTo_sum, restrictTo, if_pos (Finset.mem_singleton_self _)] at h

section Children

variable {n : ℕ} {l : List ℕ} (hl : l.Pairwise (· < ·))
include hl

/-- A code without its first digit has n digits. -/
theorem lt_of_mem_sliceList {z c : ℕ} (hc : c ∈ sliceList n z l) : c < 10 ^ n :=
  ((mem_sliceList hl).mp hc).1

/-- The list of a child increases. -/
theorem pairwise_childList (t : ℕ) : (childList n t l).Pairwise (· < ·) := by
  rw [childList]
  split_ifs
  · exact pairwise_sliceList hl
  · exact pairwise_mergeUnion (pairwise_sliceList hl) (pairwise_sliceList hl)

/-- The codes of the list of a child have n digits. -/
theorem lt_of_mem_childList (t : ℕ) : ∀ c ∈ childList n t l, c < 10 ^ n := by
  intro c hc
  rw [childList] at hc
  split_ifs at hc
  · exact lt_of_mem_sliceList hl hc
  · rcases mem_mergeUnion.mp hc with h | h <;> exact lt_of_mem_sliceList hl h

omit hl in
/-- The slice at the output variable of the term t is part of the list of the child t. -/
theorem sliceList_subset_childList (t : ℕ) : ∀ c ∈ sliceList n t l, c ∈ childList n t l := by
  intro c hc
  rw [childList]
  split_ifs with h
  · rwa [h] at hc
  · exact mem_mergeUnion.mpr (Or.inl hc)

omit hl in
/-- The slice at z₀ is part of the list of every child. -/
theorem sliceList_nine_subset_childList (t : ℕ) : ∀ c ∈ sliceList n 9 l, c ∈ childList n t l := by
  intro c hc
  rw [childList]
  split_ifs
  · exact hc
  · exact mem_mergeUnion.mpr (Or.inr hc)

end Children

/-! ## Positions of the segments -/

/-- The slice at z + 1 begins where the slice at z ends. -/
theorem segStart_succ (n : ℕ) (l : List ℕ) (z : ℕ) :
    segStart n l (z + 1) = segStart n l z + (sliceList n z l).length := by
  simp [segStart, List.range_succ]

/-- The ten slices make up the list. -/
theorem segStart_ten {n : ℕ} {l : List ℕ} (hl : l.Pairwise (· < ·))
    (hlt : ∀ c ∈ l, c < 10 ^ (n + 1)) : segStart n l 10 = l.length := by
  obtain ⟨S, rfl⟩ := exists_codesOf l hl hlt
  exact sum_length_sliceList S

/-- The slices stand in the order of their first digits. -/
theorem segStart_mono (n : ℕ) (l : List ℕ) {y z : ℕ} (h : y ≤ z) :
    segStart n l y ≤ segStart n l z :=
  List.sum_map_range_mono _ h

/-! ## The model, one level unfolded -/

/-- The sum of the values of the code c at the first k children. -/
def pvSum (EA EB : List ℤ) (n base k c : ℕ) : ℤ :=
  ((List.range k).map fun t => prunedValue EA EB n (base + t * 10 ^ n) c).sum

/-- One more child. -/
theorem pvSum_succ (EA EB : List ℤ) (n base k c : ℕ) :
    pvSum EA EB n base (k + 1) c = pvSum EA EB n base k c + prunedValue EA EB n (base + k * 10 ^ n)
        c := by
  simp [pvSum, List.range_succ]

/-- What the child t returns, also if it is not called. -/
theorem childValues_eq_map (EA EB : List ℤ) (n base t : ℕ) {l : List ℕ} (hl : l.Pairwise (· < ·)) :
    (if childList n t l = [] then [] else prunedList EA EB n (base + t * 10 ^ n) (childList n t l))
      = (childList n t l).map (prunedValue EA EB n (base + t * 10 ^ n)) := by
  split_ifs with h
  · rw [h]
    rfl
  · exact prunedList_eq_map EA EB n _ (pairwise_childList hl t) (lt_of_mem_childList hl t)

/-- Step (4): the result is the nine slices at the variables z_ij, each with the values of its own
child, followed by the slice at z₀ with the sums over the ten children. -/
theorem prunedList_succ (EA EB : List ℤ) (n base : ℕ) {l : List ℕ} (hl : l.Pairwise (· < ·)) :
    prunedList EA EB (n + 1) base l
      = (List.range 9).flatMap
          (fun t => (sliceList n t l).map (prunedValue EA EB n (base + t * 10 ^ n)))
        ++ (sliceList n 9 l).map (pvSum EA EB n base 10) := by
  rw [prunedList, gather]
  simp only [childValues_eq_map EA EB n base _ hl]
  have hslice : ∀ t, restrictList (childList n t l)
        ((childList n t l).map (prunedValue EA EB n (base + t * 10 ^ n))) (sliceList n t l)
      = (sliceList n t l).map (prunedValue EA EB n (base + t * 10 ^ n)) := fun t =>
    restrictList_map _ (pairwise_childList hl t) (pairwise_sliceList hl)
      (sliceList_subset_childList t)
  have hlast : ∀ t, restrictList (childList n t l)
        ((childList n t l).map (prunedValue EA EB n (base + t * 10 ^ n))) (sliceList n 9 l)
      = (sliceList n 9 l).map (prunedValue EA EB n (base + t * 10 ^ n)) := fun t =>
    restrictList_map _ (pairwise_childList hl t) (pairwise_sliceList hl)
      (sliceList_nine_subset_childList t)
  simp only [hslice, hlast]
  rw [sumLists_map]
  rfl

/-- A concatenation lies in the memory if its pieces do, each at the sum of the lengths of the
earlier ones. -/
theorem Seg.flatMap_range {μ : ℕ → ℤ} {a : ℕ} (f : ℕ → List ℤ) (k : ℕ)
    (h : ∀ t < k, Seg μ (a + ((List.range t).map fun s => (f s).length).sum) (f t)) :
    Seg μ a ((List.range k).flatMap f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, seg_append]
    refine ⟨ih fun t ht => h t (by omega), ?_⟩
    simpa [List.length_flatMap] using h k (by omega)

/-! ## The lists of a round -/

section

variable {n t : ℕ} {codes : List ℕ}

/-- The first of the two lists that are merged for the child t: the slice at the output variable of
the term t, and nothing for the term P₀, which is number 9. -/
def firstList (n t : ℕ) (codes : List ℕ) : List ℕ := if t < 9 then sliceList n t codes else []

/-- Step (2): "S_{P_ij} := S_{z_ij} ∪ S_{z₀} and S_{P₀} := S_{z₀}". -/
theorem childList_eq_mergeUnion (n : ℕ) (codes : List ℕ) (ht : t < 10) :
    childList n t codes = mergeUnion (firstList n t codes) (sliceList n 9 codes) := by
  by_cases h9 : t < 9
  · rw [childList, if_neg (by omega), firstList, if_pos h9]
  · obtain rfl : t = 9 := by omega
    rw [childList, if_pos rfl, firstList, if_neg h9, mergeUnion]

/-- The first list increases. -/
theorem pairwise_firstList (h : codes.Pairwise (· < ·)) :
    (firstList n t codes).Pairwise (· < ·) := by
  unfold firstList
  split_ifs
  · exact pairwise_sliceList h
  · exact List.Pairwise.nil

/-- The first list is part of the list of the child. -/
theorem firstList_subset_childList : ∀ x ∈ firstList n t codes, x ∈ childList n t codes := by
  unfold firstList
  split_ifs
  · exact sliceList_subset_childList t
  · simp

/-- The first list ends before the slice at z₀ begins. -/
theorem segStart_add_firstList_le (n : ℕ) (codes : List ℕ) (ht : t < 10) :
    segStart n codes t + (firstList n t codes).length ≤ segStart n codes 9 := by
  by_cases h9 : t < 9
  · rw [firstList, if_pos h9, ← segStart_succ]
    exact segStart_mono n codes (by omega)
  · obtain rfl : t = 9 := by omega
    simp [firstList]

/-- The list of a child is no longer than the two lists that are merged. -/
theorem length_childList_le (n : ℕ) (codes : List ℕ) (ht : t < 10) :
    (childList n t codes).length ≤ (firstList n t codes).length + (sliceList n 9 codes).length :=
  childList_eq_mergeUnion n codes ht ▸ length_mergeUnion_le _ _

end

/-! ## The running time -/

/-- The running time of steps (3) and (4) for the term t; T is the time of the recursive call as a
function of its list, and h is the constant of the helper procedures. -/
def childTime (h : ℕ) (T : List ℕ → ℕ) (n t : ℕ) (l : List ℕ) : ℕ :=
  46 + T (childList n t l) + h * ((firstList n t l).length + (childList n t l).length + 1)
    + h * ((sliceList n 9 l).length + (childList n t l).length + 1)

/-- The running time of round number t of the loop over the ten terms. -/
def roundTime (h : ℕ) (T : List ℕ → ℕ) (n t : ℕ) (l : List ℕ) : ℕ :=
  50 + h * ((firstList n t l).length + (sliceList n 9 l).length + 1)
    + (if childList n t l = [] then 0 else childTime h T n t l)

/-- The running time of the program, by the recursion of the program: before the loop segBounds and
fill are called, and each of the ten rounds begins with the test of the loop. -/
def prunedTime (h : ℕ) : ℕ → List ℕ → ℕ
  | 0, l => 20 + h * (l.length + 1)
  | n + 1, l =>
    70 + h * (l.length + 11) + h * ((sliceList n 9 l).length + 1)
      + ((List.range 10).map fun t => 4 + roundTime h (prunedTime h n) n t l).sum

/-- A sum of terms a + h f(t) + C w(t), taken apart. -/
theorem sum_map_add_mul_add_mul (ts : List ℕ) (a h C : ℕ) (f w : ℕ → ℕ) :
    (ts.map fun t => a + h * f t + C * w t).sum
      = ts.length * a + h * (ts.map f).sum + C * (ts.map w).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- The first lists of the ten rounds are the slices before the slice at z₀. -/
theorem sum_length_firstList (n : ℕ) (l : List ℕ) :
    ((List.range 10).map fun t => (firstList n t l).length).sum = segStart n l 9 := by
  have hfirst : (List.range 9).map (fun t => (firstList n t l).length)
      = (List.range 9).map fun t => (sliceList n t l).length :=
    List.map_congr_left fun t ht => by rw [firstList, if_pos (List.mem_range.mp ht)]
  rw [List.range_succ, List.map_append, List.sum_append, segStart, hfirst]
  simp [firstList]

/-- The time of round t with the test of the loop, if the recursive call stays within C times its
work: the helpers read and write lists whose lengths are at most the lengths of the two slices. -/
theorem roundTime_le (h C n t : ℕ) (l : List ℕ) (ht : t < 10)
    (hchild : prunedTime h n (childList n t l) ≤ C * prunedWork n (childList n t l)) :
    4 + roundTime h (prunedTime h n) n t l
      ≤ 100 + h * (4 * (firstList n t l).length + 4 * (sliceList n 9 l).length + 3)
        + C * (if childList n t l = [] then 0 else prunedWork n (childList n t l)) := by
  have hlen := length_childList_le n l ht
  unfold roundTime childTime
  split_ifs
  · have hhelpers : h * ((firstList n t l).length + (sliceList n 9 l).length + 1)
        ≤ h * (4 * (firstList n t l).length + 4 * (sliceList n 9 l).length + 3) :=
      Nat.mul_le_mul_left h (by omega)
    omega
  · have hhelpers : h * ((firstList n t l).length + (sliceList n 9 l).length + 1)
          + h * ((firstList n t l).length + (childList n t l).length + 1)
          + h * ((sliceList n 9 l).length + (childList n t l).length + 1)
        ≤ h * (4 * (firstList n t l).length + 4 * (sliceList n 9 l).length + 3) := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      exact Nat.mul_le_mul_left h (by omega)
    omega

/-- The lengths that the helpers handle in the ten rounds, added up. -/
theorem sum_helper_lengths (n : ℕ) (l : List ℕ) :
    ((List.range 10).map fun t =>
        4 * (firstList n t l).length + 4 * (sliceList n 9 l).length + 3).sum
      = 4 * segStart n l 9 + 40 * (sliceList n 9 l).length + 30 := by
  have hsum := sum_map_add_mul_add_mul (List.range 10) (4 * (sliceList n 9 l).length + 3) 4 0
    (fun t => (firstList n t l).length) (fun _ => 0)
  simp only [Nat.zero_mul, Nat.add_zero, List.length_range, sum_length_firstList] at hsum
  have hterms : ((List.range 10).map fun t =>
        4 * (firstList n t l).length + 4 * (sliceList n 9 l).length + 3)
      = (List.range 10).map fun t =>
        4 * (sliceList n 9 l).length + 3 + 4 * (firstList n t l).length :=
    List.map_congr_left fun t _ => by ring
  rw [hterms, hsum]
  ring

/-- The program takes at most 50 h + 2000 steps for each call and for each code passed to a
call. -/
theorem prunedTime_le (h n : ℕ) : ∀ {l : List ℕ}, l.Pairwise (· < ·) → (∀ c ∈ l, c < 10 ^ n) →
    prunedTime h n l ≤ (50 * h + 2000) * prunedWork n l := by
  induction n with
  | zero =>
    intro l _ _
    have hexpand : (50 * h + 2000) * (l.length + 1)
        = 50 * (h * (l.length + 1)) + 2000 * (l.length + 1) := by ring
    simp only [prunedTime, prunedWork, callSizes, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  | succ n ih =>
    intro l hl hlt
    -- The ten rounds, added up.
    have hrounds := List.sum_le_sum fun t (ht : t ∈ List.range 10) =>
      roundTime_le h (50 * h + 2000) n t l (List.mem_range.mp ht)
        (ih (pairwise_childList hl t) (lt_of_mem_childList hl t))
    rw [sum_map_add_mul_add_mul (List.range 10) 100 h (50 * h + 2000)
      (fun t => 4 * (firstList n t l).length + 4 * (sliceList n 9 l).length + 3),
      sum_helper_lengths, List.length_range] at hrounds
    have hnine : segStart n l 9 + (sliceList n 9 l).length = l.length := by
      rw [← segStart_succ]
      exact segStart_ten hl hlt
    rw [prunedTime, prunedWork_succ]
    generalize ((List.range 10).map fun t =>
      if childList n t l = [] then 0 else prunedWork n (childList n t l)).sum = W at hrounds ⊢
    -- All lengths are at most the length of the list.
    have hhelpers : h * (l.length + 11) + h * ((sliceList n 9 l).length + 1)
          + h * (4 * segStart n l 9 + 40 * (sliceList n 9 l).length + 30)
        ≤ h * (50 * (l.length + 1)) := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      exact Nat.mul_le_mul_left h (by omega)
    have hexpand : (50 * h + 2000) * (l.length + 1 + W)
        = h * (50 * (l.length + 1)) + 2000 * (l.length + 1) + (50 * h + 2000) * W := by ring
    omega

end Light.Sec2
