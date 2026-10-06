/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays
public import ThreeSumApsp.Spec.Sec2.Theorem5.SortedSets

/-!
# The pruned recursion on lists

`Pruned` (Section 2.4.2) restated on increasing lists of codes: `prunedList`.  The two encodings are
two lists of `10^L` numbers, and a vertex `τ₁ ⋯ τ_k` is given by the position `base` at which its
part of the encodings begins, that is, by the code of `τ₁ ⋯ τ_k` times `10^{L-k}`.  The result is
the list of the values in the order of the list passed.

* **Correctness** (`prunedList_spec`, `prunedList_root`): by induction on the length `n = L - k` of
  the strings passed, as in the proof of Lemma 10.  A child returns the array `C_λ` of step (3) by
  the induction hypothesis.  Step (4), which puts the output together from restrictions of the
  `C_λ`, is a function of its own, `gather`, with its own lemma (`gather_spec`): the slice at `z_ij`
  comes from `C_{P_ij}`, and the slice at `z₀` is the sum of all ten `C_λ`.
* **Work** (`prunedWork_le`): `callSizes` follows the recursion of `prunedList` and lists the
  lengths of the lists passed to its calls.  These are the sizes of the sets passed to the calls of
  `Pruned` (`callSizes_spec`), and Lemma 10 bounds their total.  The work of a call is its own plus
  that of the children that are called (`prunedWork_succ`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The function -/

/-- Step (4) of `Pruned` on lists.  `l` is the list passed to the call, its strings have length
`n + 1`, and `C t` is the list that the child with digit `t` has returned.  The segment of the
output with first digit `t < 9` (the slice at `z_ij`) is the restriction of `C t`, and the segment
with first digit 9 (the slice at `z₀`) is the sum of the restrictions of all ten `C t`. -/
def gather (n : ℕ) (l : List ℕ) (C : ℕ → List ℤ) : List ℤ :=
  (List.range 9).flatMap (fun t => restrictList (childList n t l) (C t) (sliceList n t l))
    ++ sumLists (sliceList n 9 l).length
      ((List.range 10).map fun t => restrictList (childList n t l) (C t) (sliceList n 9 l))

/-- `Pruned` on lists, steps (1) to (4) of Section 2.4.2: `prunedList EA EB n base l` is the call
that is passed the list `l` of codes of strings of length `n`, at the vertex whose part of the
encodings `EA` and `EB` begins at the position `base`.  A child whose list is empty is not called.
-/
def prunedList (EA EB : List ℤ) : ℕ → ℕ → List ℕ → List ℤ
  | 0, base, l => l.map fun _ => EA.getD base 0 * EB.getD base 0
  | n + 1, base, l => gather n l fun t =>
    if childList n t l = [] then [] else prunedList EA EB n (base + t * 10 ^ n) (childList n t l)

/-! ## The ten terms, in the order of their digits -/

/-- The numbers below 10 are the digits of the terms. -/
private theorem range_ten_eq_map :
    List.range 10
      = (List.finRange 10).map fun k => ((termIdx (termEquiv.symm k) : Fin 10) : ℕ) := by
  have hdigit : ∀ k : Fin 10, termIdx (termEquiv.symm k) = k := termEquiv.apply_symm_apply
  simp only [hdigit]
  exact (List.map_coe_finRange_eq_range (n := 10)).symm

/-- All the terms, as a multiset, in the order of their digits. -/
private theorem univ_term_val :
    (Finset.univ : Finset Term).val = ((List.finRange 10).map termEquiv.symm : List Term) := by
  rw [← Finset.map_univ_equiv termEquiv.symm, Finset.map_val]
  rfl

/-- A sum over the terms is a sum over the digits. -/
private theorem sum_term_eq (f : ℕ → ℤ) :
    ∑ lam : Term, f (termIdx lam) = ((List.range 10).map f).sum := by
  rw [List.sum_map_range, ← Fin.sum_univ_eq_sum_range]
  exact termEquiv.sum_comp fun k : Fin 10 => f k

/-- A concatenation over the digits, as a multiset, is a union over the terms. -/
private theorem flatMap_term_eq {α : Type} (F : ℕ → List α) :
    (((List.range 10).flatMap F : List α) : Multiset α)
      = (Finset.univ : Finset Term).val.bind fun lam => (F (termIdx lam) : Multiset α) := by
  rw [range_ten_eq_map, univ_term_val, Multiset.coe_bind, List.flatMap_map, List.flatMap_map]

/-- A digit below 9 is the digit of a term `P_ij` and of the output variable `z_ij`. -/
private theorem exists_P_of_lt_nine {t : ℕ} (h : t < 9) :
    ∃ i j, termOfNat t = .P i j ∧ ((outIdx (.z i j) : Fin 10) : ℕ) = t := by
  have hdigit := termIdx_termOfNat (t := t) (by omega)
  rcases hlam : termOfNat t with ⟨i, j⟩ | _ <;> rw [hlam] at hdigit
  · -- `P_ij` and `z_ij` have the same digit, by definition.
    exact ⟨i, j, rfl, hdigit⟩
  · rw [termIdx_P0] at hdigit
    omega

/-- `codesOf_childSet` read by digits: the list passed to the child with digit `t` is the list of
the set `S_λ` of the term `λ` with that digit. -/
private theorem childList_codesOf {n t : ℕ} (ht : t < 10) (S : Finset (OutStr (n + 1))) :
    childList n t (codesOf S) = codesOf (childSet S (termOfNat t)) := by
  rw [codesOf_childSet, termIdx_termOfNat ht]

/-! ## Step (4): the output from the arrays of the children -/

/-- A function applied along the list of a set, slice by slice: first the slices at the nine `z_ij`,
then the slice at `z₀`. -/
private theorem map_codesOf_succ {n : ℕ} (S : Finset (OutStr (n + 1))) (F : ℕ → ℤ) :
    (codesOf S).map F
      = (List.range 9).flatMap
          (fun z => (sliceList n z (codesOf S)).map fun c => F (z * 10 ^ n + c))
        ++ (sliceList n 9 (codesOf S)).map fun c => F (9 * 10 ^ n + c) := by
  conv_lhs => rw [← flatMap_sliceList S, List.map_flatMap, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]
  simp only [List.map_map, Function.comp_def]

/-- The restriction of the array of the child with digit `t` to a slice contained in its set. -/
private theorem restrictList_child {n : ℕ} (S : Finset (OutStr (n + 1))) (g : Term → OutStr n → ℤ)
    {C : ℕ → List ℤ} (hC : ∀ t < 10, C t = (codesOf (childSet S (termOfNat t))).map fun c =>
      g (termOfNat t) (decodeO n c))
    {t : ℕ} (ht : t < 10) {z : OutVar} (hz : sliceSet S z ⊆ childSet S (termOfNat t)) :
    restrictList (childList n t (codesOf S)) (C t) (sliceList n (outIdx z) (codesOf S))
      = (sliceList n (outIdx z) (codesOf S)).map fun c => g (termOfNat t) (decodeO n c) := by
  rw [hC t ht, ← codesOf_sliceSet, childList_codesOf ht, restrictList_spec _ _ hz]

/-- What step (4) returns.  If the child with digit `t` has returned the list `C t` of the array
`g λ` on `S_λ`, then `gather` returns the list, on `S`, of any array `F` with
`F[z_ij w'] = g P_ij [w']` and `F[z₀ w'] = ∑_λ g λ [w']` for the strings of `S`. -/
theorem gather_spec {n : ℕ} (S : Finset (OutStr (n + 1))) (g : Term → OutStr n → ℤ)
    {C : ℕ → List ℤ} (hC : ∀ t < 10, C t = (codesOf (childSet S (termOfNat t))).map fun c =>
      g (termOfNat t) (decodeO n c))
    (F : OutStr (n + 1) → ℤ)
    (hF : ∀ i j, ∀ w' ∈ sliceSet S (.z i j), F (Fin.cons (.z i j) w') = g (.P i j) w')
    (hF₀ : ∀ w' ∈ sliceSet S .z0, F (Fin.cons .z0 w') = ∑ lam, g lam w') :
    gather n (codesOf S) C = (codesOf S).map fun c => F (decodeO (n + 1) c) := by
  rw [gather, map_codesOf_succ]
  refine congrArg₂ (· ++ ·) (List.flatMap_congr fun t ht => ?_) ?_
  · -- The slice at `z_ij` is the restriction of `C_{P_ij}`.
    obtain ⟨i, j, hlam, rfl⟩ := exists_P_of_lt_nine (List.mem_range.mp ht)
    have hsub : sliceSet S (.z i j) ⊆ childSet S (termOfNat (outIdx (.z i j) : Fin 10)) :=
      hlam ▸ sliceSet_subset_childSet S ((Term.contributes_z_iff _ i j).mpr rfl)
    rw [restrictList_child S g hC (Fin.isLt _) hsub, ← codesOf_sliceSet]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨w', hw', rfl⟩ := (mem_codesOf _ c).mp hc
    rw [decodeO_cons, hF i j w' hw', decodeO_codeO, hlam]
  · -- The slice at `z₀` is the sum of the restrictions of all the `C_λ`.
    have hpick : ∀ t ∈ List.range 10,
        restrictList (childList n t (codesOf S)) (C t) (sliceList n 9 (codesOf S))
          = (sliceList n 9 (codesOf S)).map fun c => g (termOfNat t) (decodeO n c) := fun t ht =>
      restrictList_child S g hC (List.mem_range.mp ht) (z := .z0)
        (sliceSet_subset_childSet S (Term.contributes_z0 _))
    rw [List.map_congr_left hpick, sumLists_map, ← outIdx_z0, ← codesOf_sliceSet]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨w', hw', rfl⟩ := (mem_codesOf _ c).mp hc
    rw [decodeO_cons, hF₀ w' hw', decodeO_codeO, ← sum_term_eq fun t => g (termOfNat t) w']
    simp only [termOfNat_termIdx]

/-! ## Correctness -/

/-- The part of an encoding below the child with digit `t` begins `t · 10^n` places further on. -/
private theorem getD_sliceAt {E : List ℤ} {n base t : ℕ} (ht : t < 10) {enc : Leaf (n + 1) → ℤ}
    (h : ∀ τ, E.getD (base + codeT τ) 0 = enc τ) (τ : Leaf n) :
    E.getD (base + t * 10 ^ n + codeT τ) 0 = sliceAt enc (termOfNat t) τ := by
  rw [sliceAt, ← h, codeT_cons, termIdx_termOfNat ht, Nat.add_assoc]

/-- `prunedList` computes `Pruned`, at any vertex: if the parts of `EA` and `EB` that begin at the
position `base` hold the encodings `encA` and `encB` below the vertex, then on the list of a set `S`
it returns the values of `Pruned(S)` in the order of the list. -/
theorem prunedList_spec (EA EB : List ℤ) {n : ℕ} (base : ℕ) (encA encB : Leaf n → ℤ)
    (hA : ∀ τ, EA.getD (base + codeT τ) 0 = encA τ) (hB : ∀ τ, EB.getD (base + codeT τ) 0 = encB τ)
    (S : Finset (OutStr n)) :
    prunedList EA EB n base (codesOf S)
      = (codesOf S).map fun c => Pruned n encA encB S (decodeO n c) := by
  induction n generalizing base with
  | zero =>
    -- Step (1): at a leaf, the product of the two encoded numbers.  The code of the empty string
    -- is 0, so they stand at the position `base`.
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨w, hw, rfl⟩ := (mem_codesOf S c).mp hc
    have hA₀ : EA.getD base 0 = encA Fin.elim0 := hA Fin.elim0
    have hB₀ : EB.getD base 0 = encB Fin.elim0 := hB Fin.elim0
    rw [decodeO_codeO, hA₀, hB₀]
    exact (if_pos hw).symm
  | succ n ih =>
    -- Step (3): the child with digit `t` returns the array `C_λ`, or is not called.
    have hC : ∀ t < 10, (if childList n t (codesOf S) = [] then []
          else prunedList EA EB n (base + t * 10 ^ n) (childList n t (codesOf S)))
        = (codesOf (childSet S (termOfNat t))).map fun c =>
          Pruned.childResult encA encB S (termOfNat t) (decodeO n c) := by
      intro t ht
      rw [childList_codesOf ht]
      split_ifs with hnil
      · rw [hnil, List.map_nil]
      · have hne : (childSet S (termOfNat t)).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr fun he => hnil ((codesOf_eq_nil _).mpr he)
        rw [ih _ _ _ (getD_sliceAt ht hA) (getD_sliceAt ht hB), Pruned.childResult, if_pos hne]
    -- Step (4): the entry of `Pruned` at `z_ij w'` is `C_{P_ij}[w']`, and at `z₀ w'` it is
    -- `∑_λ C_λ[w']`.
    refine gather_spec S _ hC _ (fun i j w' hw' => ?_) fun w' hw' => ?_
    all_goals
      rw [Pruned_succ, restrictTo, if_pos ((mem_sliceSet _ _ _).mp hw')]
      rfl

/-- `prunedList` at the root: with the lists of the two full encodings and `base = 0`. -/
theorem prunedList_root {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) :
    prunedList (arrT encA) (arrT encB) L 0 (codesOf U)
      = (codesOf U).map fun c => Pruned L encA encB U (decodeO L c) :=
  prunedList_spec _ _ 0 encA encB (fun τ => by rw [Nat.zero_add, getD_arrT])
    (fun τ => by rw [Nat.zero_add, getD_arrT]) U

/-! ## The calls and their work -/

/-- The lengths of the lists passed to all the calls that `prunedList` makes, this one included: the
same recursion as `prunedList`, with the same test for an empty list. -/
def callSizes : ℕ → List ℕ → List ℕ
  | 0, l => [l.length]
  | n + 1, l =>
    l.length :: (List.range 10).flatMap fun t =>
      if childList n t l = [] then [] else callSizes n (childList n t l)

/-- The lengths that `callSizes` lists are the sizes of the sets passed to the calls of `Pruned`. -/
theorem callSizes_spec {n : ℕ} (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) :
    (callSizes n (codesOf S) : Multiset ℕ)
      = (Pruned.calls n encA encB S).map fun c => c.passed.2.card := by
  induction n with
  | zero =>
    simp only [callSizes, Pruned.calls, Pruned.run, length_codesOf]
    rfl
  | succ n ih =>
    rw [callSizes, Pruned.calls_succ, Multiset.map_cons, ← Multiset.cons_coe, length_codesOf,
      flatMap_term_eq, Multiset.map_bind]
    refine congrArg (Multiset.cons _) (Multiset.bind_congr fun lam _ => ?_)
    rw [← codesOf_childSet, Multiset.map_map, Pruned.childCalls]
    -- Seen from the parent, a call of the child `λ` has `λ` before its vertex, and the same set.
    by_cases hne : (childSet S lam).Nonempty
    · rw [if_neg (mt (codesOf_eq_nil _).mp hne.ne_empty), if_pos hne, ih]
      rfl
    · rw [if_pos ((codesOf_eq_nil _).mpr (Finset.not_nonempty_iff_eq_empty.mp hne)), if_neg hne]
      rfl

/-- The total length of the lists passed is the total size of Lemma 10. -/
private theorem sum_callSizes {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) :
    (callSizes L (codesOf U)).sum = Pruned.totalSize encA encB U := by
  rw [Pruned.totalSize, ← callSizes_spec encA encB U, Multiset.sum_coe]

/-- The work of all the calls of `prunedList`, if a call that receives a list of length `s` does
`s + 1` units of work (Section 2.4.4: "each of its steps handles each string of S a constant number
of times"; here a string is one number). -/
def prunedWork (n : ℕ) (l : List ℕ) : ℕ := ((callSizes n l).map fun s => s + 1).sum

/-- The work of a call and of its children. -/
theorem prunedWork_succ (n : ℕ) (l : List ℕ) :
    prunedWork (n + 1) l = (l.length + 1) + ((List.range 10).map fun t =>
      if childList n t l = [] then 0 else prunedWork n (childList n t l)).sum := by
  rw [prunedWork, callSizes, List.map_cons, List.sum_cons, List.map_flatMap, List.flatMap_def,
    List.sum_flatten, List.map_map]
  congr 2
  refine List.map_congr_left fun t _ => ?_
  rw [Function.comp_apply]
  split_ifs <;> rfl

/-- Every call receives a nonempty list, if the first one does. -/
private theorem callSizes_pos : ∀ (n : ℕ) (l : List ℕ), l ≠ [] → ∀ s ∈ callSizes n l, 1 ≤ s
  | 0, l, hl, s, hs => by
    obtain rfl : s = l.length := by simpa [callSizes] using hs
    exact List.length_pos_iff.mpr hl
  | n + 1, l, hl, s, hs => by
    rw [callSizes, List.mem_cons, List.mem_flatMap] at hs
    rcases hs with rfl | ⟨t, -, hs⟩
    · exact List.length_pos_iff.mpr hl
    · split_ifs at hs with hnil
      · exact absurd hs List.not_mem_nil
      · exact callSizes_pos n _ hnil s hs

/-- Section 2.4.4: "By Lemma 10, the total number of operations per leaf of Leaves(W_T) is thus
O(L²)"; with one number for each string it is `O(L)`: the work of `Pruned(U)` is at most
`2 (L + 1) |Leaves(U)|`. -/
theorem prunedWork_le {L : ℕ} (U : Finset (OutStr L)) (hU : U.Nonempty) :
    prunedWork L (codesOf U) ≤ 2 * ((L + 1) * (Leaves U).card) := by
  -- The work is the total length of the lists plus the number of calls, and no list is empty.
  have hwork : prunedWork L (codesOf U)
      = (callSizes L (codesOf U)).sum + (callSizes L (codesOf U)).length := by
    simp [prunedWork, List.sum_map_add]
  have hcalls := List.length_le_sum_of_one_le _
    (callSizes_pos L (codesOf U) (mt (codesOf_eq_nil U).mp hU.ne_empty))
  -- Lemma 10, with any two arrays on the leaves: the calls do not depend on the numbers.
  have hsize := Lemma10.total_size (fun _ => 0) (fun _ => 0) U
  rw [← sum_callSizes] at hsize
  omega

end ThreeSumApsp.Spec
