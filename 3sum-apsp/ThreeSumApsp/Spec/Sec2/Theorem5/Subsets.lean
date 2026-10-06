/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Data.Bool.Count
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The subsets of size `m` of `{1, …, L}`, enumerated

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  A subset is a *mask*: the list of `L` truth values saying
which levels belong to it, level 1 first (`maskSet`, `maskOf`).  The subsets of size `m` are
enumerated with those containing level 1 first, and so on recursively: `unrank L m r` is number `r`
in this order.

* The masks `unrank L m r` with `r < (L choose m)` have length `L` and `m` entries `true`, and they
  are distinct, because `rank` recovers `r` (`length_unrank`, `count_unrank`, `rank_unrank`).  So
  their sets of levels are distinct subsets of size `m` (`card_maskSet_unrank`,
  `eq_of_maskSet_unrank_eq`).
* A program lists them in a table without arithmetic, each mask from the one before it: the first
  mask is `true^m false^{L-m}` (`unrank_zero`), and two consecutive masks are
  `pre true false false^a true^b` and `pre false true true^b false^a` (`unrank_succ_shape`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The enumeration -/

/-- The mask number `r` (counted from 0) among the masks of length `L` with `m` entries `true`. -/
def unrank : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | L + 1, 0, _ => false :: unrank L 0 0
  | L + 1, m + 1, r =>
    if r < L.choose m then true :: unrank L m r else false :: unrank L (m + 1) (r - L.choose m)

/-- The position of a mask in the enumeration.  A mask that begins with `false` comes after all the
masks with the same number of entries `true` that begin with `true`; if the rest `l` of the mask has
`k > 0` entries `true`, there are `(|l| choose k - 1)` of them. -/
private def rank : List Bool → ℕ
  | [] => 0
  | true :: l => rank l
  | false :: l => (if l.count true = 0 then 0 else l.length.choose (l.count true - 1)) + rank l

/-- A mask of the enumeration has length `L`. -/
@[simp] theorem length_unrank (L m r : ℕ) : (unrank L m r).length = L := by
  fun_induction unrank L m r <;> simp [*]

/-- A mask of the enumeration has `m` entries `true`. -/
theorem count_unrank {L m r : ℕ} (hr : r < L.choose m) : (unrank L m r).count true = m := by
  -- Along the recursion of `unrank`; by Pascal's rule the number passed on is again in range.
  fun_induction unrank L m r <;> grind [Nat.choose_succ_succ']

/-- A mask of the enumeration has `L - m` entries `false`. -/
theorem count_false_unrank {L m r : ℕ} (hr : r < L.choose m) :
    (unrank L m r).count false = L - m := by
  have hall := List.count_not_add_count (unrank L m r) true
  rw [count_unrank hr, length_unrank, Bool.not_true] at hall
  omega

/-- `rank` undoes `unrank`. -/
private theorem rank_unrank {L m r : ℕ} (hr : r < L.choose m) : rank (unrank L m r) = r := by
  fun_induction unrank L m r with
  | case1 m r =>
    -- No levels: the only mask is the empty one, and `r = 0`.
    cases m <;> simp_all [rank]
  | case2 L r ih =>
    -- The empty set: the only mask has no entry `true`, and `r = 0`.
    simp_all [rank, count_unrank]
  | case3 L m r h ih =>
    -- Level 1 belongs to the set.
    simpa [rank] using ih h
  | case4 L m r h ih =>
    -- Level 1 does not belong to the set: the `(L choose m)` masks with level 1 come before.
    rw [Nat.choose_succ_succ'] at hr
    have hrest : r - L.choose m < L.choose (m + 1) := by omega
    simp only [rank, count_unrank hrest, length_unrank, ih hrest, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    omega

/-- Different numbers give different masks. -/
private theorem eq_of_unrank_eq {L m r r' : ℕ} (hr : r < L.choose m) (hr' : r' < L.choose m)
    (h : unrank L m r = unrank L m r') : r = r' := by
  rw [← rank_unrank hr, ← rank_unrank hr', h]

/-! ## Masks and sets of levels -/

/-- The set of levels of a mask. -/
def maskSet (L : ℕ) (mask : List Bool) : Finset (Fin L) :=
  Finset.univ.filter fun ℓ => mask.getD ℓ false

/-- The mask of a set of levels. -/
def maskOf {L : ℕ} (Q : Finset (Fin L)) : List Bool := List.ofFn fun ℓ => decide (ℓ ∈ Q)

/-- The mask of a set of levels has one entry for each level. -/
theorem length_maskOf {L : ℕ} (Q : Finset (Fin L)) : (maskOf Q).length = L := by
  simp [maskOf]

/-- The entry of the mask at a level says whether the level belongs to the set. -/
theorem getD_maskOf {L n : ℕ} (Q : Finset (Fin L)) (hn : n < L) :
    (maskOf Q).getD n false = decide ((⟨n, hn⟩ : Fin L) ∈ Q) := by
  simp [maskOf, hn]

/-- The number of levels of a mask is the number of its entries `true`. -/
private theorem card_maskSet {L : ℕ} (mask : List Bool) (h : mask.length = L) :
    (maskSet L mask).card = mask.count true := by
  induction mask generalizing L with
  | nil =>
    subst h
    simp [maskSet]
  | cons x l ih =>
    -- Split off level 1.
    subst h
    have hrest := ih rfl
    unfold maskSet at hrest ⊢
    rw [List.length_cons, Fin.card_filter_univ_succ]
    cases x <;> simpa using hrest

/-- The set of levels of a mask of the enumeration has `m` elements. -/
theorem card_maskSet_unrank {L m r : ℕ} (hr : r < L.choose m) :
    (maskSet L (unrank L m r)).card = m := by
  rw [card_maskSet _ (length_unrank L m r), count_unrank hr]

/-- The mask of the set of levels of a mask of length `L` is that mask. -/
theorem maskOf_maskSet {L : ℕ} (mask : List Bool) (h : mask.length = L) :
    maskOf (maskSet L mask) = mask := by
  subst h
  refine List.ext_getElem (by simp [maskOf]) fun i _ _ => ?_
  simp [maskOf, maskSet]

/-- Different numbers give different sets of levels. -/
theorem eq_of_maskSet_unrank_eq {L m r r' : ℕ} (hr : r < L.choose m) (hr' : r' < L.choose m)
    (h : maskSet L (unrank L m r) = maskSet L (unrank L m r')) : r = r' := by
  refine eq_of_unrank_eq hr hr' ?_
  rw [← maskOf_maskSet _ (length_unrank L m r), h, maskOf_maskSet _ (length_unrank L m r')]

/-! ## From one mask to the next -/

/-- The first mask: `m` times `true`, then `L - m` times `false`. -/
theorem unrank_zero {L m : ℕ} (hm : m ≤ L) :
    unrank L m 0 = List.replicate m true ++ List.replicate (L - m) false := by
  induction L generalizing m with
  | zero => simp [unrank, Nat.le_zero.mp hm]
  | succ L ih =>
    cases m with
    | zero => simpa [unrank, List.replicate_succ] using ih (Nat.zero_le L)
    | succ m =>
      have hm' : m ≤ L := Nat.le_of_succ_le_succ hm
      simp [unrank, Nat.choose_pos hm', ih hm', List.replicate_succ]

/-- The last mask: `L - m` times `false`, then `m` times `true`. -/
private theorem unrank_last {L m : ℕ} (hm : m ≤ L) :
    unrank L m (L.choose m - 1) = List.replicate (L - m) false ++ List.replicate m true := by
  induction L generalizing m with
  | zero => simp [unrank, Nat.le_zero.mp hm]
  | succ L ih =>
    cases m with
    | zero => simpa [unrank, List.replicate_succ] using ih (Nat.zero_le L)
    | succ m =>
      rcases Nat.lt_or_ge m L with hlt | hge
      · have hpos : 0 < L.choose (m + 1) := Nat.choose_pos hlt
        have hnot : ¬ (L + 1).choose (m + 1) - 1 < L.choose m := by
          rw [Nat.choose_succ_succ']
          omega
        have hrank : (L + 1).choose (m + 1) - 1 - L.choose m = L.choose (m + 1) - 1 := by
          rw [Nat.choose_succ_succ']
          omega
        rw [unrank, if_neg hnot, hrank, ih hlt, show L + 1 - (m + 1) = L - (m + 1) + 1 by omega]
        -- `replicate (a + 1) false` is `false :: replicate a false`.
        rfl
      · obtain rfl : m = L := by omega
        simpa [unrank, List.replicate_succ] using ih le_rfl

/-- Two consecutive masks of the enumeration: write the first one as
`pre ++ [true, false] ++ false^a ++ true^b`, with the last occurrence of `true, false`; then the
next one is `pre ++ [false, true] ++ true^b ++ false^a`. -/
theorem unrank_succ_shape {L m r : ℕ} (hr : r + 1 < L.choose m) :
    ∃ (pre : List Bool) (a b : ℕ), L = pre.length + 2 + a + b ∧
      unrank L m r = pre ++ true :: false :: (List.replicate a false ++ List.replicate b true) ∧
      unrank L m (r + 1)
        = pre ++ false :: true :: (List.replicate b true ++ List.replicate a false) := by
  induction L generalizing m r with
  | zero => cases m <;> simp at hr
  | succ L ih =>
    cases m with
    | zero => simp at hr
    | succ m =>
      rw [Nat.choose_succ_succ'] at hr
      rcases Nat.lt_trichotomy (r + 1) (L.choose m) with hboth | hlast | hneither
      · -- Both masks contain the first level.
        obtain ⟨pre, a, b, hlen, hthis, hnext⟩ := ih hboth
        refine ⟨true :: pre, a, b, by rw [List.length_cons]; omega, ?_, ?_⟩
        · rw [unrank, if_pos (by omega), hthis, List.cons_append]
        · rw [unrank, if_pos hboth, hnext, List.cons_append]
      · -- The last mask with the first level, and the first one without it.
        have hmL : m + 1 ≤ L := by
          by_contra hcon
          rw [Nat.choose_eq_zero_of_lt (by omega : L < m + 1)] at hr
          omega
        refine ⟨[], L - m - 1, m, by rw [List.length_nil]; omega, ?_, ?_⟩
        · rw [unrank, if_pos (by omega), show r = L.choose m - 1 by omega, unrank_last (by omega),
            show L - m = L - m - 1 + 1 by omega]
          rfl
        · rw [unrank, if_neg (by omega), hlast, Nat.sub_self, unrank_zero hmL, Nat.sub_sub]
          rfl
      · -- Neither mask contains the first level.
        obtain ⟨pre, a, b, hlen, hthis, hnext⟩ := ih (m := m + 1) (r := r - L.choose m) (by omega)
        refine ⟨false :: pre, a, b, by rw [List.length_cons]; omega, ?_, ?_⟩
        · rw [unrank, if_neg (by omega), hthis, List.cons_append]
        · rw [unrank, if_neg (by omega), show r + 1 - L.choose m = r - L.choose m + 1 by omega,
            hnext, List.cons_append]

end ThreeSumApsp.Spec
