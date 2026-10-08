/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec4.Theorem30.QueryLists

/-!
# Bounds on the partial sums (proof of Theorem 30, "Word size")

"every value we compute is a sum of at most 10^m products of two such numbers".  A routine that adds
up numbers one after the other holds, at every moment, the sum of an initial part of a list.  This
file bounds all these sums, for two encodings whose entries are at most A and B in absolute value.

* What the dynamic program of Lemma 29 computes for a cube with e stars is at most 10^e A B
  (`abs_dpValue_le`), and so is every sum of an initial part of the ten values that it adds up
  for the cube (`abs_dp_partial_sum_le`).
* The numbers that a query adds up stand for disjoint sets of leaves contributing to its output
  string η (the paper's w), of which there are 10^m (`Lemma28.card_leaves`); so every sum of an
  initial part of them is at most 10^m A B (`abs_query_partial_sum_le`).
-/

public section

namespace ThreeSumApsp.Spec

variable {L : ℕ} {encA encB : Leaf L → ℤ} {A B : ℤ} (hA : ∀ τ, |encA τ| ≤ A)
  (hB : ∀ τ, |encB τ| ≤ B)

include hA hB

/-! ## The dynamic program of Lemma 29 -/

/-- A B ≥ 0 for bounds A, B on the two arrays. -/
theorem mul_nonneg_of_abs_le : 0 ≤ A * B :=
  mul_nonneg ((abs_nonneg _).trans (hA fun _ => Term.P0))
    ((abs_nonneg _).trans (hB fun _ => Term.P0))

/-- The product at a leaf is at most A B in absolute value. -/
private theorem abs_mul_le (τ : Leaf L) : |encA τ * encB τ| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul (hA τ) (hB τ) (abs_nonneg _) ((abs_nonneg _).trans (hA τ))

/-- What the dynamic program computes at depth e is at most 10^e A B in absolute value. -/
theorem abs_dpValue_le (e : ℕ) (π : Cube L) : |dpValue encA encB e π| ≤ 10 ^ e * (A * B) := by
  have hAB := mul_nonneg_of_abs_le hA hB
  induction e generalizing π with
  | zero =>
    rw [dpValue, pow_zero, one_mul]
    exact abs_mul_le hA hB _
  | succ e ih =>
    rw [dpValue]
    split_ifs with h
    · calc |∑ lam : Term, dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)|
          ≤ ∑ lam : Term, |dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _lam : Term, 10 ^ e * (A * B) := Finset.sum_le_sum fun lam _ => ih _
        _ = 10 ^ (e + 1) * (A * B) := by
            rw [Finset.sum_const, Finset.card_univ, card_term, nsmul_eq_mul]
            push_cast
            ring
    · rw [abs_zero]
      positivity

/-- What the dynamic program on digits computes for a cube at depth e is at most 10^e A B in
absolute value. -/
private theorem abs_dpValueD_le (e : ℕ) (π : Cube L) :
    |dpValueD (arrT encA) (arrT encB) e (digitsC π)| ≤ 10 ^ e * (A * B) := by
  rw [dpValueD_digitsC]
  exact abs_dpValue_le hA hB e π

/-- The ten values that the dynamic program adds up for a box with e + 1 stars (the proof of Lemma
29), the star at position ℓ being replaced by the ten terms in the order of their digits: every sum
of an initial part of them is at most 10^{e+1} A B. -/
theorem abs_dp_partial_sum_le (e : ℕ) (π : Cube L) (ℓ : Fin L) (k : ℕ) :
    |((tenValues (dpValueD (arrT encA) (arrT encB) e) (digitsC π) ℓ).take k).sum|
      ≤ 10 ^ (e + 1) * (A * B) := by
  refine (List.abs_sum_take_map_le (List.range 10) _ (B := 10 ^ e * (A * B))
    (fun d hd => ?_) k).trans
    (le_of_eq ?_)
  · -- each of the ten strings is a cube
    have hd' : d < 10 := List.mem_range.mp hd
    have hcube : (digitsC π).set ℓ d = digitsC (Cube.replace π ℓ (termOfIdx ⟨d, hd'⟩)) := by
      rw [digitsC_replace]
      exact congrArg _ (congrArg Fin.val (termEquiv.apply_symm_apply ⟨d, hd'⟩).symm)
    rw [hcube]
    exact abs_dpValueD_le hA hB e _
  · rw [List.length_range]
    push_cast
    ring

/-! ## A query -/

/-- Every sum of an initial part of the numbers that a query adds up is at most 10^m A B in absolute
value: the numbers stand for disjoint sets of leaves contributing to η, of which there are 10^m. -/
theorem abs_query_partial_sum_le {m t : ℕ} (ht : t ≤ m) {η : OutStr L}
    (hη : (innerSetO η).card = m) (k : ℕ) :
    |((queryTerms m t (arrT encA) (arrT encB) (storedD (arrT encA) (arrT encB))
        (digitsO η)).take k).sum| ≤ 10 ^ m * (A * B) := by
  have hcount : ((lowLeaves m t η).card : ℤ)
      + ∑ π ∈ (Vsets m t η).biUnion (BV η), ((Cube.leaves π).card : ℤ) = 10 ^ m := by
    exact_mod_cast Lemma28.card_leaves m t ht η hη
  refine (List.abs_sum_take_le_sum_abs _ k).trans ?_
  rw [queryTerms, List.map_append, List.sum_append, List.map_map, List.map_map,
    sum_lowList ht hη, sum_boxesOf ht hη]
  calc _ ≤ ∑ _τ ∈ lowLeaves m t η, A * B
        + ∑ π ∈ (Vsets m t η).biUnion (BV η), ((Cube.leaves π).card : ℤ) * (A * B) := by
        refine add_le_add (Finset.sum_le_sum fun τ _ => ?_) (Finset.sum_le_sum fun π _ => ?_)
        · -- a leaf stands for itself
          simp only [Function.comp]
          rw [leafProduct_digitsT]
          exact abs_mul_le hA hB τ
        · -- a box with e stars stands for its 10^e leaves
          simp only [Function.comp, storedD]
          rw [Cube.card_leaves, card_starLevels]
          push_cast
          exact abs_dpValueD_le hA hB _ π
    _ = 10 ^ m * (A * B) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← add_mul, hcount]

end ThreeSumApsp.Spec
