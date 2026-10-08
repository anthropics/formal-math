/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Lemma36a

/-!
# Lemma 36(b)

Lemma 36(b) reduces 3SUM on `n` real numbers to polylogarithmically many calls of a counting
problem on the blocks `A_i`, `B_j` of `d` numbers.  The reduction is cited from [CVX22]; this file
proves the part that the paper argues itself: a call is one comparison count.  The rows are the
pairs `(i,k)` and the columns the pairs `(j,ℓ)`.  All numbers have the same color, so a comparison
count is the number of pairs `x < y` between two lists (`comparisonCount_eq_card_pairs`), and by
Fredman's trick this is the count that the call asks for (`lemma_36b_count`).  The lists have
`|K'|` and `|L'|` numbers, at most `d` (`lemma_36b_lists`), and forming them costs `O(nd)`
subtractions (`lemma_36b_subtractions`).
-/

public section

namespace ThreeSumApsp

open Finset Asymptotics Filter
open ComparisonCounts

open Classical in
/-- Section 5.2: "In those of Lemma 36(b), all numbers have the same color, and γ(r,c) is the number
of pairs x < y between the two lists." -/
theorem comparisonCount_eq_card_pairs {n d : ℕ} (cmp : Cmp) (Ls : Lists n d) (χ₀ : Fin d)
    (hrow : ∀ r, ∀ x ∈ Ls.row r, x.2 = χ₀) (hcol : ∀ c, ∀ y ∈ Ls.col c, y.2 = χ₀) (r c : Fin n) :
    comparisonCount cmp Ls r c =
      (univ.filter fun p : Fin (Ls.row r).length × Fin (Ls.col c).length =>
        cmp.Holds ((Ls.row r).get p.1).1 ((Ls.col c).get p.2).1).card := by
  refine congrArg card (filter_congr fun p _ => and_iff_right ?_)
  exact (hrow r _ (List.get_mem _ _)).trans (hcol c _ (List.get_mem _ _)).symm

open Classical in
/-- For lists `l₁`, `l₂` without repetitions, the pairs of places of `l₁.map f` and `l₂.map g` whose
entries satisfy `Q` are as many as the pairs `(a, b)` of elements of `l₁` and `l₂` with
`Q (f a) (g b)`. -/
private theorem card_places {α β α' β' : Type} [DecidableEq α] [DecidableEq β] {l₁ : List α}
    {l₂ : List β} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (f : α → α') (g : β → β') (Q : α' → β' → Prop) :
    (univ.filter fun p : Fin (l₁.map f).length × Fin (l₂.map g).length =>
        Q ((l₁.map f).get p.1) ((l₂.map g).get p.2)).card
      = ((l₁.toFinset ×ˢ l₂.toFinset).filter fun ab => Q (f ab.1) (g ab.2)).card := by
  refine card_bij
    (fun p _ => (l₁.get (p.1.cast (by simp)), l₂.get (p.2.cast (by simp)))) ?_ ?_ ?_
  · intro p hp
    refine mem_filter.2 ⟨mem_product.2 ⟨List.mem_toFinset.2 (List.get_mem _ _),
      List.mem_toFinset.2 (List.get_mem _ _)⟩, ?_⟩
    simpa using (mem_filter.1 hp).2
  · intro p _ q _ hpq
    obtain ⟨hfst, hsnd⟩ := Prod.mk.inj hpq
    exact Prod.ext (Fin.cast_injective _ (h₁.injective_get hfst))
      (Fin.cast_injective _ (h₂.injective_get hsnd))
  · rintro ⟨a, b⟩ hab
    obtain ⟨hmem, hQ⟩ := mem_filter.1 hab
    obtain ⟨i, rfl⟩ := List.get_of_mem (List.mem_toFinset.1 (mem_product.1 hmem).1)
    obtain ⟨j, rfl⟩ := List.get_of_mem (List.mem_toFinset.1 (mem_product.1 hmem).2)
    refine ⟨(i.cast (by simp), j.cast (by simp)), mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    simpa using hQ

/-- All numbers in the lists of Lemma 36(b) have the same color. -/
private theorem color_eq_of_mem_lists45 {b d : ℕ} (A B : Fin b → Fin d → ℝ)
    (K' L' : Finset (Fin d)) (χ₀ : Fin d) :
    (∀ r, ∀ x ∈ (lists45 A B K' L' χ₀).row r, x.2 = χ₀) ∧
      (∀ c, ∀ y ∈ (lists45 A B K' L' χ₀).col c, y.2 = χ₀) := by
  constructor <;> intro _ x hx <;> obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx <;> rfl

/-- Proof of Lemma 36(b): "By Fredman's trick, the condition is A_i[k'] - A_i[k] < B_j[ℓ] -
B_j[ℓ'].  So a call is one comparison count: the rows are the n pairs (i,k) and the columns are the
n pairs (j,ℓ) ... and P := Q."  Also with ≤, and with k' and ℓ' restricted to subsets K' and L' of
[d]. -/
theorem lemma_36b_count {b d : ℕ} (cmp : Cmp) (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d))
    (χ₀ : Fin d) (i j : Fin b) (k l : Fin d) :
    count45 cmp A B K' L' i j k l =
      comparisonCount cmp (lists45 A B K' L' χ₀)
        (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) := by
  classical
  -- all numbers have one color, so `γ` counts the pairs of places with `x < y`
  rw [comparisonCount_eq_card_pairs cmp _ χ₀ (color_eq_of_mem_lists45 A B K' L' χ₀).1
    (color_eq_of_mem_lists45 A B K' L' χ₀).2]
  -- the lists have no repetitions: count the pairs `(k',ℓ') ∈ K' × L'` instead of the places
  refine ((card_places (nodup_listOf K') (nodup_listOf L') _ _
    fun x y : ℝ × Fin d => cmp.Holds x.1 y.1).trans ?_).symm
  -- the two conditions on `(k',ℓ')` agree by Fredman's trick
  refine congrArg card ?_
  ext kl
  simp only [mem_filter, mem_product, List.mem_toFinset, mem_listOf, Equiv.symm_apply_apply,
    cmp.fredman (A i k) (A i kl.1) (B j l) (B j kl.2)]

/-- Lemma 36(b): the comparison counts have "n row lists and n column lists of at most d numbers,
all of the same color"; the proof of Lemma 36: "A restriction of k' or of ℓ' deletes numbers from
the lists." -/
theorem lemma_36b_lists {b d : ℕ} (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d)) (χ₀ : Fin d) :
    (lists45 A B K' L' χ₀).Valid ∧
      (∀ r, ((lists45 A B K' L' χ₀).row r).length = K'.card) ∧
      (∀ c, ((lists45 A B K' L' χ₀).col c).length = L'.card) ∧
      (∀ r, ∀ x ∈ (lists45 A B K' L' χ₀).row r, x.2 = χ₀) ∧
      (∀ c, ∀ y ∈ (lists45 A B K' L' χ₀).col c, y.2 = χ₀) := by
  refine ⟨⟨fun r => ?_, fun c => ?_⟩, fun r => ?_, fun c => ?_,
    color_eq_of_mem_lists45 A B K' L' χ₀⟩
  · simpa [lists45] using length_listOf_le K'
  · simpa [lists45] using length_listOf_le L'
  · simp [lists45, length_listOf]
  · simp [lists45, length_listOf]

/-- Lemma 36(b): "forming the lists of a comparison count costs O(nd) subtractions", with
n = b * d. -/
theorem lemma_36b_subtractions {b d : ℕ} (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d))
    (χ₀ : Fin d) :
    ∑ r, ((lists45 A B K' L' χ₀).row r).length + ∑ c, ((lists45 A B K' L' χ₀).col c).length
      ≤ 2 * (b * d) * d :=
  (lemma_36b_lists A B K' L' χ₀).1.sum_length_le

end ThreeSumApsp
