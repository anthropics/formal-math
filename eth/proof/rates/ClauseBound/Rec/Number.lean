/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Rec.Defs

/-! # Numbering the terms of a sum by bit strings

A function F(z,z') that is a sum of at most 2^c products f_i(z)·f'_i(z') factors through c bits:
give each term a string θ of c bits of its own, let the two functions of the
factorization be f_i and f'_i at the string of term i, and 0 at the strings that number no term. A
bound on the values of the f_i and f'_i is kept. -/

public section

namespace ClauseBound.Rec

open Finset Polynomial Pieces

/-- A sum of at most 2^c products f_i(z)·f'_i(z'), all values below b in absolute value, factors
through c bits with the bound b. -/
theorem factorsThrough_of_sum {Z Z' ι : Type} (S : Finset ι) (F : Z → Z' → ℤ) (f : ι → Z → ℤ) (f' : ι → Z' → ℤ) (b : ℤ) (c : ℕ)
    (hF : ∀ z z', F z z' = ∑ i ∈ S, f i z * f' i z') (hc : #S ≤ 2 ^ c) (hb : 0 < b)
    (hf : ∀ i ∈ S, ∀ z, |f i z| < b) (hf' : ∀ i ∈ S, ∀ z, |f' i z| < b) : FactorsThrough F c b := by
  classical
  have hcard : Fintype.card S ≤ Fintype.card (Bits c) := by simpa using hc
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have key : ∀ (i : S) (hi : ∃ j : S, e j = e i), hi.choose = i := fun i hi => e.injective hi.choose_spec
  refine ⟨fun z θ => if hθ : ∃ i : S, e i = θ then f hθ.choose z else 0,
    fun z' θ => if hθ : ∃ i : S, e i = θ then f' hθ.choose z' else 0, fun z z' => ?_, fun z θ => ?_, fun z' θ => ?_⟩
  · rw [hF, ← sum_coe_sort S, ← sum_subset (subset_univ (univ.map e)), sum_map]
    · refine sum_congr rfl fun i _ => ?_
      have hi : ∃ j : S, e j = e i := ⟨i, rfl⟩
      simp only [dif_pos hi, key i hi]
    · intro θ _ hθ
      have hn : ¬ ∃ i : S, e i = θ := fun ⟨i, hi⟩ => hθ (mem_map.2 ⟨i, mem_univ _, hi⟩)
      simp only [dif_neg hn, zero_mul]
  · by_cases hθ : ∃ i : S, e i = θ
    · simp only [dif_pos hθ]
      exact hf _ hθ.choose.2 z
    · simpa only [dif_neg hθ, abs_zero] using hb
  · by_cases hθ : ∃ i : S, e i = θ
    · simp only [dif_pos hθ]
      exact hf' _ hθ.choose.2 z'
    · simpa only [dif_neg hθ, abs_zero] using hb

end ClauseBound.Rec
