/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cross.Psi

/-!
# The value at `x = 1`: a determinant
-/

namespace Nc.Cross

open Matrix Finset

/-- The matrix of coincidences of two increasing tuples. -/
theorem det_coinc {R : Type*} [CommRing R] {μ : ℕ} (f g : Fin μ → ℕ) (hf : StrictMono f) (hg : StrictMono g) :
    (of fun i j => if f i = g j then (1 : R) else 0).det = if f = g then 1 else 0 := by
  by_cases h : f = g
  · subst h
    rw [if_pos rfl]
    have : (of fun i j => if f i = f j then (1 : R) else 0) = (1 : Matrix (Fin μ) (Fin μ) R) := by
      ext i j
      simp [Matrix.one_apply, hf.injective.eq_iff]
    rw [this, det_one]
  · rw [if_neg h]
    have hr : ¬ Set.range f ⊆ Set.range g := by
      intro hsub
      apply h
      have hfin : Set.range f = Set.range g := by
        have h1 : (Finset.univ.image f) ⊆ (Finset.univ.image g) := by
          intro n hn
          have : n ∈ Set.range g := hsub (by simpa using hn)
          simpa using this
        have h2 := Finset.eq_of_subset_of_card_le h1 (by
          rw [Finset.card_image_of_injective _ hf.injective, Finset.card_image_of_injective _ hg.injective])
        have h3 := congrArg (fun s : Finset ℕ => (s : Set ℕ)) h2
        simpa using h3
      exact StrictMono.range_inj hf hg |>.1 hfin
    rw [Set.not_subset] at hr
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hr
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    simp only [of_apply]
    rw [if_neg]
    intro hij
    exact hi ⟨j, hij.symm⟩

end Nc.Cross
