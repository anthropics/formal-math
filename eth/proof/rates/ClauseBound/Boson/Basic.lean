/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Defs

/-! # The monomials of a given weight, the grading of the operators a[r], and rules for the normally ordered product

* `mem_P`, `mem_Pz`, `card_P`: the monomials of weight m are the multisets of positive integers with
  sum m, and there are p(m) of them.
* `op_grade`: a[r] raises the weight by r.
* `nop_eq_sum`: the index sets in the definition of the normally ordered product may be enlarged.

The auxiliary statements are in the namespace `ClauseBound.Boson.Basic`. -/

public section

namespace ClauseBound.Boson

open Finset

namespace Basic

/-- A nonzero entry of a normally ordered product comes from a nonzero entry of the family, after a
part of π or a part of σ has been removed. -/
theorem nop_ne_zero {n : ℕ} {F : ℤ → Ker} {r : ℤ} {π σ : Multiset ℕ} (h : nop n F r π σ ≠ 0) :
    (∃ l ∈ π, F (r - l) (π.erase l) σ ≠ 0) ∨ ∃ k ∈ σ, F (r + k) π (σ.erase k) ≠ 0 := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 : ∀ l ∈ π, F (r - l) (π.erase l) σ = 0 := fun l hl => by
    by_contra h0
    exact hcon.1 ⟨l, hl, h0⟩
  have h2 : ∀ k ∈ σ, F (r + k) π (σ.erase k) = 0 := fun k hk => by
    by_contra h0
    exact hcon.2 ⟨k, hk, h0⟩
  apply h
  unfold nop
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro k hk
    simp [ann, h2 k (Multiset.mem_toFinset.1 hk)]
  · intro l hl
    have hl' := Multiset.mem_toFinset.1 hl
    simp [cre, hl', h1 l hl']

/-- The weight after a part has been removed. -/
theorem sum_erase_cast {π : Multiset ℕ} {l : ℕ} (h : l ∈ π) : ((π.erase l).sum : ℤ) = π.sum - l := by
  have := Multiset.sum_erase h
  omega

end Basic

open Basic

theorem mem_P {m : ℕ} {τ : Multiset ℕ} : τ ∈ P m ↔ τ.sum = m ∧ 0 ∉ τ := by
  unfold P
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact ⟨q.parts_sum, fun h => lt_irrefl 0 (q.parts_pos h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨τ, fun {i} hi => Nat.pos_of_ne_zero fun h0 => h2 (h0 ▸ hi), h1⟩, Finset.mem_univ _, rfl⟩

theorem mem_Pz {m : ℤ} {τ : Multiset ℕ} : τ ∈ Pz m ↔ (τ.sum : ℤ) = m ∧ 0 ∉ τ := by
  unfold Pz
  split_ifs with h
  · rw [mem_P]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  · constructor
    · intro h0
      simp at h0
    · rintro ⟨h1, -⟩
      omega

theorem card_P (m : ℕ) : #(P m) = Partitions.p m := by
  unfold P Partitions.p
  rw [Finset.card_image_of_injective _ fun q q' h => Nat.Partition.ext h, Finset.card_univ]

/-- a[r] raises the weight by r. -/
theorem op_grade {a : List ℕ} {r : ℤ} {π σ : Multiset ℕ} (h : op a r π σ ≠ 0) : (π.sum : ℤ) = σ.sum + r := by
  induction a generalizing r π σ with
  | nil =>
    unfold op at h
    split_ifs at h with h0
    · unfold one at h
      split_ifs at h with h1
      · rw [h0, h1, add_zero]
      · exact absurd rfl h
    · exact absurd rfl h
  | cons n a ih =>
    rcases nop_ne_zero (show nop n (op a) r π σ ≠ 0 from h) with ⟨l, hl, h1⟩ | ⟨k, hk, h1⟩
    · have := ih h1
      rw [sum_erase_cast hl] at this
      omega
    · have := ih h1
      rw [sum_erase_cast hk] at this
      omega

/-- In `nop` the two index sets may be replaced by any larger finite sets. -/
theorem nop_eq_sum (n : ℕ) (F : ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) {S T : Finset ℕ} (hS : π.toFinset ⊆ S) (hT : σ.toFinset ⊆ T) :
    nop n F r π σ = ∑ l ∈ S, bet n l * cre l (F (r - l)) π σ + ∑ k ∈ T, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ := by
  unfold nop
  rw [Finset.sum_subset hS, Finset.sum_subset hT]
  · intro k _ hk
    have : σ.count k = 0 := Multiset.count_eq_zero.2 fun h => hk (Multiset.mem_toFinset.2 h)
    simp [ann, this]
  · intro l _ hl
    have : l ∉ π := fun h => hl (Multiset.mem_toFinset.2 h)
    simp [cre, this]

namespace Basic

end Basic

end ClauseBound.Boson
