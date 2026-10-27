/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Half

/-! # The pieces made from partitions, with the partitions given as lists

A program writes a partition of h as a list of its parts in some order of its own. Here a string x
is encoded by a list ℓ(x) of positive integers with sum h, and different strings have
lists that differ as multisets. The pieces `ApcL` are defined from these lists in the same way as
the pieces A_s in the proof of Theorem B are defined from partitions.
`ApcL_col_eq` writes a piece as a sum, over i ≤ 2h and the monomials τ of weight 2h − s − i, of
products of a function of (x,u) and a function of (y,v), as in the column-wise
expansion in the proof of Theorem B. -/

public section

namespace ClauseBound.Boson

open Finset

/-- The piece number s, for an encoding ℓ of the strings by lists of positive integers with sum h. -/
@[expose] def ApcL {lam : ℕ} (ℓ : Pieces.Bits lam → List ℕ) (h : ℕ) (s : ℤ) : Pieces.Four lam := fun x y u v =>
  ((h.factorial / zz (ℓ v : Multiset ℕ) : ℕ) : ℤ) * Qk (aFam (ℓ x)) (ℓ v) s (ℓ u : Multiset ℕ) (ℓ y : Multiset ℕ)

namespace HalfList

end HalfList

variable {lam h : ℕ}

variable {ℓ : Pieces.Bits lam → List ℕ}

/-- The piece as a sum over i ≤ 2h and the monomials τ of weight 2h − s − i: one factor depends on
(x,u), the other on (y,v). -/
theorem ApcL_col_eq (hℓ : ∀ x, Pos (ℓ x) ∧ (ℓ x).sum = h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ApcL ℓ h s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (2 * h - s - i),
      topK (ℓ x) h i (s - h + i) (ℓ u : Multiset ℕ) τ * botK (ℓ v) h (h - s - i) τ (ℓ y : Multiset ℕ) := by
  unfold ApcL
  rw [Half.Qk_eq, (hℓ v).2, Multiset.sum_coe, (hℓ y).2, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, show (h : ℤ) + (h - s - i) = 2 * h - s - i by ring]
  exact sum_congr rfl fun τ _ => mul_left_comm _ _ _

end ClauseBound.Boson
