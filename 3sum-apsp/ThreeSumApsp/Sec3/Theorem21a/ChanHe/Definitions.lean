/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Theorem 21(a), the reduction of Chan and He: the problems on three sets and on arrays

The problems between which the reduction of [CH20] passes on its way from 3SUM to Convolution-3SUM:
3SUM on three sets (`HasSol`), Convolution-3SUM on three arrays (`ConvSol`, and `Node.Conv` for the
arrays of a node of the recursion tree) and on one array (`ConvOne`).  An array is a function on
`ℕ`, of which only the cells below a given length are read.  `Bdd U S` says that the elements of `S`
have absolute value at most `U`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-- 3SUM on three sets (Definition 2.1 of [CH20], without the requirement that the sets have the
same size). -/
def HasSol (S₁ S₂ S₃ : Finset ℤ) : Prop := ∃ a ∈ S₁, ∃ b ∈ S₂, ∃ c ∈ S₃, a + b + c = 0

/-- Convolution-3SUM on three arrays of length `N` (Definition 2.2 of [CH20]).  [CH20] does not say
where the indices start or what happens when `i + j` leaves the array: we number the cells from 0
and ask for `i + j < N`. -/
def ConvSol (N : ℕ) (X Y Z : ℕ → ℤ) : Prop := ∃ i j : ℕ, i + j < N ∧ X i + Y j = Z (i + j)

/-- Convolution-3SUM on one array of length `N`: the three arrays are the same.  This is the
`Convolution3SUM` of Section 1.2 for the first `N` cells (`convolution3SUM_iff_convOne`). -/
def ConvOne (N : ℕ) (y : ℕ → ℤ) : Prop := ConvSol N y y y

/-- The Convolution-3SUM instance of the node has a solution, at length `N`. -/
def Node.Conv (ν : Node) (U N : ℕ) : Prop :=
  ConvSol N (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)

/-- All elements of `S` have absolute value at most `U`. -/
def Bdd (U : ℕ) (S : Finset ℤ) : Prop := ∀ x ∈ S, |x| ≤ (U : ℤ)

end ChanHe

end ThreeSumApsp
