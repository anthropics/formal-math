/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecCrossing_Crossing
public import PaddedDescent.F.FuelCert
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Log

/-! # A closure lemma for certificates of polynomial time, used for Lemma 2(a)
This file lies beside files for a variant of Lemma 2 whose pieces are made from single bits (ρ =
(log 12)/4), but its lemma serves the paper's own pieces of Lemma 2 as well.
«Computable in time poly(λ)» is rendered as a certificate `Groundwork.PolyT` (some Turing machine of
the model used here computes the function in time polynomial in the length of its input). The
statement here, `unary_min_right`, says that the smaller of a polynomial-time number and a number
given in unary is again given in unary.

It lies in the namespace `SingleBitPieces.SecCrossing_PolyA`. -/

public section

namespace SingleBitPieces

open Groundwork PaddedDescent.F Finset

namespace SecCrossing_PolyA

variable {α : Type} [Enc α]

/-! ### The closure lemma -/

/-- The smaller of any number and a number given in unary is given in unary. -/
theorem unary_min_right {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hg (PolyT.min' hf hg.poly) fun _ => min_le_right _ _

end SecCrossing_PolyA

open SecCrossing_PolyA

end SingleBitPieces
