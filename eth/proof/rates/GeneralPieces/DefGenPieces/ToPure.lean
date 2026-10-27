/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.DefGenPieces.Conv

/-! # Sums over strings of bits, as functions and as words

A sum over the strings of n bits, written as functions from {0, …, n − 1} to the bits
(`Pieces.Bits n`), is the same as a sum over the words of n bits (`sum_bitsOf`). -/

@[expose] public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime

namespace DefGenPieces

open Trim

/-- A sum over all strings of n bits, as functions, is the sum over all words of n bits. -/
theorem sum_bitsOf {n : ℕ} (G : List Bool → ℤ) : ∑ θ : Pieces.Bits n, G (bitsOf θ) = ∑ w ∈ words n, G w :=
  Finset.sum_nbij bitsOf (fun θ _ => mem_words.2 (length_bitsOf θ)) (fun _ _ _ _ e => List.ofFn_injective e)
    (fun _ hw => let ⟨x, hx⟩ := exists_bitsOf (mem_words.1 (Finset.mem_coe.1 hw)); ⟨x, Finset.mem_coe.2 (Finset.mem_univ x), hx⟩) fun _ _ => rfl

end DefGenPieces

open DefGenPieces

end GeneralPieces
