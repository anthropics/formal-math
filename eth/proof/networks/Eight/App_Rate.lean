/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_PolyDefs
public import ClauseBound.Gen.Defs
import Eight.App_Pieces
import Mathlib.Tactic

/-! # A sum over θ ∈ {0,1}^c as a sum over the words of c bits

`sum_ofFn`: a sum over θ ∈ {0,1}^c, written as functions (`Pieces.Bits c`), equals the sum over the
words of c bits (`words c`).
It belongs to Appendix A, on the functions A_0, …, A_t of Lemma 2 as pieces: a factorization in the
sense of Definition 1 is a sum over θ ∈ {0,1}^c, and this lemma lets it be read as a sum over words
of c bits. -/

public section

namespace Eight

open Finset Groundwork ClauseBound.Alg

/-- A sum over θ ∈ {0,1}^c, written as functions, is the sum over the words of c bits. -/
theorem sum_ofFn (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Pieces.Bits c, G (List.ofFn θ) = ∑ w ∈ words c, G w := by
  refine sum_bij (fun θ _ => List.ofFn θ) (fun θ _ => mem_words.2 List.length_ofFn) (fun θ _ θ' _ h => List.ofFn_injective h)
    (fun w hw => ?_) fun θ _ => rfl
  obtain rfl := mem_words.1 hw
  exact ⟨fun t => w[t], mem_univ _, List.ofFn_getElem⟩

end Eight
