/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecCrossing_Crossing
public import PaddedDescent.F.Fuel
public import SingleBitPieces.SecCrossing_PolyA
public import ToTuring.Lib.Table
public import SingleBitPieces.SecNetworks_LemGrouping
public import Paper.SecLevel_Recursion
public import ClauseBound.Alg.Grid
import PaddedDescent.F.FuelCert
import Mathlib.Tactic

/-! # A sum over θ ∈ {0,1}^c as a sum over the words of c bits

`Pieces.sum_ofFn`: a sum over θ ∈ {0,1}^c, the index of a factorization in Definition 1, written as
functions `Fin c → Bool`, equals the same sum over the words of c bits (`words c`). -/

public section

namespace SingleBitPieces.Level

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset

namespace Pieces

/-- A sum over θ ∈ {0,1}^c, written as functions, is the sum over the words of c bits. -/
theorem sum_ofFn (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Fin c → Bool, G (List.ofFn θ) = ∑ w ∈ words c, G w := by
  refine sum_bij (fun θ _ => List.ofFn θ) (fun θ _ => mem_words.2 List.length_ofFn) (fun θ _ θ' _ h => List.ofFn_injective h)
    (fun w hw => ?_) fun θ _ => rfl
  obtain rfl := mem_words.1 hw
  exact ⟨fun t => w[t], mem_univ _, List.ofFn_getElem⟩

end Pieces

end SingleBitPieces.Level
