/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecLevel_GridWords

/-! # The display «the smaller total» for the numbers that the algorithm compares

Procedure CLIQUE of Algorithm 1 (`levelAlg`) compares the numbers `totalG eightF g g false 0 λ y`
and `totalG eightF g g true 0 λ y`. They are the totals U_row and U_col of the two networks of ι
(`U_netOfι`), so display (36) of the proof of
Proposition 3 (`Eight.eqMinTotal`, for the networks on words `eqMinTotal_words`) bounds the smaller
one: `stMin`. -/

public section

namespace Eight.Level

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg

namespace Min

end Min

/-- Display (36) of the proof of Proposition 3, «min(U_row, U_col) ≤ ½(U_row + U_col) ≤ N/g + |ℛ|(11λ/3 + 8)
≤ N(ρ + 1/g) + 2g⁴», N = g⁴λ, ρ = 11/12, for the numbers that the algorithm compares. From
`eqMinTotal_words`, that is from `Eight.eqMinTotal`.
Same as in the paper; N/g is written g³λ. -/
theorem stMin : StMin := fun g lam y hlam => by
  rw [← U_netOfι g false lam y fun _ _ => 0, ← U_netOfι g true lam y fun _ _ => 0]
  exact eqMinTotal_words hlam g y _

end Eight.Level
