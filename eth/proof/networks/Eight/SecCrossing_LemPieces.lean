/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_Identity
public import Eight.SecCrossing_Blocks
public import Eight.SecCrossing_PiecesAC
public import Eight.SecCrossing_MulOut
public import Eight.SecCrossing_Chunk
public import Eight.SecCrossing_Fact
public import Eight.SecCrossing_Cert

/-! # Lemma 2 from the eight-square identity, without hypotheses

The files of proof/networks/Eight/ imported here prove the parts of the section «Two crossing
equalities as a sum of ⌈λ/3⌉ + 1 cheaper functions»; where a part uses another one, it takes it as a
hypothesis. Here the hypotheses are filled in. The order is that
of the paper: the sign rule (`signs`, SecCrossing_Identity.lean) gives R + C = 2[x = v][y = u],
which gives part (a); the factorizations of R and C through 3 bits give part (b) (`stFact`, for the
functions `fTop`, `fBot` of the
paper's proof); part (c) is arithmetic. -/

public section

namespace Eight

open Groundwork

/-- Lemma 2(b) for the functions of the paper's proof, θ = (Q, θ'), with the factorization through
2λ bits wherever the other one would need more. -/
theorem stFact : StFact := stFact_of stChunk stAMul A_eq_sum_subsets

/-- **Lemma 2**, parts (a), (b), (c), as in the paper but without the claims «computable in time
poly(λ)». -/
theorem lemPieces : LemPieces :=
  ⟨a_sum signs, a_abs, lemPieces_b_row stFact, lemPieces_b_col stFact, c_row, c_col, fun _ _ _ hi => crow_add_ccol_le hi, c_sum⟩

end Eight
