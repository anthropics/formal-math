/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PrintedOrder.Defs
import ThmCount.Main
import RecursionWithPieces.Forms

/-! # Appendix C, Theorem C: the implication of proof/consequences/ThmCount/ applied

proof/consequences/ThmCount/ proves the implication from Theorem D(b) to Theorem C
(`ThmCount.stTheorem`) for every machine with the bound of Theorem D(b). Here it is applied to the
proof of Theorem D(b) (`RecursionWithPieces.Forms.thmVariablesB`). This is not the route of the
proof sketch of Appendix C. -/

public section

namespace PrintedOrder

/-- **Theorem C**, in the wording of PaperSentencesStatement.lean: one algorithm computes the number
of satisfying assignments of a 3-CNF on n ≥ 2 variables in time 2^{O(n/(log n)^{1/20})}. It is
`ThmCount.stTheorem` applied to `RecursionWithPieces.Forms.thmVariablesB`. -/
theorem countRateFromBoundInN : CountRateFromBoundInN := ThmCount.stTheorem RecursionWithPieces.Forms.thmVariablesB

end PrintedOrder
