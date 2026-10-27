/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmCount.Defs
import ThmCount.Main
import RecursionWithPieces.Forms

/-! # The closing remark of Appendix C: «with it the time becomes 2^{O(n(log log n)^{2/3}/(log n)^{α/3})}», as a sentence

The sentence is that of the paper, with α = 1/2. `stRemarkTime` is `stRemarkTime_of`
(proof/consequences/ThmCount/Main.lean) applied to Theorem D(b)
(`RecursionWithPieces.Forms.thmVariablesB`). It is not the remark's own derivation of the time: the
sentence is weaker than Theorem D(b) at k = 3 and follows from it by comparing the rates. -/

public section

namespace ThmCount

/-- One deterministic algorithm computes the number of satisfying assignments of a 3-CNF on n ≥ 4
variables in time 2^{O(n·(log log n)^{2/3}/(log n)^{1/6})}: the statement `ThmCount.StRemarkTime`. -/
theorem stRemarkTime : StRemarkTime := stRemarkTime_of RecursionWithPieces.Forms.thmVariablesB

end ThmCount
