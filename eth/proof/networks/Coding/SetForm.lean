/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.Sets
import Exits.End

/-! # Theorem 2 in its decision form for 3-CNFs as sets

Theorem 2 in the form for deciding (the paper's Theorem 2 counts the satisfying assignments): for
every δ > 0 there is a deterministic algorithm that decides 3-SAT on n variables, with any number of
clauses, in time O(2^{δn}). Section 6: «a clause is a nonempty set of literals, and a 3-CNF is a
finite set of clauses with at most 3 literals each».
`stSetForm` is Theorem 2 for these sets, in whichever way a set is written on the tape as a list of
lists. It is `stSetFormOf` (proof/networks/Coding/Sets.lean) applied to `stWrites` (lists write
sets) and to Theorem 2 for lists in the proof by Algorithm 1, `Exits.threeSat_by_algorithm`
(proof/threesat/Exits/End.lean). -/

public section

namespace Coding

/-- **Theorem 2 in its decision form for 3-CNFs as sets**: in the form for deciding: for every δ > 0
there is a deterministic algorithm that decides 3-SAT on n variables, with any number of clauses, in
time O(2^{δn}), a 3-CNF being «a finite set of clauses with at most 3 literals each». -/
theorem stSetForm : StSetForm := stSetFormOf stWrites Exits.threeSat_by_algorithm

end Coding
