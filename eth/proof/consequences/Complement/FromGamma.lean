/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Complement.Defs
import Complement.Readers
import SizeCircuit.Sized

/-! # Section 7, proof of Corollary 7: the route from end to end, counted in steps

`stFromGamma` is `stFromGamma_of` (proof/consequences/Complement/Readers.lean) applied to
`SizeCircuit.stSizedBy` from proof/consequences/SizeCircuit/Sized.lean; so this file builds only
with the proofs of proof/consequences/SizeCircuit/. -/

public section

namespace Complement

/-- **The route from end to end, counted in steps**: for every family of circuits that tests the
size, every δ > 0 and every procedure E for #3-SAT whose exponent is small enough, the machine «Γ
beside the formula, then E», put after the reader of the formula for independent sets, after
`readClique` and after `readCover`, returns the numbers of independent sets, cliques and vertex
covers of size s ≤ n within c'·2^{δn} steps. -/
theorem stFromGamma : StFromGamma := stFromGamma_of SizeCircuit.stSizedBy

end Complement
