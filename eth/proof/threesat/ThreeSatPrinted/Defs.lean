/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatOnTree.Defs
public import Eight.ViaGrouping.AlgDefs

/-! # The deciding form of procedure #Sat of Algorithm 1 on the tree of the sparsification procedure of Appendix C, with NETWORK as in the printed proof of Lemma 1: definition

`SATCp ℓ τ` is `ThreeSatOnTree.satC τ` (proof/threesat/ThreeSatOnTree/Defs.lean: decode the input,
walk depth first the tree of the sparsification procedure of Appendix C at width 3, test the formula
ψ at every leaf) with
`Eight.ViaGrouping.COUNTp ℓ` as the test (proof/networks/Eight/ViaGrouping/AlgDefs.lean: COUNT of
Algorithm 1 at level ℓ, in which NETWORK is the algorithm of the printed proof of Lemma 1 and CLIQUE
that of the proof of Proposition 3 on the pieces of Lemma 2).
The thresholds of the procedure are θ 0 = 1, θ i = 4·τ^(2i−1) (`UniformInK.thetaU τ`), not
Calabro's, which Appendix C takes. This is the tree whose leaves the Lean statement of Lemma 4
(`SparsificationLemma.Mach.LemSparsification`) lists; the paper cites Lemma 4 and does not say which
procedure
computes its list.
This file has one definition and no proof. -/

@[expose] public section

namespace ThreeSatPrinted

open Paper

/-- **The deciding form of procedure #Sat(φ)** of Algorithm 1, for a fixed level ℓ and a fixed
parameter τ: the tree of the sparsification procedure of Appendix C is walked, and every leaf is
tested with COUNT at level ℓ. -/
def SATCp (ℓ τ : ℕ) : StepMachine (List Bool) Bool := ThreeSatOnTree.satC τ (Eight.ViaGrouping.COUNTp ℓ)

end ThreeSatPrinted
