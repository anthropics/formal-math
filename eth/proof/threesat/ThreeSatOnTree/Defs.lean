/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.Defs
public import WidthK.Top.Sat
public import WidthK.Decode
public import SparsifyWidthK.DefsProg
public import UniformInK.Spars.Defs

/-! # The machine for 3-SAT that walks the recursion tree of a sparsification procedure: definitions

`satC τ Mc` is the machine `satMK` of proof/consequences/WidthK/Top/Sat.lean at width 3, on the tree
of a sparsification procedure in the style of Appendix C, with thresholds of this development, θ 0 =
1, θ i = 4·τ^(2i−1) (`UniformInK.thetaU τ`): decode the input, answer «no» if there is an empty
clause, walk the tree depth first, and test the formula ψ at every leaf with the machine `Mc`.
This file has definitions only. -/

@[expose] public section

namespace ThreeSatOnTree

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper

/-- The machine for 3-SAT on the tree of Appendix C with parameter τ: decode the input, walk the
tree, test every leaf with `Mc`. -/
def satC (τ : ℕ) (Mc : StepMachine Formula ℤ) : StepMachine (List Bool) Bool := satMK (DecodeK.decK 3) (stepK (thetaU τ) 3) rootP Mc

end ThreeSatOnTree
