/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Tree.Defs
public import UniformInK.Cert.Sparsify
public import CountKSatRate.Cert

/-! # One step of the walk of the counting tree is polynomial-time jointly in the width k

The two children of a node of the counting tree, for the thresholds `thetaU τ` and with the width k
a function of the context, given in unary together with 2^k,
are computed in polynomial time jointly in k, τ and the node. -/

public section

namespace UniformInK

open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert

namespace CertWalk

variable {α : Type} [Enc α]

/-- The two children of a node of the counting tree are polynomial-time jointly in k, τ and the
node, if k and 2^k are given in unary. -/
theorem polyT_stepCU {k τ : α → ℕ} {s : α → CNode} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => stepC (thetaU (τ x)) (k x) (s x) := by
  have hp : PolyT fun x => pickK (thetaU (τ x)) (k x) (s x).1 := CertSparsify.polyT_pickKU hk h2 hτ (by fun_prop)
  exact PolyT.optionMap (f := fun (x : α) (HP : PCl × PFml) => ((addP [HP.1] (s x).1, (s x).2), (addP HP.2 (s x).1, negU HP.1 ++ (s x).2)))
    (by fun_prop) hp

end CertWalk

end UniformInK
