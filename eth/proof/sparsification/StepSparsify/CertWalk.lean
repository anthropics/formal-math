/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
public import CountKSatRate.Cert

/-! # Certificates of polynomial time for the sparsification of Appendix D, Step 5

This file proves `StCertNoTaut` of proof/sparsification/StepSparsify/Defs.lean.
`stCertNoTaut`: `noTaut` is a filter whose test runs through a clause and looks up a literal in it;
each of these has a certificate. -/

public section

namespace StepSparsify

open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK SparsificationLemma

/-- The walk that adds up is polynomial-time jointly in k, s, the pad, the root and whatever the
value function depends on, if the thresholds serve and k, 2^k and s are given in unary. -/
theorem stCertWalkSG : StCertWalkSG := by
  intro Θ Lc hS α _ k s pad val r hk h2 hs' hp hv hr
  have u1 : Unary fun q : (α × (List CNode × ℕ) × Unit) × CNode => k q.1.1 :=
    hk.comp (h := fun q : (α × (List CNode × ℕ) × Unit) × CNode => q.1.1) (by fun_prop)
  have u2 : Unary fun q : (α × (List CNode × ℕ) × Unit) × CNode => 2 ^ k q.1.1 :=
    h2.comp (h := fun q : (α × (List CNode × ℕ) × Unit) × CNode => q.1.1) (by fun_prop)
  have u3 : Unary fun q : (α × (List CNode × ℕ) × Unit) × CNode => s q.1.1 :=
    hs'.comp (h := fun q : (α × (List CNode × ℕ) × Unit) × CNode => q.1.1) (by fun_prop)
  have u4 : PolyT fun q : (α × (List CNode × ℕ) × Unit) × CNode => q.2 := by fun_prop
  have hs : PolyT fun q : (α × (List CNode × ℕ) × Unit) × CNode => stepC (Θ (k q.1.1) (s q.1.1)) (k q.1.1) q.2 :=
    hS.cert _ _ _ _ u1 u2 u3 u4
  have h := foldl_cap (pad := pad) (l := pad) (a := fun x => ([r x], 0))
    (g := fun x st _ => roundS (stepC (Θ (k x) (s x)) (k x)) (val x) st) ([], 0) hp hp (by fun_prop)
    (polyT_roundS (step := fun p : α × (List CNode × ℕ) × Unit => stepC (Θ (k p.1) (s p.1)) (k p.1)) (val := fun p => val p.1) (st := fun p => p.2.1)
      hs (by fun_prop) (by fun_prop))
  unfold walkSG
  exact PolyT.snd h

/-- Deleting the clauses that contain a variable together with its negation is polynomial-time. -/
theorem stCertNoTaut : StCertNoTaut := by
  unfold StCertNoTaut noTaut
  fun_prop

end StepSparsify
