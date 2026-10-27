/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Basic
public import ToTuring.Poly.Comb
public import ToTuring.Poly.Walk
public import ToTuring.Poly.Decode
public import ToTuring.Poly.Sparsify
public import StepMachines.Prog.Sat

/-! Polynomial-time facts (`PolyT`) for the functions `decF`, `hasNil` and `posZ` that the 3-SAT
machine of `StepMachines.Prog.Sat`
uses. -/

@[expose] public section

namespace Groundwork.Prog

open Stepped Groundwork.Sparsify

theorem decF_polyT : PolyT decF := by have := Decode.dec_polyT; unfold decF; fun_prop

theorem hasNil_polyT : PolyT hasNil := by unfold hasNil; fun_prop

theorem posZ_polyT : PolyT posZ := by unfold posZ; fun_prop

/-- `satM τ M` decodes the input, answers `false` if `hasNil` holds, and otherwise walks the
sparsification tree and tests
every leaf by whether the count given by `M` is positive. It is `IsPolyT` if `M` is. -/
@[instance_reducible] def IsPolyT.satM (τ : ℕ) {M : Stepped Fml ℤ} [IsPolyT M] : IsPolyT (satM τ M) :=
  haveI := IsPolyT.mapOut (M := M) posZ_polyT
  haveI := IsPolyT.walk (T := Stepped.mapOut M posZ) (step := stepP τ) (root := rootP) (by fun_prop) (by fun_prop)
  haveI : IsPolyT (Stepped.const false : Stepped Fml Bool) := IsPolyT.const false
  haveI := IsPolyT.ite (M := (Stepped.const false : Stepped Fml Bool))
    (N := Stepped.walk (stepP τ) rootP (Stepped.mapOut M posZ)) hasNil_polyT
  IsPolyT.mapIn decF_polyT

end Groundwork.Prog
