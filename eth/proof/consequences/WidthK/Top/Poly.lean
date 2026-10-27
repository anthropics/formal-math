/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import StepMachines.Prog.Sat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import StepMachines.Math.SparsifyCount
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import ToTuring.Poly.Spec
public import ToTuring.Poly.Brute
public import ToTuring.Poly.NetFun
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
public import ToTuring.Poly.GridSide
public import ToTuring.Poly.Count
public import ToTuring.Poly.Sat
public import WidthK.Top.Sat

/-! The machine `satMK` is `IsPolyT` (init, step and out are polynomial-time) if the decoder, the
sparsification step and the root function are
polynomial-time and the machine that counts the solutions of a sparse formula is `IsPolyT`.
A lemma used for it: reading the formula off the decoder's output is polynomial-time if the decoder
is (`decF_polyT`). -/

@[expose] public section

namespace Groundwork.Prog.SatTopK

open Stepped

/-- Reading the formula off the decoder's output is polynomial-time if the decoder is. -/
theorem decF_polyT {dec : List Bool → ℕ × Fml} (hd : PolyT dec) : PolyT (decF dec) := by unfold decF; fun_prop

/-- `satMK dec step root M` is `IsPolyT` if `dec`, `step`, `root` are polynomial-time and `M` is
`IsPolyT`. -/
@[instance_reducible] def isPolyT_satMK {dec : List Bool → ℕ × Fml} {step : Fml → Option (Fml × Fml)} {root : Fml → Fml}
    (hd : PolyT dec) (hs : PolyT step) (hr : PolyT root) {M : Stepped Fml ℤ} [IsPolyT M] :
    IsPolyT (satMK dec step root M) :=
  haveI := IsPolyT.mapOut (M := M) posZ_polyT
  haveI := IsPolyT.walk (T := Stepped.mapOut M posZ) (step := step) (root := root) hs hr
  haveI : IsPolyT (Stepped.const false : Stepped Fml Bool) := IsPolyT.const false
  haveI := IsPolyT.ite (M := (Stepped.const false : Stepped Fml Bool))
    (N := Stepped.walk step root (Stepped.mapOut M posZ)) hasNil_polyT
  IsPolyT.mapIn (decF_polyT hd)

end Groundwork.Prog.SatTopK
