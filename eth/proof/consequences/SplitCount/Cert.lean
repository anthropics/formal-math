/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import Occ.Main
import CountKSat.Walk
import CountKSat.Poly
import ToTuring.Poly.Sat

/-! # The steps of the procedure of proof/consequences/SplitCount/ are polynomial time

A bound on the number of steps of a machine cut into steps says something only if each step takes
polynomial time (`PolyTimeSteps`). Here: the functions `stepPlain step`, `rootPlain`, `leafPlain`
are polynomial-time; `timesFreeAfter Cnt` has polynomial-time steps if Cnt has (the factor 2^{n'}:
`Occ.stTimesFreeCert`);
`engineBy step D` has them if `step` is polynomial-time and D has them (the width reduction:
`Eight.Width.widthP_polyT`; the walk that adds up: `CountKSat.isPolyT_walkSum`). The proof follows
`GraphProblems.isPolyT_engine` (proof/consequences/GraphProblems/Engine.lean). -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat Eight.Width Occ

/-- The step of the tree with n handed down is polynomial-time if the step of the tree is. -/
theorem stepPlain_polyT {step : CNode → Option (CNode × CNode)} (hs : PolyT step) : PolyT (stepPlain step) := by
  unfold stepPlain
  fun_prop

/-- The root with the empty side list is computed in polynomial time. -/
theorem rootPlain_polyT : PolyT rootPlain := by
  unfold rootPlain
  fun_prop

/-- What is counted at a node is computed in polynomial time. -/
theorem leafPlain_polyT : PolyT leafPlain := by
  unfold leafPlain leafF
  fun_prop

/-- The steps of `timesFreeAfter Cnt` are polynomial time if those of Cnt are; the steps of
`engineBy step D` are polynomial time if `step` is polynomial-time and the steps of D are polynomial
time. -/
theorem stCert : StCert := by
  constructor
  · rintro Cnt ⟨hC⟩
    have := hC
    have := IsPolyT.mapIn (M := Cnt) (f := (Prod.snd : List Unit × Fml → Fml)) PolyT.id'.snd
    have := IsPolyT.ofFun stTimesFreeCert
    exact ⟨IsPolyT.bind (M := Stepped.mapIn (Prod.snd : List Unit × Fml → Fml) Cnt) (N := Stepped.ofFun timesFree)⟩
  · rintro step D hs ⟨hD⟩
    have := hD
    have := IsPolyT.mapIn (M := D) widthP_polyT
    have := IsPolyT.mapIn (M := Stepped.mapIn widthP D) leafPlain_polyT
    have := isPolyT_walkSum (T := Stepped.mapIn leafPlain (Stepped.mapIn widthP D)) (stepPlain_polyT hs) rootPlain_polyT
    have : IsPolyT (Stepped.const 0 : Stepped (List Unit × Fml) ℕ) := IsPolyT.const 0
    have := IsPolyT.ite (M := (Stepped.const 0 : Stepped (List Unit × Fml) ℕ))
      (N := walkSum (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D))) (p := fun p => hasNil p.2)
      (by have := hasNil_polyT; fun_prop)
    have := IsPolyT.ofFun Poly.outW_polyT
    exact ⟨IsPolyT.bind (M := Stepped.ite (fun p : List Unit × Fml => hasNil p.2) (Stepped.const 0)
      (walkSum (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)))) (N := Stepped.ofFun outW)⟩

end SplitCount
