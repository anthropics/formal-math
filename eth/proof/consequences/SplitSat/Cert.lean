/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import WidthK.Top.Poly
import SparsifyWidthK.Poly.Sparsify
import CountKSat.InOut

/-! # Section 7, proof of Corollary 5: the steps of the reduction are polynomial time

No sentence of the paper stands behind this file; the paper counts operations. `stReduceCert` proves
`SplitSat.StReduceCert`. The proof follows `Groundwork.Prog.SatTopK.isPolyT_satMK`
(proof/consequences/WidthK/Top/Poly.lean). Its pieces: splitting the long clauses is polynomial time
(`Eight.Width.widthP_polyT`), one step of the tree is (`WidthK.Prog.certStep`), the reader of the
input is (`CountKSat.stCertDecU`). -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight.Width

/-- The step of the tree with n carried along is polynomial time if the step of the tree is. -/
theorem stepN_polyT {step : Fml → Option (Fml × Fml)} (hs : PolyT step) : PolyT (stepN step) := by
  unfold stepN
  fun_prop

/-- The steps of the reduction without its reader are polynomial time, if the step of the tree is
polynomial time and the steps of D are. -/
theorem reduceCore_polyTimeSteps {step : Fml → Option (Fml × Fml)} (hs : PolyT step) {D : StepMachine (List Unit × Fml) Bool} (hD : PolyTimeSteps D) :
    PolyTimeSteps (reduceCore step D) := by
  obtain ⟨h⟩ := hD
  have := IsPolyT.mapIn (M := D) widthP_polyT
  have := IsPolyT.walk (T := Stepped.mapIn widthP D) (step := stepN step) (root := fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml))
    (stepN_polyT hs) (by fun_prop)
  have : IsPolyT (Stepped.const false : Stepped (List Unit × Fml) Bool) := IsPolyT.const false
  exact ⟨IsPolyT.ite (M := (Stepped.const false : Stepped (List Unit × Fml) Bool))
    (N := Stepped.walk (stepN step) (fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml)) (Stepped.mapIn widthP D))
    (p := fun p : List Unit × Fml => hasNil p.2) (by have := hasNil_polyT; fun_prop)⟩

/-- The steps of the reduction are polynomial time if those of D are: the statement
`SplitSat.StReduceCert`. -/
theorem stReduceCert : StReduceCert := fun k τ D hD => by
  obtain ⟨h⟩ := reduceCore_polyTimeSteps (certStep (thetaU τ) k) hD
  exact ⟨IsPolyT.mapIn (stCertDecU k)⟩

end SplitSat
