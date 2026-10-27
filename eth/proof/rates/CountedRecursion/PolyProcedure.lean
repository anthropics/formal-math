/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PolyQueries
public import CountedRecursion.PolyRules
public import ExplicitCost.Poly
public import Printed.HandOver
import Mathlib.Tactic

/-! # The procedure has polynomial-time steps

One certificate for each of `rowWeight`, `rowPair`, `rowFactor`, for the four procedures as one
machine, and for `procedure c`. Each is written along the definition of the machine
(GridProcedures.lean) with the rules of PolyRules.lean; the plain functions are those of
PolyQueries.lean; `entryData` has its certificate from proof/rates/ExplicitCost/Poly.lean. -/

public section

namespace ExplicitCost

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

/-- W_a. -/
theorem rowWeight_poly : rowWeight.PolyTimeSteps :=
  ite_poly (by fun_prop) (prodRange_poly (by fun_prop) (askInt_poly (by fun_prop))) (const_poly 0)

/-- Ψ_{a,a'}. -/
theorem rowPair_poly : rowPair.PolyTimeSteps :=
  mapIn_poly (by fun_prop) (ite_poly (by fun_prop)
    (prodRange_poly (by fun_prop) (ite_poly isRect_polyT (askInt_poly (PolyT.inr' rectQuestion_polyT)) (const_poly 1))) (const_poly 0))

/-- f_{a,a'}. -/
theorem rowFactor_poly : rowFactor.PolyTimeSteps :=
  ite_poly (by fun_prop) (prodRange_poly (by fun_prop) (ite_poly isRect_polyT (askInt_poly (PolyT.inr' factorQuestion_polyT)) (const_poly 1))) (const_poly 0)

/-- The membership test, which answers yes to every string of g³λ bits, has polynomial-time steps. -/
theorem rowMem_poly (c : ℕ) : (gridProcsData c).mem.PolyTimeSteps := by
  -- `IsPolyQ.lift` finds the two certificates among the hypotheses
  have i0 := IsPolyT.const (α := Unit) true
  have i1 := IsPolyT.mapIn (M := (Stepped.const true : Stepped Unit Bool)) (f := fun _ : Parent × WQ => ()) (by fun_prop)
  exact ⟨QueryMachine.IsPolyQ.lift _⟩

/-- The four procedures as one machine. -/
theorem gridProcsData_poly (c : ℕ) : (gridProcsData c).answer.PolyTimeSteps :=
  answer_poly (gridProcsData c) (rowMem_poly c) rowWeight_poly rowPair_poly rowFactor_poly

/-- **The procedure for an entry has polynomial-time steps.** -/
theorem procedure_poly (c : ℕ) : (procedure c).PolyTimeSteps :=
  mapOut_poly (mapIn_poly (calleeInput_polyT c) (subst_poly entryPoly (gridProcsData_poly c))) (by fun_prop)

end ExplicitCost
