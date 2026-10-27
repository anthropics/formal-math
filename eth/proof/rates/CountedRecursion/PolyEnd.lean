/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RecursionDefs
public import CountedRecursion.PolyProcedure
public import CountedRecursion.PolySolver
import Mathlib.Tactic

/-! # The recursion has polynomial-time steps

`recursionPolyFrom : RecursionPolyFrom`: the tower of the solver and the procedure.
`recursionPoly_of`: `RecursionPoly` from the certificate of the procedure of the lemma on groupings
up to its call (the first half of `GroupingPoly`). `recursionWithPoly_of`: `RecursionWithPoly` from
the fact that `recursion c x₀` has polynomial-time steps for all `c x₀`. -/

public section

namespace ExplicitCost

open Groundwork QueryMachines Printed

/-- `RecursionPoly`, given the certificate of `groupingCall`. -/
theorem recursionPoly_of (hG : groupingCall.PolyTimeSteps) : RecursionPoly := fun c x₀ => ⟨solver_poly hG c x₀, procedure_poly c⟩

/-- `RecursionPolyFrom`. -/
theorem recursionPolyFrom : RecursionPolyFrom := fun hT hR c x₀ => hT _ _ _ _ _ _ (hR c x₀).1 (hR c x₀).2

/-- A machine with the queries to the pieces answered by an algorithm with polynomial-time steps. -/
theorem withAlgorithm_poly {Q α β : Type} [HasSize Q] [Enc Q] [Carried Q] [Enc α] [Enc β] {M : QueryMachine (Q ⊕ PieceQuery) Ans α β} {Alg : Stepped PieceQuery Ans} (hM : M.PolyTimeSteps)
    (hA : Nonempty (IsPolyT Alg)) : (PiecesCounted.withAlgorithm M Alg).PolyTimeSteps :=
  mapIn_poly (by fun_prop) (subst_poly hM (branch_poly (by fun_prop) (query_poly PolyT.id') (lift_poly hA)))

/-- `RecursionWithPoly`, given that the recursion has polynomial-time steps. -/
theorem recursionWithPoly_of (h : ∀ c x₀ : ℕ, (recursion c x₀).PolyTimeSteps) : RecursionWithPoly := fun c x₀ Alg hA =>
  have h1 : (recursionWith c x₀ Alg).PolyTimeSteps := withAlgorithm_poly (h c x₀) hA
  ⟨h1, mapOut_poly (mapIn_poly (by fun_prop) (readAs_poly (by fun_prop) h1)) asInt_polyT⟩

/-- `RecursionWithPolyFrom`. -/
theorem recursionWithPolyFrom : RecursionWithPolyFrom := recursionWithPoly_of

end ExplicitCost
