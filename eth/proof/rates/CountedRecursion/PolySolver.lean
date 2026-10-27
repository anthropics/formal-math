/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PolySolverData
public import CountedRecursion.PolyRules
public import CountedRecursion.Numbers
public import ToTuring.Poly.Brute
import Mathlib.Tactic

/-! # The solver has polynomial-time steps

One certificate for each machine of SolverDefs.lean, written along its definition with the rules of
PolyRules.lean. The procedure of the lemma on groupings up to its call (`groupingCall`) has its
certificate from the first half of `GroupingPoly`; here it is a hypothesis. -/

public section

namespace ExplicitCost

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

/-- Z_ι. -/
theorem patternValue_poly (hG : groupingCall.PolyTimeSteps) (c : ℕ) : (patternValue c).PolyTimeSteps :=
  mapIn_poly (by fun_prop) (subst_poly hG (askInt_poly (by fun_prop)))

/-- The numbers c^row_i or c^col_i. -/
theorem capsLoop_poly {σ : Type} [HasSize σ] [Enc σ] [Carried σ] (tr : Bool) {lamU : σ → List Unit} {idx : σ → List ℤ} (h1 : PolyT lamU) (h2 : PolyT idx) : (capsLoop tr lamU idx).PolyTimeSteps :=
  foldRange_poly (by fun_prop) (askInt_poly (by fun_prop)) (by fun_prop) (by fun_prop)

/-- The sum over the patterns and the division. -/
theorem sumAndDivide_poly (hG : groupingCall.PolyTimeSteps) (c : ℕ) : (sumAndDivide c).PolyTimeSteps :=
  bind_poly (sumRange_poly nPatterns_polyT (patternValue_poly hG c)) (ofFun_poly divide_polyT)

/-- The loop for K and g, on ℓ − 1. -/
theorem numbersOn_poly (x₀ : ℕ) : Nonempty (IsPolyT (Stepped.mapIn (fun a : Head => a.1.tail) (numbersM x₀))) := by
  obtain ⟨_⟩ := numbersPoly x₀
  exact ⟨IsPolyT.mapIn (M := numbersM x₀) (f := fun a : Head => a.1.tail) (by fun_prop)⟩

/-- The solver at a level ℓ ≥ 1. -/
theorem levelSolver_poly (hG : groupingCall.PolyTimeSteps) (c x₀ : ℕ) : (levelSolver c x₀).PolyTimeSteps :=
  bind_poly (lift_poly (numbersOn_poly x₀)) (bind_poly (askList_poly (by fun_prop)) (bind_poly (askInt_poly (by fun_prop))
    (bind_poly (capsLoop_poly false (by fun_prop) (by fun_prop)) (bind_poly (capsLoop_poly true (by fun_prop) (by fun_prop)) (sumAndDivide_poly hG c)))))

/-- Brute force. (The same stands in proof/threesat/Printed/Achievable.lean; it is said again here
so that the certificates stand on `Printed.Programs` alone.) -/
theorem brute_poly (K : ℕ) : (bruteMachine K).PolyTimeSteps := by
  have hl : Unary fun c : List Unit × List Unit => c.1.length := Unary.of_length (by fun_prop)
  exact sumRange_poly (bruteBound_polyT K hl) (prodRange_poly (by unfold Function.const; fun_prop)
    (mapIn_poly (bruteQuery_polyT K hl (dflt := nilC) (by unfold nilC; fun_prop)) (query_poly (by unfold toTable; fun_prop))))

/-- The solver at the level 0. -/
theorem baseSolver_poly (x₀ : ℕ) : (baseSolver x₀).PolyTimeSteps :=
  mapIn_poly (by fun_prop) (readAs_poly asInt_polyT (mapAsk_poly (by fun_prop) (brute_poly (2 ^ x₀))))

/-- **The solver has polynomial-time steps.** -/
theorem solver_poly (hG : groupingCall.PolyTimeSteps) (c x₀ : ℕ) : (solver c x₀).PolyTimeSteps :=
  mapOut_poly (mapIn_poly PolyT.id'.fst (ite_poly (by fun_prop) (baseSolver_poly x₀) (levelSolver_poly hG c x₀))) (by fun_prop)

end ExplicitCost
