/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmVariables.Defs
import ThmVariables.Bound
import ThmVariables.PartA

/-! # Theorem D (a) with the printed hypothesis, for every machine that runs the named algorithm

The step from counted operations to the padding string is
`QueryMachines.Bridge.SolverOfMachineLevels`, a hypothesis here: for every machine E with query
access as in the hypothesis of Theorem D (a), with any certificate that its steps are
polynomial-time, the NAMED solver `solverOfMachine E num C₀` is polynomial-time and has a sequence Q
of levels for K_ℓ and e′_ℓ = `cutNumber K num ℓ`, and the level is picked by
the named program `pickOf kf (K 0)`.
* `solverFromMachine_of`: the form that forgets the names follows.
* `partAForEveryMachineFrom`: Theorem D (a) for every machine that computes `RecursionToBound.count`
  (`RecursionToBound.ThmVariablesAForEveryMachine`, a hypothesis here) is applied to this solver, to
  Q and to the fraction `cutFraction num` (`numberBetween_cut`); `Q.pick` is rewritten to the named
  program; the bound at e′_ℓ is the bound at e_ℓ with twice the constant (`conclusion_of_cut`).
* `partAFromEveryMachine`: the form that says that there is a machine (`PartA`) follows, at n₁ = n₀. -/

public section

namespace ThmVariables

open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms

/-- What the proof of `PartA` through the padding string takes from the step from counted operations
to the padding string (`SolverFromMachine`) follows from the statement on the named solver
(`QueryMachines.Bridge.SolverOfMachineLevels`). -/
theorem solverFromMachine_of (h : SolverOfMachineLevels) : SolverFromMachine := by
  intro K e C₀ kf num E hyp
  obtain ⟨inst⟩ := hyp.steps
  obtain ⟨hP, Q, -, hK, -⟩ := h E K e C₀ kf num hyp.solves hyp.levels hyp.computesK hyp.number
  exact ⟨_, inferInstance, solverOfMachine E num C₀, 2 * C₀ + 1, Q, hP, hK⟩

/-- Theorem D (a) for every machine that runs the named algorithm on the named solver, from the
statement on the named solver and Theorem D (a) for every machine that computes the function of
Steps 1 to 5. -/
theorem partAForEveryMachineFrom : PartAForEveryMachineFrom := by
  intro hB hVariablesA K e C₀ kf num E _ hyp
  obtain ⟨hP, Q, -, hK, hpick⟩ := hB E K e C₀ kf num hyp.solves hyp.levels hyp.computesK hyp.number
  obtain ⟨n₀, hn₀⟩ := hVariablesA _ (solverOfMachine E num C₀) (cutNumber K num) (2 * C₀ + 1) Q hP (cutFraction num) (numberBetween_cut Q hyp.number.1 hK)
  refine ⟨n₀, fun n₁ hn₁ => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n₁ hn₁
  rw [hpick] at h1 h2
  refine ⟨h1, fun M q hM => ?_⟩
  obtain ⟨C', hC'⟩ := h2 M q hM
  exact ⟨2 * C', conclusion_of_cut Q hyp.levels hyp.number hK hC'⟩

/-- Theorem D (a) in the form that says that there is a machine (`PartA`) follows from the form for
every machine (`PartAForEveryMachine`). -/
theorem partAFromEveryMachine : PartAFromEveryMachine := by
  intro h K e C₀ kf num E hyp
  obtain ⟨inst⟩ := hyp.steps
  obtain ⟨n₀, hn₀⟩ := h K e C₀ kf num E hyp
  obtain ⟨⟨M, q, hf, hM⟩, hall⟩ := hn₀ n₀ le_rfl
  obtain ⟨C', hC'⟩ := hall M q hM
  exact ⟨M, C', hf, hC'⟩

end ThmVariables
