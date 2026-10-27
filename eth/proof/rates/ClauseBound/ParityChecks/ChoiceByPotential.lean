/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.Martingale
public import ClauseBound.ParityChecks.Start
public import ClauseBound.ParityChecks.Structure
public import ClauseBound.ParityChecks.Approx

/-! # The choice of the checks by conditional expectations: all statements together

`stepTwo` proves `ParityChecks.ChoiceByPotential` of ParityChecksStatement.lean: it puts together
the theorems on one decision (Martingale.lean), on the sign, the start and the passage from one
check to the next
(Start.lean), on what a potential below 1 gives (Structure.lean) and on the truncated potential
(Approx.lean). -/

public section

namespace ClauseBound.ParityChecks

/-- The choice of the checks by conditional expectations (`ParityChecks.ChoiceByPotential`): a
variant of Step 2 of Appendix D that chooses the checks by a potential of four terms instead of by
Lemma 13. Here are its mathematical statements, without the program that carries it out. -/
theorem stepTwo : _root_.ParityChecks.ChoiceByPotential where
  nonneg := Start.nonneg
  five_eighths := Start.five_eighths
  start := Start.start
  martingale := Martingale.martingale
  boundary := Start.boundary
  structure_ := fun X E _ _ _ V nb r j Λ D hnb hE hs hU => Structure.structure_ V nb r j Λ D (Start.nonneg X E V nb r j Λ D hnb) hnb hE hs hU
  final := fun X E _ _ _ V nb r Λ hnb hs hU => Structure.final V nb r Λ (Start.nonneg X E V nb r (r - 1) Λ ∅ hnb) hs hU
  approx := fun _ _ _ _ _ => Approx.approx
  compute := fun _ _ _ _ _ => Approx.compute
  abs_le := fun _ _ _ _ _ => Approx.abs_le

end ClauseBound.ParityChecks
