/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
public import CountKSatRate.Walk
import all PaddedDescent.F.Top

/-! # The walk that adds up, for arbitrary thresholds

This file proves `StWalkSG` of proof/sparsification/StepSparsify/Defs.lean.
`stWalkSG`: `walkSG`, which makes one round for each unit of the pad and cuts off states that are
too long, returns the sum of the values of the leaves if the pad is long enough, for any thresholds
θ;
the lemma `roundS_iterate_of_le` that the proof uses holds for every step function. -/

public section

namespace StepSparsify

open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate UniformInK

/-- If the procedure has stopped at every node that is listed when the paths are cut after d steps,
the pad has at least 2·(number of these nodes) − 1 units and the word of every state of the walk
fits under the pad, then `walkSG` returns the sum of the
values of these nodes. -/
theorem stWalkSG : StWalkSG := by
  intro θ k pad val r d hd hlen hst
  unfold walkSG
  rw [Top.foldl_capped_eq_iterate (cap pad ([], 0)) (roundS (stepC θ k) val) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], 0) (fun i _ => hst i),
    roundS_iterate_of_le (stepC θ k) val d r hd pad.length (by omega)]

end StepSparsify
