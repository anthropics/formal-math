/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces
import all PaddedDescent.F.Top

/-! # The walk that adds up, in rounds

`proof/machines/StepMachines/Math/SparsifyTree.lean` walks the tree of a step function depth first,
in rounds: `round` lists the leaves, `roundB` keeps only whether some leaf passed a
test. `roundS` keeps only the sum of the values of the leaves. This file shows that `roundS` follows
`round`, that the sum is complete once the stack is empty, and that
`walkS`, which makes one round for each unit of the pad and cuts off states that are too long,
returns the sum over the leaves if the pad is long enough. The last proof
is that of `walk` in `proof/rates/PaddedDescent/F/Top.lean`. -/

namespace CountKSatRate

open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)

/-- The state of the summing walk after i rounds: the stack of the plain walk, and the sum of the
values of the leaves that the plain walk has listed. -/
public theorem roundS_iterate {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (i : ℕ) (st out : List σ) :
    (roundS step val)^[i] (st, (out.map val).sum) =
      (((Sparsify.round step)^[i] (st, out)).1, (((Sparsify.round step)^[i] (st, out)).2.map val).sum) := by
  induction i generalizing st out with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    obtain _ | ⟨s, r⟩ := st
    · exact ih [] out
    · cases h0 : step s with
      | none =>
        have e1 : roundS step val (s :: r, (out.map val).sum) = (r, ((s :: out).map val).sum) := by
          simp [roundS, h0, Nat.add_comm]
        have e2 : Sparsify.round step (s :: r, out) = (r, s :: out) := by simp [Sparsify.round, h0]
        rw [e1, e2]; exact ih r (s :: out)
      | some lh =>
        have e1 : roundS step val (s :: r, (out.map val).sum) = (lh.1 :: lh.2 :: r, (out.map val).sum) := by
          simp [roundS, h0]
        have e2 : Sparsify.round step (s :: r, out) = (lh.1 :: lh.2 :: r, out) := by simp [Sparsify.round, h0]
        rw [e1, e2]; exact ih _ out

/-- After at least 2·(number of leaves) − 1 rounds the stack is empty and the number is the sum of
the values of the leaves. -/
public theorem roundS_iterate_of_le {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (R : ℕ) (hR : 2 * (leaves step d s).length - 1 ≤ R) :
    (roundS step val)^[R] ([s], 0) = ([], ((leaves step d s).map val).sum) := by
  have := roundS_iterate step val R [s] []
  rw [round_iterate_of_le step d s hd R hR] at this
  simpa [List.sum_reverse] using this

/-! ### The interface statements of `proof/consequences/CountKSatRate/Interfaces.lean` that this file proves -/

/-- `roundS_iterate`, as the interface states it. -/
public theorem stRoundS : StRoundS := fun _ step val i st out => roundS_iterate step val i st out

/-- `roundS_iterate_of_le`, as the interface states it. -/
public theorem stRoundSEnd : StRoundSEnd := fun _ step val d s hd R hR => roundS_iterate_of_le step val d s hd R hR

/-- If the pad has at least 2·(number of leaves) − 1 units and the word of every state of the walk
fits under the pad, then `walkS` returns the sum of the values of the leaves. -/
public theorem stWalkS : StWalkS := by
  intro k pad τ val r d hd hlen hst
  unfold walkS
  rw [Top.foldl_capped_eq_iterate (cap pad ([], 0)) (roundS (stepC (theta τ) k) val) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], 0) (fun i _ => hst i),
    roundS_iterate_of_le (stepC (theta τ) k) val d r hd pad.length (by omega)]

end CountKSatRate
