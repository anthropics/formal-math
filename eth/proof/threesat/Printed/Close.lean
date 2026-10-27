/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs
public import QueryMachines.Comb
import Mathlib.Tactic

/-! # The named machines, with the oracle built in, are the step machines of this development -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

variable {Q A C : Type}

/-- One entry W̃_γ(Θ): with the oracle built in, `tableQ` is `Eight.ViaGrouping.tableM` on the
procedures with the oracle built in. -/
theorem tableQ_close [HasSize C] (K g : ℕ) (Np : ProcsQ Q A C) (O : Q → Option A) : (tableQ K g Np).close O = tableM K g (Np.close O) := by
  simp only [tableQ, termQ, wQ, psiQ, fQ, close_ite, close_sumRange, close_prodRange, close_gated, close_mapIn, close_const]
  rfl

/-- The weight of a row: with the tables built in, `sideWQ` is `Groundwork.Prog.sideWP`. -/
theorem sideWQ_close [HasSize C] (g : ℕ) (tr : Bool) (lam : C → ℕ) (O : TableQuery → Option ℤ) :
    (sideWQ g tr lam).close O = sideWP g tr lam ((askTable : QueryMachine TableQuery ℤ (C × IQ) ℤ).close O) := by
  simp only [sideWQ, close_ite, close_prodRange, close_mapIn, close_const]
  rfl

/-- Brute force: with the tables built in, `bruteMachine` is `Groundwork.brute`. -/
theorem bruteMachine_close (K : ℕ) (O : TableQuery → Option ℤ) :
    (bruteMachine K).close O = brute K (fun c : List Unit × List Unit => c.1.length) nilC ((askTable : QueryMachine TableQuery ℤ ((List Unit × List Unit) × IQ) ℤ).close O) := by
  simp only [bruteMachine, close_sumRange, close_prodRange, close_mapIn]
  rfl

/-- The four procedures as one machine: `close` goes to each of them. -/
theorem answer_close (Np : ProcsQ Q A C) (O : Q → Option A) : Np.answer.close O = answerOf (Np.close O) := by
  simp only [ProcsQ.answer, close_branch, close_mapOut]
  rfl

/-- The two networks of ι: with the tables built in, `gridProcs` is `Eight.ViaGrouping.levelProcs`,
except that its bound `B` is B₁ = gB + g²λ + 1 of the proof of Proposition 3. -/
theorem gridProcs_close (g : ℕ) (tr : Bool) (O : TableQuery → Option ℤ) :
    (gridProcs g tr).close O = { levelProcs g tr (gridPsi g tr) (fun c : List Unit × List Unit => c.1.length) (askTable.close O) with
      B := fun c => g * c.1.2.length + g ^ 2 * c.1.1.length + 1 } := by
  simp only [ProcsQ.close, gridProcs, sideWQ_close, close_lift]
  rfl

/-- A machine for networks run on procedures that may ask: with the oracle built in, its queries are
answered by the procedures with the oracle built in. -/
theorem networkOn_close [HasSize C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) (O : Q → Option A) :
    (networkOn g NM Np).close O = networkOnSteps g NM (Np.close O) := by
  simp only [networkOn, close_mapIn, close_subst, answer_close]
  rfl

/-- The algorithm of the proof of Proposition 3: with the tables built in, it is the loop of
`Eight.ViaGrouping.levelAlgP` over the machine `groupingMachine` of Lemma 1. -/
theorem levelMachine_close (K g : ℕ) (M : CliqueMachine) (O : TableQuery → Option ℤ) :
    (levelMachine K g M).close O = Stepped.bind
      (Stepped.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
        (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g (groupingMachine K g M) ((gridProcs g false).close O))
          (networkOnSteps g (groupingMachine K g M) ((gridProcs g true).close O))))
      (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) := by
  simp only [levelMachine, close_bind, close_sumRange, close_ite, networkOn_close, close_lift]

end Printed

