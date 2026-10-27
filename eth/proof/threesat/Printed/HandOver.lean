/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs
public import QueryMachines.Poly
import Mathlib.Tactic

/-! # A machine for networks on a network given by procedures: polynomial-time steps

Definition 2(iii): «an algorithm receives P, B and the numbers P_a, c_{a,b} as input». `networkOn`
and `networkOnSteps` (Programs.lean) write this input down from the numbers that the procedures give
(`inputOf`) and answer each query by running a procedure (`ProcsQ.answer`, `answerOf`).
This file shows that all of this is computed in polynomial time if the numbers are given in unary
and the procedures have polynomial-time steps. -/

public section

namespace Printed

open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

variable {Q A C : Type}

/-- The input of Definition 2(iii) is written down in polynomial time from numbers given in unary.
The number g of nodes is a constant. -/
theorem inputOf_polyT [Enc C] (g : ℕ) {P B : C → ℕ} {len : C → ℕ → ℕ} {cap : C → ℕ → ℕ → ℕ} (hP : Unary P) (hB : Unary B)
    (hl : Unary fun p : C × ℕ => len p.1 p.2) (hc : Unary fun p : C × ℕ × ℕ => cap p.1 p.2.1 p.2.2) :
    PolyT fun c => inputOf g (P c) (B c) (len c) (cap c) := by
  have h1 : PolyT fun c => List.replicate (P c) () := hP
  have h2 : PolyT fun c => List.replicate (B c) () := hB
  have h3 : PolyT fun p : C × ℕ => List.replicate (len p.1 p.2) () := hl
  have h4 : PolyT fun p : (C × ℕ) × ℕ => List.replicate (cap p.1.1 p.1.2 p.2) () :=
    PolyT.comp (g := fun p : (C × ℕ) × ℕ => (p.1.1, p.1.2, p.2)) hc (by fun_prop)
  unfold inputOf unary
  fun_prop

/-- (c, x or y) ↦ (c, x) or (c, y) is polynomial-time. -/
theorem dist_polyT [Enc C] {X Y : Type} [Enc X] [Enc Y] : PolyT (dist : C × (X ⊕ Y) → (C × X) ⊕ (C × Y)) :=
  (by fun_prop : PolyT fun p : C × (X ⊕ Y) => p.2.elim (fun x => (.inl (p.1, x) : (C × X) ⊕ (C × Y))) fun y => .inr (p.1, y)).congr
    fun p => by rcases p with ⟨c, x | y⟩ <;> rfl

/-- yes is 1 and no is 0. -/
theorem bit_polyT : PolyT fun b : Bool => if b = true then (1 : ℤ) else 0 := by fun_prop

/-- The four procedures as one step machine. -/
theorem answerOf_poly [Enc C] (Np : Procs C) (hm : Nonempty (IsPolyT Np.mem)) (hW : Nonempty (IsPolyT Np.W)) (hΨ : Nonempty (IsPolyT Np.Ψ)) (hf : Nonempty (IsPolyT Np.f)) :
    Nonempty (IsPolyT (answerOf Np)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hW⟩ := hW
  obtain ⟨hΨ⟩ := hΨ
  obtain ⟨hf⟩ := hf
  have i1 : IsPolyT (Stepped.mapOut Np.mem fun b => if b = true then (1 : ℤ) else 0) := IsPolyT.mapOut bit_polyT
  have i2 : IsPolyT (Stepped.branch dist Np.Ψ Np.f) := IsPolyT.branch dist_polyT
  have i3 : IsPolyT (Stepped.branch dist Np.W (Stepped.branch dist Np.Ψ Np.f)) := IsPolyT.branch dist_polyT
  exact ⟨IsPolyT.branch dist_polyT⟩

/-- The four procedures as one machine with query access. -/
theorem answer_poly [Enc Q] [Enc A] [Enc C] (Np : ProcsQ Q A C) (hm : Np.mem.PolyTimeSteps) (hW : Np.W.PolyTimeSteps) (hΨ : Np.Ψ.PolyTimeSteps) (hf : Np.f.PolyTimeSteps) :
    Np.answer.PolyTimeSteps := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hW⟩ := hW
  obtain ⟨hΨ⟩ := hΨ
  obtain ⟨hf⟩ := hf
  have i1 := QueryMachine.IsPolyQ.mapOut Np.mem bit_polyT
  have i2 := QueryMachine.IsPolyQ.branch (sel := dist) Np.Ψ Np.f dist_polyT
  have i3 := QueryMachine.IsPolyQ.branch (sel := dist) Np.W (QueryMachine.branch dist Np.Ψ Np.f) dist_polyT
  exact ⟨QueryMachine.IsPolyQ.branch _ _ dist_polyT⟩

/-- A machine for networks with polynomial-time steps, on a network given by step machines with
polynomial-time steps and numbers in unary. -/
theorem networkOnSteps_poly [HasSize C] [Enc C] [Carried C] (g : ℕ) (NM : NetMachine) (Np : Procs C) (hN : NM.PolyTimeSteps) (h : Np.Keeps) (hP : Unary Np.P) (hB : Unary Np.B) :
    Nonempty (IsPolyT (networkOnSteps g NM Np)) := by
  obtain ⟨hN⟩ := hN
  obtain ⟨ha⟩ := answerOf_poly Np h.mem h.W h.Ψ h.f
  have i1 := QueryMachine.plug_isPolyT NM (answerOf Np)
  have h0 := inputOf_polyT g hP hB h.len h.cap
  exact ⟨IsPolyT.mapIn (M := NM.plug (answerOf Np)) (f := fun c => (c, inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c))) (by fun_prop)⟩

/-- The same on a network given by procedures that have query access of their own. -/
theorem networkOn_poly [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) (hN : NM.PolyTimeSteps)
    (hP : Unary Np.P) (hB : Unary Np.B) (hl : Unary fun p : C × ℕ => Np.len p.1 p.2) (hc : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2)
    (hm : Np.mem.PolyTimeSteps) (hW : Np.W.PolyTimeSteps) (hΨ : Np.Ψ.PolyTimeSteps) (hf : Np.f.PolyTimeSteps) : (networkOn g NM Np).PolyTimeSteps := by
  obtain ⟨hN⟩ := hN
  obtain ⟨ha⟩ := answer_poly Np hm hW hΨ hf
  have i1 := QueryMachine.subst_isPolyQ NM Np.answer
  have h0 := inputOf_polyT g hP hB hl hc
  exact ⟨QueryMachine.IsPolyQ.mapIn (g := fun c => (c, inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c))) (by fun_prop) (NM.subst Np.answer)⟩

end Printed
