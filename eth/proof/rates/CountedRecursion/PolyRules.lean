/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.Answers
import Mathlib.Tactic

/-! # Rules for polynomial-time steps

proof/machines/QueryMachines/Poly.lean has a certificate (`IsPolyQ`, a class that holds the coding
of the states) for every construction. Here each of them is restated for the statement
`PolyTimeSteps` (there is a certificate), so that the certificate of a machine can be written along
its definition, one rule for each construction, with the plain functions left to `fun_prop`. Also:
`askInt`, `askList`, `readAs`. -/

public section

namespace ExplicitCost

open Groundwork QueryMachines QueryMachines.QueryMachine Printed

variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]

/-- A step machine with polynomial-time steps, seen as a machine that asks nothing. -/
theorem lift_poly {R : Stepped α β} (h : Nonempty (IsPolyT R)) : (QueryMachine.lift R : QueryMachine Q A α β).PolyTimeSteps := by
  obtain ⟨_⟩ := h
  exact ⟨IsPolyQ.lift R⟩

/-- One step that applies a polynomial-time function. -/
theorem ofFun_poly [HasSize α] [HasSize β] [Carried α] [Carried β] {f : α → β} (hf : PolyT f) : (QueryMachine.lift (Stepped.ofFun f) : QueryMachine Q A α β).PolyTimeSteps :=
  lift_poly ⟨IsPolyT.ofFun hf⟩

/-- A single query, computed in polynomial time from the input. -/
theorem query_poly [HasSize α] [HasSize A] [Carried α] [Carried A] {h : α → Q} (hh : PolyT h) : (QueryMachine.query h : QueryMachine Q A α A).PolyTimeSteps := ⟨IsPolyQ.query hh⟩

/-- Queries rewritten by a polynomial-time function. -/
theorem mapAsk_poly {h : Q → Q'} (hh : PolyT h) {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) : (QueryMachine.mapAsk h M).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.mapAsk hh M⟩

/-- A polynomial-time function applied to the input. -/
theorem mapIn_poly {g : α → β} (hg : PolyT g) {M : QueryMachine Q A β γ} (hM : M.PolyTimeSteps) : (QueryMachine.mapIn g M).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.mapIn hg M⟩

/-- A polynomial-time function applied to the result. -/
theorem mapOut_poly {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) {g : β → γ} (hg : PolyT g) : (QueryMachine.mapOut M g).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.mapOut M hg⟩

/-- One machine after the other. -/
theorem bind_poly [HasSize α] [Carried α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (QueryMachine.bind M N).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  obtain ⟨_⟩ := hN
  exact ⟨IsPolyQ.bind M N⟩

/-- A choice between two machines by a polynomial-time function of the input. -/
theorem branch_poly {sel : α → α₁ ⊕ α₂} (hs : PolyT sel) {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} (h₁ : M₁.PolyTimeSteps) (h₂ : M₂.PolyTimeSteps) :
    (QueryMachine.branch sel M₁ M₂).PolyTimeSteps := by
  obtain ⟨_⟩ := h₁
  obtain ⟨_⟩ := h₂
  exact ⟨IsPolyQ.branch M₁ M₂ hs⟩

/-- A choice by a polynomial-time test. -/
theorem ite_poly {p : α → Bool} (hp : PolyT p) {M N : QueryMachine Q A α β} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (QueryMachine.ite p M N).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  obtain ⟨_⟩ := hN
  exact ⟨IsPolyQ.ite hp M N⟩

/-- A constant. -/
theorem const_poly [HasSize α] [HasSize β] [Carried α] [Carried β] (b : β) : (QueryMachine.const b : QueryMachine Q A α β).PolyTimeSteps := ⟨IsPolyQ.const b⟩

/-- The loop over a range, if the range, the update and the start are polynomial-time. -/
theorem foldRange_poly [HasSize α] [Carried α] [HasSize γ] [Carried γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} (hN : PolyT N) (hM : M.PolyTimeSteps)
    (hg : PolyT fun p : γ × ℕ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : (QueryMachine.foldRange N M g c₀).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.foldRange M hN hg hc⟩

/-- The sum over a range. -/
theorem sumRange_poly [HasSize α] [Carried α] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) ℤ} (hN : PolyT N) (hM : M.PolyTimeSteps) : (QueryMachine.sumRange N M).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.sumRange M hN⟩

/-- The product over a range. -/
theorem prodRange_poly [HasSize α] [Carried α] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) ℤ} (hN : PolyT N) (hM : M.PolyTimeSteps) : (QueryMachine.prodRange N M).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  exact ⟨IsPolyQ.prodRange M hN⟩

/-- Queries answered by a machine with query access. -/
theorem subst_poly [HasSize C] [Enc C] [Carried C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (M.subst N).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  obtain ⟨_⟩ := hN
  exact ⟨subst_isPolyQ M N⟩

/-- Answers read by a polynomial-time function. -/
theorem readAs_poly {r : A' → A} (hr : PolyT r) {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) : (readAs r M).PolyTimeSteps := readAsPoly _ _ _ _ _ r M hr hM

/-- An answer read as an integer. -/
theorem asInt_polyT : PolyT asInt :=
  (by fun_prop : PolyT fun a : Ans => a.elim (fun v => v) fun _ => (0 : ℤ)).congr fun a => by cases a <;> rfl

/-- An answer read as a list of integers. -/
theorem asList_polyT : PolyT asList :=
  (by fun_prop : PolyT fun a : Ans => a.elim (fun _ => ([] : List ℤ)) fun l => l).congr fun a => by cases a <;> rfl

/-- One query, its answer read as an integer. -/
theorem askInt_poly [HasSize α] [Carried α] {h : α → Q} (hh : PolyT h) : (askInt h).PolyTimeSteps := mapOut_poly (query_poly hh) asInt_polyT

/-- One query, its answer read as a list of integers. -/
theorem askList_poly [HasSize α] [Carried α] {h : α → Q} (hh : PolyT h) : (askList h).PolyTimeSteps := mapOut_poly (query_poly hh) asList_polyT

end ExplicitCost
