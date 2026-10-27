/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.CombDefs
public import QueryMachines.Runs

/-! # Building in the oracle commutes with every construction

The lemmas `close_…` say that building in the oracle (`close`) commutes with every construction of
proof/machines/QueryMachines/CombDefs.lean. So a machine built there, with the oracle built in, is
the step machine built in the same way from the parts with the oracle built in; and every bound
proved for such step machines is a bound on own steps plus queries (`StClose`). -/

public section

namespace Groundwork.Stepped

variable {α β : Type}

/-- Where g has a value, `ofOption g` returns it in one step. -/
theorem ofOption_runs [HasSize α] [HasSize β] {g : α → Option β} {a : α} {b : β} (h : g a = some b) :
    (ofOption g).Runs a 1 (max (size a) (size b) + 1) b :=
  .step rfl (by change size a + 1 ≤ _; omega) (by
    have e : (ofOption g).step (.inl a) = .inr b := by change (match g a with | some b => _ | none => _) = _; rw [h]
    rw [show (ofOption g).init a = .inl a from rfl, e]
    exact .halt rfl (by change size b + 1 ≤ _; omega))

end Groundwork.Stepped

namespace QueryMachines.QueryMachine

open Groundwork

variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}

/-- A step machine stays what it is. -/
@[simp] theorem close_lift (M : Stepped α β) (O : Q → Option A) : (lift M : QueryMachine Q A α β).close O = M := rfl

/-- A single query becomes one step that looks the answer up. -/
@[simp] theorem close_query [HasSize α] [HasSize A] (h : α → Q) (O : Q → Option A) :
    (query h : QueryMachine Q A α A).close O = Stepped.ofOption fun a => O (h a) :=
  stepped_eq (fun _ => rfl) (fun s => by rcases s with a | b <;> rfl) (fun s => by rcases s with a | b <;> rfl)

/-- Rewriting the queries is rewriting the oracle. -/
@[simp] theorem close_mapAsk (h : Q → Q') (M : QueryMachine Q A α β) (O : Q' → Option A) :
    (mapAsk h M).close O = M.close fun x => O (h x) :=
  stepped_eq (fun _ => rfl) (fun s => by
    simp only [mapAsk]
    cases M.ask s <;> rfl) (fun _ => rfl)

/-- `close` commutes with `mapIn`. -/
@[simp] theorem close_mapIn (g : α → β) (M : QueryMachine Q A β γ) (O : Q → Option A) :
    (mapIn g M).close O = Stepped.mapIn g (M.close O) := rfl

/-- `close` commutes with `mapOut`. -/
@[simp] theorem close_mapOut (M : QueryMachine Q A α β) (g : β → γ) (O : Q → Option A) :
    (mapOut M g).close O = Stepped.mapOut (M.close O) g := rfl

/-- `close` commutes with `bind`. -/
@[simp] theorem close_bind [HasSize α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) (O : Q → Option A) :
    (bind M N).close O = Stepped.bind (M.close O) (N.close O) :=
  stepped_eq (fun _ => rfl) (fun s => by
    rcases s with p | s
    · simp only [bind, Stepped.bind, close]
      cases M.out p.2 <;> simp only []
      cases M.ask p.2 <;> simp only []
      cases O _ <;> rfl
    · simp only [bind, Stepped.bind, close]
      cases N.ask s <;> simp only []
      cases O _ <;> rfl) (fun s => by rcases s with a | b <;> rfl)

/-- `close` commutes with the loop. -/
@[simp] theorem close_foldWhile [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : QueryMachine Q A τ β)
    (g : γ → τ → β → γ) (c₀ : α → γ) (O : Q → Option A) :
    (foldWhile start nxt M g c₀).close O = Stepped.foldWhile start nxt (M.close O) g c₀ :=
  stepped_eq (fun _ => rfl) (fun s => by
    rcases s with p | s
    · simp only [foldWhile, Stepped.foldWhile, close]
      cases M.out p.2.2 <;> simp only []
      · cases M.ask p.2.2 <;> simp only []
        cases O _ <;> rfl
      · rfl
    · rfl) (fun s => by rcases s with a | b <;> rfl)

/-- `close` commutes with `branch`. -/
@[simp] theorem close_branch (sel : α → α₁ ⊕ α₂) (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) (O : Q → Option A) :
    (branch sel M₁ M₂).close O = Stepped.branch sel (M₁.close O) (M₂.close O) :=
  stepped_eq (fun _ => rfl) (fun s => by
    rcases s with s | s
    · simp only [branch, Stepped.branch, close]
      cases M₁.ask s <;> simp only []
      cases O _ <;> rfl
    · simp only [branch, Stepped.branch, close]
      cases M₂.ask s <;> simp only []
      cases O _ <;> rfl) (fun s => by rcases s with a | b <;> rfl)

/-- `close` commutes with `both`. -/
@[simp] theorem close_both [HasSize α] [HasSize β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) (O : Q → Option A) :
    (both M N).close O = Stepped.both (M.close O) (N.close O) :=
  stepped_eq (fun _ => rfl) (fun s => by
    rcases s with p | p
    · simp only [both, Stepped.both, close]
      cases M.out p.2 <;> simp only []
      cases M.ask p.2 <;> simp only []
      cases O _ <;> rfl
    · simp only [both, Stepped.both, close]
      cases N.ask p.2 <;> simp only []
      cases O _ <;> rfl) (fun s => by rcases s with a | b <;> rfl)

/-- `close` commutes with `ite`. -/
@[simp] theorem close_ite (p : α → Bool) (M N : QueryMachine Q A α β) (O : Q → Option A) :
    (ite p M N).close O = Stepped.ite p (M.close O) (N.close O) := close_branch _ _ _ _

/-- A constant stays what it is. -/
@[simp] theorem close_const [HasSize α] [HasSize β] (b : β) (O : Q → Option A) :
    (const b : QueryMachine Q A α β).close O = Stepped.const b := rfl

/-- `close` commutes with `optBind`. -/
@[simp] theorem close_optBind [HasSize α] [HasSize β] (M : QueryMachine Q A α (Option ι)) (N : QueryMachine Q A (α × ι) β) (dflt : α → β) (O : Q → Option A) :
    (optBind M N dflt).close O = Stepped.optBind (M.close O) (N.close O) dflt := by
  simp only [optBind, Stepped.optBind, close_bind, close_branch, close_lift]

/-- `close` commutes with `foldRange`. -/
@[simp] theorem close_foldRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) β) (g : γ → ℕ → β → γ) (c₀ : α → γ) (O : Q → Option A) :
    (foldRange N M g c₀).close O = Stepped.foldRange N (M.close O) g c₀ := close_foldWhile _ _ _ _ _ _

/-- `close` commutes with `sumRange`. -/
@[simp] theorem close_sumRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) (O : Q → Option A) :
    (sumRange N M).close O = Stepped.sumRange N (M.close O) := close_foldRange _ _ _ _ _

/-- `close` commutes with `prodRange`. -/
@[simp] theorem close_prodRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) (O : Q → Option A) :
    (prodRange N M).close O = Stepped.prodRange N (M.close O) := close_foldRange _ _ _ _ _

/-- `close` commutes with `gated`. -/
@[simp] theorem close_gated [HasSize α] (M : QueryMachine Q A α Bool) (N : QueryMachine Q A α ℤ) (O : Q → Option A) :
    (gated M N).close O = Eight.SecNetworks.gated (M.close O) (N.close O) := by
  simp only [gated, Eight.SecNetworks.gated, close_bind, close_ite, close_mapIn, close_const]

end QueryMachines.QueryMachine
