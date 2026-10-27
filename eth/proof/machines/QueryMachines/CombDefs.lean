/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.Kernel
public import StepMachines.Prog.Range
public import Eight.SecNetworks_LemGrouping

/-! # Building machines with query access (definitions only)

Every way to build step machines that the algorithms of the main text use
(proof/machines/StepMachines/Prog/Stepped.lean, Comb.lean, Range.lean; `gated` of
proof/networks/Eight/SecNetworks_LemGrouping.lean) is repeated here for machines with query access
(`QueryMachines.QueryMachine`, proof/machines/QueryMachines/Kernel.lean).
In each case the step machine underneath IS the construction for step machines, applied to the
parts' step machines; added is how `ask` and `resume` pass on to the running part.
`lift` (asks nothing) and `query` (asks one query) have no counterpart for step machines. That
building in the oracle (`close`) commutes with every construction is proved in
proof/machines/QueryMachines/Comb.lean. This file has no proofs. -/

@[expose] public section

namespace Groundwork.Stepped

variable {α β : Type}

/-- One step: the value g a, if there is one; if there is none the machine stays where it is and
never halts. (This is what a single query becomes when the oracle is built in.) -/
def ofOption [HasSize α] [HasSize β] (g : α → Option β) : Stepped α β where
  σ := α ⊕ β
  init := .inl
  step s := match s with | .inl a => (match g a with | some b => .inr b | none => .inl a) | .inr b => .inr b
  out s := match s with | .inl _ => none | .inr b => some b

end Groundwork.Stepped

namespace QueryMachines.QueryMachine

open Groundwork

variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}

/-! ## The constructions -/

/-- A step machine: it asks nothing. -/
def lift (M : Stepped α β) : QueryMachine Q A α β := { M with ask := fun _ => none, resume := fun s _ => s }

/-- Ask the query h a and return the answer. No step of its own. -/
def query [HasSize α] [HasSize A] (h : α → Q) : QueryMachine Q A α A where
  σ := α ⊕ A
  init := .inl
  step s := s
  out s := match s with | .inl _ => none | .inr b => some b
  ask s := match s with | .inl a => some (h a) | .inr _ => none
  resume _ v := .inr v

/-- The same machine with every query x written as h x. -/
def mapAsk (h : Q → Q') (M : QueryMachine Q A α β) : QueryMachine Q' A α β :=
  { M.toStepped with ask := fun s => (M.ask s).map h, resume := M.resume }

/-- M on g a. -/
def mapIn (g : α → β) (M : QueryMachine Q A β γ) : QueryMachine Q A α γ :=
  { Stepped.mapIn g M.toStepped with ask := M.ask, resume := M.resume }

/-- g applied to the result of M. -/
def mapOut (M : QueryMachine Q A α β) (g : β → γ) : QueryMachine Q A α γ :=
  { Stepped.mapOut M.toStepped g with ask := M.ask, resume := M.resume }

/-- M, then N on the input together with the result of M. -/
def bind [HasSize α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) : QueryMachine Q A α γ :=
  { Stepped.bind M.toStepped N.toStepped with
    ask := fun (s : (α × M.σ) ⊕ N.σ) => match s with
      | .inl p => (match M.out p.2 with | some _ => none | none => M.ask p.2)
      | .inr s => N.ask s
    resume := fun (s : (α × M.σ) ⊕ N.σ) v => match s with
      | .inl p => (.inl (p.1, M.resume p.2 v) : (α × M.σ) ⊕ N.σ)
      | .inr s => .inr (N.resume s v) }

/-- The loop of `Stepped.foldWhile` with a body that may ask. -/
def foldWhile [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : QueryMachine Q A τ β) (g : γ → τ → β → γ) (c₀ : α → γ) : QueryMachine Q A α γ :=
  { Stepped.foldWhile start nxt M.toStepped g c₀ with
    ask := fun (s : (τ × γ × M.σ) ⊕ γ) => match s with
      | .inl p => (match M.out p.2.2 with | some _ => none | none => M.ask p.2.2)
      | .inr _ => none
    resume := fun (s : (τ × γ × M.σ) ⊕ γ) v => match s with
      | .inl p => (.inl (p.1, p.2.1, M.resume p.2.2 v) : (τ × γ × M.σ) ⊕ γ)
      | .inr c => .inr c }

/-- M₁ on x if sel a = inl x, M₂ on y if sel a = inr y. -/
def branch (sel : α → α₁ ⊕ α₂) (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) : QueryMachine Q A α β :=
  { Stepped.branch sel M₁.toStepped M₂.toStepped with
    ask := fun (s : M₁.σ ⊕ M₂.σ) => match s with | .inl s => M₁.ask s | .inr s => M₂.ask s
    resume := fun (s : M₁.σ ⊕ M₂.σ) v => match s with
      | .inl s => (.inl (M₁.resume s v) : M₁.σ ⊕ M₂.σ) | .inr s => .inr (M₂.resume s v) }

/-- M, then N, on the same input; both results. -/
def both [HasSize α] [HasSize β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) : QueryMachine Q A α (β × γ) :=
  { Stepped.both M.toStepped N.toStepped with
    ask := fun (s : (α × M.σ) ⊕ (β × N.σ)) => match s with
      | .inl p => (match M.out p.2 with | some _ => none | none => M.ask p.2)
      | .inr p => N.ask p.2
    resume := fun (s : (α × M.σ) ⊕ (β × N.σ)) v => match s with
      | .inl p => (.inl (p.1, M.resume p.2 v) : (α × M.σ) ⊕ (β × N.σ))
      | .inr p => .inr (p.1, N.resume p.2 v) }

/-! ## Made from these, as for step machines -/

/-- M if p a, else N. -/
def ite (p : α → Bool) (M N : QueryMachine Q A α β) : QueryMachine Q A α β := branch (Stepped.iteSel p) M N

/-- The result b; one step. -/
def const [HasSize α] [HasSize β] (b : β) : QueryMachine Q A α β := lift (Stepped.const b)

/-- M; if its result is some i, then N on (a, i); if none, then dflt a. -/
def optBind [HasSize α] [HasSize β] (M : QueryMachine Q A α (Option ι)) (N : QueryMachine Q A (α × ι) β) (dflt : α → β) : QueryMachine Q A α β :=
  bind M (branch Stepped.optSel N (lift (Stepped.ofFun dflt)))

/-- The loop over y = 0, 1, …, N a − 1. -/
def foldRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) β) (g : γ → ℕ → β → γ) (c₀ : α → γ) : QueryMachine Q A α γ :=
  foldWhile (Stepped.rangeStart N) (Stepped.rangeNext N) M (Stepped.rangeG g) c₀

/-- Σ_{y < N a} M(a, y). -/
def sumRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) : QueryMachine Q A α ℤ := foldRange N M Stepped.addG Stepped.zeroC

/-- ∏_{y < N a} M(a, y). -/
def prodRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) : QueryMachine Q A α ℤ := foldRange N M Stepped.mulG Stepped.oneC

/-- [M says yes]·N: first the test M; if it says yes, N; else 0. -/
def gated [HasSize α] (M : QueryMachine Q A α Bool) (N : QueryMachine Q A α ℤ) : QueryMachine Q A α ℤ :=
  bind M (ite (fun p : α × Bool => p.2) (mapIn Prod.fst N) (const 0))

end QueryMachines.QueryMachine
