/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.Comb
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
import Mathlib.Tactic

/-! # Polynomial-time steps
`IsPolyQ` (proof/machines/QueryMachines/Kernel.lean) is kept by the constructions of
proof/machines/QueryMachines/CombDefs.lean and by `subst`; `IsPolyT` by `plug` and `close`, and it
holds for the step machine underneath a machine with `IsPolyQ`.
The fields init, step, out say that the start, one step and the read-out of the step machine
underneath are polynomial-time, as for `IsPolyT` (proof/machines/ToTuring/Poly); `ask` and `resume`
say that asking a query and taking in its answer are polynomial-time. -/

@[expose] public section

namespace QueryMachines.QueryMachine

open Groundwork

variable {Q A Q' A' C α α₁ α₂ β γ δ ι τ : Type}

namespace IsPolyQ

/-- The step machine underneath has polynomial-time steps. -/
@[instance_reducible] instance under [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) [h : IsPolyQ M] : IsPolyT M.toStepped where
  enc := h.enc
  carried := h.carried
  init := h.init
  step := h.step
  out := h.out

section lift

variable [Enc Q] [Enc A] [Enc α] [Enc β]

/-- A step machine with polynomial-time steps, seen as a machine that asks nothing. -/
@[instance_reducible] def lift (R : Stepped α β) [h : IsPolyT R] : IsPolyQ (QueryMachine.lift R : QueryMachine Q A α β) where
  enc := h.enc
  carried := h.carried
  init := h.init
  step := h.step
  out := h.out
  ask := (by fun_prop : PolyT fun _ : R.σ => (none : Option Q))
  resume := (by fun_prop : PolyT fun p : R.σ × A => p.1)

end lift

section query

variable [Enc Q] [Enc A] [Enc α] [HasSize α] [HasSize A] [Carried α] [Carried A]

/-- A single query, if the query is computed in polynomial time from the input. -/
@[instance_reducible] def query {h : α → Q} (hh : PolyT h) : IsPolyQ (QueryMachine.query h : QueryMachine Q A α A) where
  enc := (inferInstance : Enc (α ⊕ A))
  carried := (inferInstance : Carried (α ⊕ A))
  init := (by fun_prop : PolyT fun a : α => (.inl a : α ⊕ A))
  step := (by fun_prop : PolyT fun s : α ⊕ A => s)
  out := (IsPolyT.ofFun_out (α := α) (β := A)).congr fun s => by cases s <;> rfl
  ask := (by fun_prop : PolyT fun s : α ⊕ A => s.elim (fun a => some (h a)) fun _ => none).congr fun s => by cases s <;> rfl
  resume := (by fun_prop : PolyT fun p : (α ⊕ A) × A => (.inr p.2 : α ⊕ A))

end query

section maps

variable [Enc Q] [Enc Q'] [Enc A] [Enc α] [Enc β] [Enc γ]

/-- Queries rewritten by a polynomial-time function. -/
@[instance_reducible] def mapAsk {h : Q → Q'} (hh : PolyT h) (M : QueryMachine Q A α β) [i : IsPolyQ M] : IsPolyQ (QueryMachine.mapAsk h M) where
  enc := i.enc
  carried := i.carried
  init := i.init
  step := i.step
  out := i.out
  ask := by
    have := i.ask
    exact (by fun_prop : PolyT fun s : M.σ => (M.ask s).map h)
  resume := i.resume

/-- A polynomial-time function applied to the input. -/
@[instance_reducible] def mapIn {g : α → β} (hg : PolyT g) (M : QueryMachine Q A β γ) [i : IsPolyQ M] : IsPolyQ (QueryMachine.mapIn g M) where
  enc := i.enc
  carried := i.carried
  init := IsPolyT.mapIn_init (M := M.toStepped) hg
  step := i.step
  out := i.out
  ask := i.ask
  resume := i.resume

/-- A polynomial-time function applied to the result. -/
@[instance_reducible] def mapOut (M : QueryMachine Q A α β) [i : IsPolyQ M] {g : β → γ} (hg : PolyT g) : IsPolyQ (QueryMachine.mapOut M g) where
  enc := i.enc
  carried := i.carried
  init := i.init
  step := i.step
  out := IsPolyT.mapOut_out (M := M.toStepped) hg
  ask := i.ask
  resume := i.resume

end maps

section bind

variable [Enc Q] [Enc A] [Enc α] [Enc β] [Enc γ] [HasSize α] [Carried α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) [IsPolyQ M] [IsPolyQ N]

/-- One machine after the other. -/
@[instance_reducible] def bind : IsPolyQ (QueryMachine.bind M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ N.σ))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ N.σ))
  init := IsPolyT.bind_init (M := M.toStepped) (N := N.toStepped)
  step := IsPolyT.bind_step (M := M.toStepped) (N := N.toStepped)
  out := IsPolyT.bind_out (M := M.toStepped) (N := N.toStepped)
  ask := by
    have h1 := IsPolyQ.out (M := M); have h2 := IsPolyQ.ask (M := M); have h3 := IsPolyQ.ask (M := N)
    refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ N.σ => s.elim (fun p => (M.out p.2).elim (M.ask p.2) fun _ => none) fun s => N.ask s).congr fun s => ?_
    rcases s with p | s
    · change _ = (match M.out p.2 with | some _ => none | none => M.ask p.2)
      simp only [Sum.elim_inl]
      cases M.out p.2 <;> rfl
    · rfl
  resume := by
    have h1 : PolyT fun q : (((α × M.σ) ⊕ N.σ) × A) × (α × M.σ) => M.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ N.σ) × A) × (α × M.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    have h2 : PolyT fun q : (((α × M.σ) ⊕ N.σ) × A) × N.σ => N.resume q.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ N.σ) × A) × N.σ => (q.2, q.1.2)) (IsPolyQ.resume (M := N)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : ((α × M.σ) ⊕ N.σ) × A => q.1) (f := fun q p => (.inl (p.1, M.resume p.2 q.2) : (α × M.σ) ⊕ N.σ))
      (g := fun q s => .inr (N.resume s q.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl

end bind

section foldWhile

variable [Enc Q] [Enc A] [Enc α] [Enc β] [Enc γ] [Enc τ] [HasSize τ] [HasSize γ] [Carried τ] [Carried γ] {start : α → Option τ} {nxt : τ → Option τ} (M : QueryMachine Q A τ β) [IsPolyQ M]
  {g : γ → τ → β → γ} {c₀ : α → γ}

/-- The loop, if its body has polynomial-time steps and `start`, `nxt`, `g`, `c₀` are
polynomial-time. -/
@[instance_reducible] def foldWhile (hs : PolyT start) (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : IsPolyQ (QueryMachine.foldWhile start nxt M g c₀) where
  enc := (inferInstance : Enc ((τ × γ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((τ × γ × M.σ) ⊕ γ))
  init := IsPolyT.foldWhile_init (M := M.toStepped) hs hc
  step := IsPolyT.foldWhile_step (M := M.toStepped) hn hg
  out := IsPolyT.foldWhile_out (M := M.toStepped)
  ask := by
    have h1 := IsPolyQ.out (M := M); have h2 := IsPolyQ.ask (M := M)
    refine (by fun_prop : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim (fun p => (M.out p.2.2).elim (M.ask p.2.2) fun _ => none) fun _ => none).congr fun s => ?_
    rcases s with p | s
    · change _ = (match M.out p.2.2 with | some _ => none | none => M.ask p.2.2)
      simp only [Sum.elim_inl]
      cases M.out p.2.2 <;> rfl
    · rfl
  resume := by
    have h1 : PolyT fun q : (((τ × γ × M.σ) ⊕ γ) × A) × (τ × γ × M.σ) => M.resume q.2.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((τ × γ × M.σ) ⊕ γ) × A) × (τ × γ × M.σ) => (q.2.2.2, q.1.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : ((τ × γ × M.σ) ⊕ γ) × A => q.1) (f := fun q p => (.inl (p.1, p.2.1, M.resume p.2.2 q.2) : (τ × γ × M.σ) ⊕ γ))
      (g := fun _ c => .inr c) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl

end foldWhile

section branch

variable [Enc Q] [Enc A] [Enc α] [Enc α₁] [Enc α₂] [Enc β] {sel : α → α₁ ⊕ α₂} (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) [IsPolyQ M₁] [IsPolyQ M₂]

/-- A choice between two machines by a polynomial-time function of the input. -/
@[instance_reducible] def branch (hs : PolyT sel) : IsPolyQ (QueryMachine.branch sel M₁ M₂) where
  enc := (inferInstance : Enc (M₁.σ ⊕ M₂.σ))
  carried := (inferInstance : Carried (M₁.σ ⊕ M₂.σ))
  init := IsPolyT.branch_init (M₁ := M₁.toStepped) (M₂ := M₂.toStepped) hs
  step := IsPolyT.branch_step (M₁ := M₁.toStepped) (M₂ := M₂.toStepped)
  out := IsPolyT.branch_out (M₁ := M₁.toStepped) (M₂ := M₂.toStepped)
  ask := by
    have h1 := IsPolyQ.ask (M := M₁); have h2 := IsPolyQ.ask (M := M₂)
    exact (by fun_prop : PolyT fun s : M₁.σ ⊕ M₂.σ => s.elim (fun s => M₁.ask s) fun s => M₂.ask s).congr fun s => by cases s <;> rfl
  resume := by
    have h1 : PolyT fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₁.σ => M₁.resume q.2 q.1.2 :=
      PolyT.comp (g := fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₁.σ => (q.2, q.1.2)) (IsPolyQ.resume (M := M₁)) (by fun_prop)
    have h2 : PolyT fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₂.σ => M₂.resume q.2 q.1.2 :=
      PolyT.comp (g := fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₂.σ => (q.2, q.1.2)) (IsPolyQ.resume (M := M₂)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : (M₁.σ ⊕ M₂.σ) × A => q.1) (f := fun q s => (.inl (M₁.resume s q.2) : M₁.σ ⊕ M₂.σ))
      (g := fun q s => .inr (M₂.resume s q.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl

end branch

section both

variable [Enc Q] [Enc A] [Enc α] [Enc β] [Enc γ] [HasSize α] [HasSize β] [Carried α] [Carried β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) [IsPolyQ M] [IsPolyQ N]

/-- Two machines on one input. -/
@[instance_reducible] def both : IsPolyQ (QueryMachine.both M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ (β × N.σ)))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ (β × N.σ)))
  init := IsPolyT.both_init (M := M.toStepped) (N := N.toStepped)
  step := IsPolyT.both_step (M := M.toStepped) (N := N.toStepped)
  out := IsPolyT.both_out (M := M.toStepped) (N := N.toStepped)
  ask := by
    have h1 := IsPolyQ.out (M := M); have h2 := IsPolyQ.ask (M := M); have h3 := IsPolyQ.ask (M := N)
    refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ (β × N.σ) => s.elim (fun p => (M.out p.2).elim (M.ask p.2) fun _ => none) fun p => N.ask p.2).congr fun s => ?_
    rcases s with p | s
    · change _ = (match M.out p.2 with | some _ => none | none => M.ask p.2)
      simp only [Sum.elim_inl]
      cases M.out p.2 <;> rfl
    · rfl
  resume := by
    have h1 : PolyT fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (α × M.σ) => M.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (α × M.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    have h2 : PolyT fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (β × N.σ) => N.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (β × N.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := N)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : ((α × M.σ) ⊕ (β × N.σ)) × A => q.1) (f := fun q p => (.inl (p.1, M.resume p.2 q.2) : (α × M.σ) ⊕ (β × N.σ)))
      (g := fun q p => .inr (p.1, N.resume p.2 q.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl

end both

/-! ## Constructions made from the ones above -/

section derived

variable [Enc Q] [Enc A] [Enc α] [Enc β]

/-- A choice by a polynomial-time test. -/
@[instance_reducible] def ite {p : α → Bool} (hp : PolyT p) (M N : QueryMachine Q A α β) [IsPolyQ M] [IsPolyQ N] : IsPolyQ (QueryMachine.ite p M N) := branch M N (IsPolyT.iteSel_poly hp)

/-- A constant. -/
@[instance_reducible] def const [HasSize α] [HasSize β] [Carried α] [Carried β] (b : β) : IsPolyQ (QueryMachine.const b : QueryMachine Q A α β) :=
  haveI := IsPolyT.const (α := α) b
  lift (Stepped.const b)

/-- `optBind`, if the default is polynomial-time. -/
@[instance_reducible] def optBind [HasSize α] [HasSize β] [Carried α] [Carried β] [Enc ι] (M : QueryMachine Q A α (Option ι)) (N : QueryMachine Q A (α × ι) β) [IsPolyQ M] [IsPolyQ N] {dflt : α → β}
    (hd : PolyT dflt) : IsPolyQ (QueryMachine.optBind M N dflt) :=
  haveI := IsPolyT.ofFun hd
  haveI : IsPolyQ (QueryMachine.lift (Stepped.ofFun dflt) : QueryMachine Q A α β) := lift _
  haveI : IsPolyQ (QueryMachine.branch Stepped.optSel N (QueryMachine.lift (Stepped.ofFun dflt))) := branch _ _ IsPolyT.optSel_poly
  bind _ _

/-- The loop over a range, if the range, `g` and `c₀` are polynomial-time. -/
@[instance_reducible] def foldRange [HasSize α] [Carried α] [HasSize γ] [Enc γ] [Carried γ] {N : α → ℕ} (M : QueryMachine Q A (α × ℕ) β) [IsPolyQ M] {g : γ → ℕ → β → γ} {c₀ : α → γ}
    (hN : PolyT N) (hg : PolyT fun p : γ × ℕ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : IsPolyQ (QueryMachine.foldRange N M g c₀) :=
  foldWhile M (IsPolyT.rangeStart_poly hN) (IsPolyT.rangeNext_poly hN)
    (by unfold Stepped.rangeG; exact PolyT.comp (g := fun p : γ × (α × ℕ) × β => (p.1, p.2.1.2, p.2.2)) hg (by fun_prop)) hc

/-- The sum over a range. -/
@[instance_reducible] def sumRange [HasSize α] [Carried α] {N : α → ℕ} (M : QueryMachine Q A (α × ℕ) ℤ) [IsPolyQ M] (hN : PolyT N) : IsPolyQ (QueryMachine.sumRange N M) :=
  foldRange M hN (by unfold Stepped.addG; fun_prop) (by unfold Stepped.zeroC; fun_prop)

/-- The product over a range. -/
@[instance_reducible] def prodRange [HasSize α] [Carried α] {N : α → ℕ} (M : QueryMachine Q A (α × ℕ) ℤ) [IsPolyQ M] (hN : PolyT N) : IsPolyQ (QueryMachine.prodRange N M) :=
  foldRange M hN (by unfold Stepped.mulG; fun_prop) (by unfold Stepped.oneC; fun_prop)

/-- A machine behind a test. -/
@[instance_reducible] def gated [HasSize α] [Carried α] (M : QueryMachine Q A α Bool) (N : QueryMachine Q A α ℤ) [IsPolyQ M] [IsPolyQ N] : IsPolyQ (QueryMachine.gated M N) :=
  haveI := mapIn (g := (Prod.fst : α × Bool → α)) (by fun_prop) N
  haveI : IsPolyQ (QueryMachine.const 0 : QueryMachine Q A (α × Bool) ℤ) := const 0
  haveI := ite (p := fun p : α × Bool => p.2) (by fun_prop) (QueryMachine.mapIn Prod.fst N) (QueryMachine.const 0)
  bind _ _

end derived

end IsPolyQ

/-! ## The three ways to answer the queries -/

section answer

variable [Enc Q] [Enc A] [Enc α] [Enc β]

/-- One step that looks a value up, if the look-up is polynomial-time. -/
@[instance_reducible] def ofOption_isPolyT [HasSize α] [HasSize β] [Carried α] [Carried β] {g : α → Option β} (hg : PolyT g) : IsPolyT (Stepped.ofOption g) where
  enc := (inferInstance : Enc (α ⊕ β))
  carried := (inferInstance : Carried (α ⊕ β))
  init := (by fun_prop : PolyT fun a : α => (.inl a : α ⊕ β))
  step := (by fun_prop : PolyT fun s : α ⊕ β => s.elim (fun a => (g a).elim (.inl a : α ⊕ β) fun b => .inr b) fun b => .inr b).congr fun s => by
    rcases s with a | b
    · change _ = (match g a with | some b => _ | none => _)
      simp only [Sum.elim_inl]
      cases g a <;> rfl
    · rfl
  out := (IsPolyT.ofFun_out (α := α) (β := β)).congr fun s => by cases s <;> rfl

/-- The oracle built in, if it is computed in polynomial time from the query. -/
@[instance_reducible] def close_isPolyT (M : QueryMachine Q A α β) [IsPolyQ M] {O : Q → Option A} (hO : PolyT O) : IsPolyT (M.close O) where
  enc := (inferInstance : Enc M.σ)
  carried := (inferInstance : Carried M.σ)
  init := IsPolyQ.init (M := M)
  step := by
    have h1 := IsPolyQ.ask (M := M); have h2 := IsPolyQ.step (M := M)
    have h3 : PolyT fun q : (M.σ × Q) × A => M.resume q.1.1 q.2 := PolyT.comp (g := fun q : (M.σ × Q) × A => (q.1.1, q.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    have h4 : PolyT fun q : M.σ × Q => (O q.2).elim q.1 fun v => M.resume q.1 v := PolyT.optionElim (by fun_prop) (by fun_prop) h3
    refine (PolyT.optionElim (o := fun s : M.σ => M.ask s) (d := fun s => M.step s) (f := fun s x => (O x).elim s fun v => M.resume s v) h1 h2 h4).congr fun s => ?_
    change _ = (match M.ask s with | some x => (match O x with | some v => M.resume s v | none => s) | none => M.step s)
    cases M.ask s with
    | none => rfl
    | some x => change _ = (match O x with | some v => M.resume s v | none => s); simp only [Option.elim_some]; cases O x <;> rfl
  out := IsPolyQ.out (M := M)

variable [HasSize C] [Enc C] [Carried C]

omit [Carried C] in
/-- The step of `plug` is polynomial-time. -/
theorem plug_step_poly (M : QueryMachine Q A α β) [IsPolyQ M] (R : Stepped (C × Q) A) [IsPolyT R] :
    @PolyT (C × (M.σ ⊕ (M.σ × R.σ))) (C × (M.σ ⊕ (M.σ × R.σ))) inferInstance inferInstance (M.plug R).step := by
  have h1 := IsPolyQ.ask (M := M); have h2 := IsPolyQ.step (M := M); have h3 := IsPolyT.init (M := R); have h4 := IsPolyT.step (M := R); have h5 := IsPolyT.out (M := R)
  have h6 : PolyT fun r : ((C × (M.σ ⊕ (M.σ × R.σ))) × (M.σ × R.σ)) × A => M.resume r.1.2.1 r.2 :=
    PolyT.comp (g := fun r : ((C × (M.σ ⊕ (M.σ × R.σ))) × (M.σ × R.σ)) × A => (r.1.2.1, r.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
  have hG1 : PolyT fun q : (C × (M.σ ⊕ (M.σ × R.σ))) × M.σ => (M.ask q.2).elim ((q.1.1, .inl (M.step q.2)) : C × (M.σ ⊕ (M.σ × R.σ))) fun x => (q.1.1, .inr (q.2, R.init (q.1.1, x))) := by fun_prop
  have hG2 : PolyT fun q : (C × (M.σ ⊕ (M.σ × R.σ))) × (M.σ × R.σ) => (R.out q.2.2).elim ((q.1.1, .inr (q.2.1, R.step q.2.2)) : C × (M.σ ⊕ (M.σ × R.σ))) fun v => (q.1.1, .inl (M.resume q.2.1 v)) :=
    PolyT.optionElim (by fun_prop) (by fun_prop) (by fun_prop)
  refine (PolyT.sumElim (s := fun s : C × (M.σ ⊕ (M.σ × R.σ)) => s.2) (f := fun s m => (M.ask m).elim ((s.1, .inl (M.step m)) : C × (M.σ ⊕ (M.σ × R.σ))) fun x => (s.1, .inr (m, R.init (s.1, x))))
    (g := fun s p => (R.out p.2).elim ((s.1, .inr (p.1, R.step p.2)) : C × (M.σ ⊕ (M.σ × R.σ))) fun v => (s.1, .inl (M.resume p.1 v))) (by fun_prop) hG1 hG2).congr fun s => ?_
  rcases s with ⟨c, m | p⟩
  · change _ = (match M.ask m with | some x => _ | none => _)
    simp only [Sum.elim_inl]
    cases M.ask m <;> rfl
  · change _ = (match R.out p.2 with | some v => _ | none => _)
    simp only [Sum.elim_inr]
    cases R.out p.2 <;> rfl

/-- Queries answered by a step machine with polynomial-time steps. -/
@[instance_reducible] def plug_isPolyT (M : QueryMachine Q A α β) [IsPolyQ M] (R : Stepped (C × Q) A) [IsPolyT R] : IsPolyT (M.plug R) where
  enc := (inferInstance : Enc (C × (M.σ ⊕ (M.σ × R.σ))))
  carried := (inferInstance : Carried (C × (M.σ ⊕ (M.σ × R.σ))))
  init := by
    have h1 := IsPolyQ.init (M := M)
    exact (by fun_prop : PolyT fun x : C × α => ((x.1, .inl (M.init x.2)) : C × (M.σ ⊕ (M.σ × R.σ))))
  step := plug_step_poly M R
  out := by
    have h1 := IsPolyQ.out (M := M)
    exact (by fun_prop : PolyT fun s : C × (M.σ ⊕ (M.σ × R.σ)) => s.2.elim (fun m => M.out m) fun _ => none).congr fun s => by rcases s with ⟨c, m | p⟩ <;> rfl

variable [Enc Q'] [Enc A']

/-- Queries answered by a machine with query access and polynomial-time steps. -/
@[instance_reducible] def subst_isPolyQ (M : QueryMachine Q A α β) [IsPolyQ M] (N : QueryMachine Q' A' (C × Q) A) [IsPolyQ N] : IsPolyQ (M.subst N) where
  enc := (inferInstance : Enc (C × (M.σ ⊕ (M.σ × N.σ))))
  carried := (inferInstance : Carried (C × (M.σ ⊕ (M.σ × N.σ))))
  init := (plug_isPolyT M N.toStepped).init
  step := (plug_isPolyT M N.toStepped).step
  out := (plug_isPolyT M N.toStepped).out
  ask := by
    have h1 := IsPolyQ.out (M := N); have h2 := IsPolyQ.ask (M := N)
    refine (by fun_prop : PolyT fun s : C × (M.σ ⊕ (M.σ × N.σ)) => s.2.elim (fun _ => none) fun p => (N.out p.2).elim (N.ask p.2) fun _ => none).congr fun s => ?_
    rcases s with ⟨c, m | p⟩
    · rfl
    · change _ = (match N.out p.2 with | some _ => none | none => N.ask p.2)
      simp only [Sum.elim_inr]
      cases N.out p.2 <;> rfl
  resume := by
    have h1 : PolyT fun q : ((C × (M.σ ⊕ (M.σ × N.σ))) × A') × (M.σ × N.σ) => N.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : ((C × (M.σ ⊕ (M.σ × N.σ))) × A') × (M.σ × N.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := N)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : (C × (M.σ ⊕ (M.σ × N.σ))) × A' => q.1.2) (f := fun q _ => q.1)
      (g := fun q p => ((q.1.1, .inr (p.1, N.resume p.2 q.2)) : C × (M.σ ⊕ (M.σ × N.σ)))) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨⟨c, m | p⟩, v⟩ <;> rfl

end answer

end QueryMachines.QueryMachine

namespace QueryMachines

open Groundwork QueryMachine

/-- `StPolyPlug` holds: `plug` of a machine with query access and polynomial-time steps and a step
machine with polynomial-time steps has polynomial-time steps. -/
theorem stPolyPlug : StPolyPlug := fun _ _ _ _ _ _ _ _ _ _ _ _ M R ⟨_hM⟩ ⟨_hR⟩ => ⟨plug_isPolyT M R⟩

/-- `StPolySubst` holds: queries answered by a machine with query access and polynomial-time steps
give a machine with query access and polynomial-time steps. -/
theorem stPolySubst : StPolySubst := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M N ⟨_hM⟩ ⟨_hN⟩ => ⟨subst_isPolyQ M N⟩

/-- `StPolyClose` holds: a machine with query access and polynomial-time steps, with an oracle built
in that is computed in polynomial time from the query, has polynomial-time steps. -/
theorem stPolyClose : StPolyClose := fun _ _ _ _ _ _ _ _ M _ ⟨_hM⟩ hO => ⟨close_isPolyT M hO⟩

end QueryMachines
