/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Basic
public import StepMachines.Prog.Comb

/-! `IsPolyT` (start, step and output of a stepped computation are polynomial-time) is closed under
combinators of
StepMachines/Prog/Comb.lean, such as `branch`, `ite`, `const` and `optBind`. -/

@[expose] public section

namespace Groundwork

namespace IsPolyT

open Stepped

variable {α α₁ α₂ β γ δ ι : Type}

section branch

variable [Enc α] [Enc α₁] [Enc α₂] [Enc β] {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} [IsPolyT M₁]
  [IsPolyT M₂]

theorem branch_init (hs : PolyT sel) : PolyT (fun a : α => match sel a with
    | .inl x => (.inl (M₁.init x) : M₁.σ ⊕ M₂.σ) | .inr y => .inr (M₂.init y)) := by
  have := IsPolyT.init (M := M₁); have := IsPolyT.init (M := M₂)
  refine (by fun_prop : PolyT fun a : α => (sel a).elim (fun x => (.inl (M₁.init x) : M₁.σ ⊕ M₂.σ))
    fun y => .inr (M₂.init y)).congr fun a => ?_
  cases sel a <;> rfl

theorem branch_step : PolyT (fun s : M₁.σ ⊕ M₂.σ => match s with
    | .inl s => (.inl (M₁.step s) : M₁.σ ⊕ M₂.σ) | .inr s => .inr (M₂.step s)) := by
  have := IsPolyT.step (M := M₁); have := IsPolyT.step (M := M₂)
  exact (by fun_prop : PolyT fun s : M₁.σ ⊕ M₂.σ => s.elim (fun s => (.inl (M₁.step s) : M₁.σ ⊕ M₂.σ))
    fun s => .inr (M₂.step s)).congr fun s => by cases s <;> rfl

theorem branch_out : PolyT (fun s : M₁.σ ⊕ M₂.σ => match s with | .inl s => M₁.out s | .inr s => M₂.out s) := by
  have := IsPolyT.out (M := M₁); have := IsPolyT.out (M := M₂)
  exact (by fun_prop : PolyT fun s : M₁.σ ⊕ M₂.σ => s.elim (fun s => M₁.out s) fun s => M₂.out s).congr
    fun s => by cases s <;> rfl

/-- The machine that runs `M₁` or `M₂`, as a polynomial-time `sel` decides from the input, is
`IsPolyT`. -/
@[instance_reducible] def branch (hs : PolyT sel) : IsPolyT (branch sel M₁ M₂) where
  enc := (inferInstance : Enc (M₁.σ ⊕ M₂.σ))
  carried := (inferInstance : Carried (M₁.σ ⊕ M₂.σ))
  init := branch_init hs
  step := branch_step
  out := branch_out

end branch

section ite

variable [Enc α] [Enc β] {p : α → Bool} {M N : Stepped α β} [IsPolyT M] [IsPolyT N]

theorem iteSel_poly (hp : PolyT p) : PolyT (iteSel p) := by unfold iteSel; fun_prop

/-- The choice between `M` and `N` by a polynomial-time test `p` of the input is `IsPolyT`. -/
@[instance_reducible] def ite (hp : PolyT p) : IsPolyT (ite p M N) := branch (iteSel_poly hp)

end ite

section const

variable [HasSize α] [HasSize β] [Enc α] [Carried α] [Enc β] [Carried β]

/-- The machine that always returns `b` is `IsPolyT`. -/
@[instance_reducible] def const (b : β) : IsPolyT (const b : Stepped α β) := ofFun (by unfold Function.const; fun_prop)

end const

section optBind

variable [HasSize α] [HasSize β] [Enc α] [Carried α] [Enc β] [Carried β] [Enc ι] {M : Stepped α (Option ι)}
  {N : Stepped (α × ι) β} {dflt : α → β} [IsPolyT M] [IsPolyT N]

omit [HasSize α] [Carried α] in
theorem optSel_poly : PolyT (optSel : α × Option ι → (α × ι) ⊕ α) :=
  (by fun_prop : PolyT fun x : α × Option ι => x.2.elim (.inr x.1 : (α × ι) ⊕ α) fun i => .inl (x.1, i)).congr
    fun x => by rcases x with ⟨a, _ | i⟩ <;> rfl

/-- Run `M`; on `some i` run `N` on the input paired with `i`, on `none` return the polynomial-time
`dflt` of the input.
This is `IsPolyT`. -/
@[instance_reducible] def optBind (hd : PolyT dflt) : IsPolyT (optBind M N dflt) :=
  haveI := ofFun hd
  haveI : IsPolyT (Stepped.branch optSel N (Stepped.ofFun dflt)) := branch optSel_poly
  bind

end optBind

section both

variable [HasSize α] [HasSize β] [Enc α] [Carried α] [Enc β] [Carried β] [Enc γ] {M : Stepped α β} {N : Stepped α γ}
  [IsPolyT M] [IsPolyT N]

omit [HasSize α] [HasSize β] [Carried α] [Carried β] in
theorem both_init : PolyT (fun a : α => (.inl (a, M.init a) : (α × M.σ) ⊕ (β × N.σ))) := by
  have := IsPolyT.init (M := M); fun_prop

omit [HasSize α] [HasSize β] [Carried α] [Carried β] in
theorem both_step : PolyT (fun s : (α × M.σ) ⊕ (β × N.σ) => match s with
    | .inl p => match M.out p.2 with
      | some b => (.inr (b, N.init p.1) : (α × M.σ) ⊕ (β × N.σ))
      | none => .inl (p.1, M.step p.2)
    | .inr p => .inr (p.1, N.step p.2)) := by
  have := IsPolyT.step (M := M); have := IsPolyT.out (M := M)
  have := IsPolyT.init (M := N); have := IsPolyT.step (M := N)
  refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ (β × N.σ) => s.elim
    (fun p => (M.out p.2).elim (.inl (p.1, M.step p.2) : (α × M.σ) ⊕ (β × N.σ)) fun b => .inr (b, N.init p.1))
    fun p => .inr (p.1, N.step p.2)).congr fun s => ?_
  rcases s with p | s
  · simp only [Sum.elim_inl]
    cases M.out p.2 <;> rfl
  · rfl

omit [HasSize α] [HasSize β] [Carried α] [Carried β] in
theorem both_out : PolyT (fun s : (α × M.σ) ⊕ (β × N.σ) => match s with
    | .inl _ => none | .inr p => (N.out p.2).map fun c => (p.1, c)) := by
  have := IsPolyT.out (M := N)
  exact (by fun_prop : PolyT fun s : (α × M.σ) ⊕ (β × N.σ) => s.elim (fun _ => none)
    fun p => (N.out p.2).map fun c => (p.1, c)).congr fun s => by cases s <;> rfl

/-- Running `M` and then `N` on the same input, and returning the pair of their outputs, is
`IsPolyT`. -/
@[instance_reducible] def both : IsPolyT (both M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ (β × N.σ)))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ (β × N.σ)))
  init := both_init
  step := both_step
  out := both_out

/-- Combining the outputs of `M` and `N` on the same input by a polynomial-time `f` is `IsPolyT`. -/
@[instance_reducible] def map2 [Enc δ] {f : β → γ → δ} (hf : PolyT fun p : β × γ => f p.1 p.2) : IsPolyT (map2 f M N) :=
  haveI : IsPolyT (Stepped.both M N) := both
  mapOut (by unfold Function.uncurry; exact hf)

end both

section mul2

variable [HasSize α] [Enc α] [Carried α] {M N : Stepped α ℤ} [IsPolyT M] [IsPolyT N]

/-- The product of the integer outputs of `M` and `N` on the same input is `IsPolyT`. -/
@[instance_reducible] def mul2 : IsPolyT (mul2 M N) := map2 (by change PolyT fun p : ℤ × ℤ => p.1 * p.2; fun_prop)

end mul2

end IsPolyT

end Groundwork
