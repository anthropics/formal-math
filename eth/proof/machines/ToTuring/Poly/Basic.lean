/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.IsPoly

/-! `IsPolyT` (every part of a stepped computation is polynomial-time) is closed under the
combinators `mapIn`, `mapOut`
and `bind` of `StepMachines/Prog/Stepped.lean`. -/

@[expose] public section

namespace Groundwork

namespace IsPolyT

open Stepped

variable {α β γ : Type}

section mapIn

variable [Enc α] [Enc β] [Enc γ] {f : α → β} {M : Stepped β γ} [IsPolyT M]

theorem mapIn_init (hf : PolyT f) : PolyT (fun a => M.init (f a)) := by
  have := IsPolyT.init (M := M); fun_prop

/-- Applying a polynomial-time `f` to the input before running `M` keeps `IsPolyT`. -/
@[instance_reducible] def mapIn (hf : PolyT f) : IsPolyT (mapIn f M) where
  enc := (inferInstance : Enc M.σ)
  carried := (inferInstance : Carried M.σ)
  init := mapIn_init hf
  step := IsPolyT.step (M := M)
  out := IsPolyT.out (M := M)

end mapIn

section mapOut

variable [Enc α] [Enc β] [Enc γ] {M : Stepped α β} [IsPolyT M] {f : β → γ}

theorem mapOut_out (hf : PolyT f) : PolyT (fun s => (M.out s).map f) := by
  have := IsPolyT.out (M := M); fun_prop

/-- Applying a polynomial-time `f` to the output of `M` keeps `IsPolyT`. -/
@[instance_reducible] def mapOut (hf : PolyT f) : IsPolyT (mapOut M f) where
  enc := (inferInstance : Enc M.σ)
  carried := (inferInstance : Carried M.σ)
  init := IsPolyT.init (M := M)
  step := IsPolyT.step (M := M)
  out := mapOut_out hf

end mapOut

section bind

variable [Enc α] [Enc β] [Enc γ] {M : Stepped α β} {N : Stepped (α × β) γ} [IsPolyT M] [IsPolyT N]

theorem bind_init : PolyT (fun a : α => (.inl (a, M.init a) : (α × M.σ) ⊕ N.σ)) := by
  have := IsPolyT.init (M := M); fun_prop

theorem bind_step : PolyT (fun s : (α × M.σ) ⊕ N.σ => match s with
    | .inl p => match M.out p.2 with
      | some b => (.inr (N.init (p.1, b)) : (α × M.σ) ⊕ N.σ)
      | none => .inl (p.1, M.step p.2)
    | .inr s => .inr (N.step s)) := by
  have := IsPolyT.step (M := M); have := IsPolyT.out (M := M)
  have := IsPolyT.init (M := N); have := IsPolyT.step (M := N)
  refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ N.σ => s.elim
    (fun p => (M.out p.2).elim (.inl (p.1, M.step p.2) : (α × M.σ) ⊕ N.σ) fun b => .inr (N.init (p.1, b)))
    fun s => .inr (N.step s)).congr fun s => ?_
  rcases s with p | s
  · simp only [Sum.elim_inl]
    cases M.out p.2 <;> rfl
  · rfl

theorem bind_out : PolyT (fun s : (α × M.σ) ⊕ N.σ => match s with | .inl _ => none | .inr s => N.out s) := by
  have := IsPolyT.out (M := N)
  exact (by fun_prop : PolyT fun s : (α × M.σ) ⊕ N.σ => s.elim (fun _ => none) fun s => N.out s).congr
    fun s => by cases s <;> rfl

/-- Running `M`, then `N` on the input paired with the output of `M`, keeps `IsPolyT`. The state
carries the input while
`M` runs. -/
@[instance_reducible] def bind [HasSize α] [Carried α] : IsPolyT (bind M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ N.σ))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ N.σ))
  init := bind_init
  step := bind_step
  out := bind_out

end bind

end IsPolyT

end Groundwork
