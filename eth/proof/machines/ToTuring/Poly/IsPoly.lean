/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Unary
public import ToTuring.Lib.Int
public import StepMachines.Prog.Range

/-! `IsPolyT` (every part of a stepped computation is polynomial-time) for a single step and for the
loop `foldWhile`. -/

@[expose] public section

namespace Groundwork

namespace IsPolyT

open Stepped

variable {α β γ τ : Type}

section ofFun

variable [Enc α] [Enc β]

theorem ofFun_step {f : α → β} (hf : PolyT f) :
    PolyT (fun s : α ⊕ β => match s with | .inl a => (.inr (f a) : α ⊕ β) | .inr b => .inr b) :=
  (by fun_prop : PolyT fun s : α ⊕ β => s.elim (fun a => (.inr (f a) : α ⊕ β)) fun b => .inr b).congr
    fun s => by cases s <;> rfl

theorem ofFun_out : PolyT (fun s : α ⊕ β => match s with | .inl _ => none | .inr b => some b) :=
  (by fun_prop : PolyT fun s : α ⊕ β => s.elim (fun _ => none) fun b => some b).congr fun s => by cases s <;> rfl

theorem ofFun_init : PolyT (fun a : α => (.inl a : α ⊕ β)) := by fun_prop

variable [HasSize α] [HasSize β] [Carried α] [Carried β]

/-- A polynomial-time function, run as a single step (`Stepped.ofFun`), is `IsPolyT`. -/
@[instance_reducible] def ofFun {f : α → β} (hf : PolyT f) : IsPolyT (ofFun f) where
  enc := (inferInstance : Enc (α ⊕ β))
  carried := (inferInstance : Carried (α ⊕ β))
  init := ofFun_init
  step := ofFun_step hf
  out := ofFun_out

end ofFun

section foldWhile

variable [Enc τ] [Enc γ] [Enc α] [Enc β] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} [IsPolyT M]
  {g : γ → τ → β → γ} {c₀ : α → γ}

theorem foldGo_poly : PolyT (fun p : γ × Option τ => foldGo M p.1 p.2) := by
  have := IsPolyT.init (M := M)
  exact (by fun_prop : PolyT fun p : γ × Option τ =>
    p.2.elim (.inr p.1 : (τ × γ × M.σ) ⊕ γ) fun x => .inl (x, p.1, M.init x)).congr fun p => by
      rcases p with ⟨c, _ | x⟩ <;> rfl

theorem foldWhile_init (hs : PolyT start) (hc : PolyT c₀) : PolyT (fun a => foldGo M (c₀ a) (start a)) :=
  PolyT.comp (g := fun a => (c₀ a, start a)) (foldGo_poly (M := M) (γ := γ)) (by fun_prop)

theorem foldWhile_step (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) :
    PolyT (fun s : (τ × γ × M.σ) ⊕ γ => match s with
      | .inl p => match M.out p.2.2 with
        | some b => foldGo M (g p.2.1 p.1 b) (nxt p.1)
        | none => .inl (p.1, p.2.1, M.step p.2.2)
      | .inr c => .inr c) := by
  have h1 := IsPolyT.step (M := M)
  have h2 := IsPolyT.out (M := M)
  have h3 : PolyT fun q : (τ × γ × M.σ) × β => foldGo M (g q.1.2.1 q.1.1 q.2) (nxt q.1.1) :=
    PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (g q.1.2.1 q.1.1 q.2, nxt q.1.1)) (foldGo_poly (M := M) (γ := γ))
      (PolyT.prodMk (PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (q.1.2.1, q.1.1, q.2)) hg (by fun_prop)) (by fun_prop))
  have h4 : PolyT fun p : τ × γ × M.σ => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
      fun b => foldGo M (g p.2.1 p.1 b) (nxt p.1) :=
    PolyT.optionElim (by fun_prop) (by fun_prop) h3
  have h5 : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim
      (fun p => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
        fun b => foldGo M (g p.2.1 p.1 b) (nxt p.1)) fun c => .inr c :=
    PolyT.sumElim (by fun_prop) (PolyT.comp (g := fun q : ((τ × γ × M.σ) ⊕ γ) × (τ × γ × M.σ) => q.2) h4 (by fun_prop))
      (by fun_prop)
  refine h5.congr fun s => ?_
  rcases s with p | c
  · simp only [Sum.elim_inl]
    cases M.out p.2.2 <;> rfl
  · rfl

theorem foldWhile_out : PolyT (fun s : (τ × γ × M.σ) ⊕ γ => match s with | .inl _ => none | .inr c => some c) :=
  (by fun_prop : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim (fun _ => none) fun c => some c).congr
    fun s => by cases s <;> rfl

variable [HasSize τ] [HasSize γ] [Carried τ] [Carried γ]

/-- The loop `Stepped.foldWhile` is `IsPolyT` if its body `M` is and `start`, `nxt`, `g`, `c₀` are
polynomial-time. -/
@[instance_reducible] def foldWhile (hs : PolyT start) (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2)
    (hc : PolyT c₀) : IsPolyT (foldWhile start nxt M g c₀) where
  enc := (inferInstance : Enc ((τ × γ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((τ × γ × M.σ) ⊕ γ))
  init := foldWhile_init hs hc
  step := foldWhile_step hn hg
  out := foldWhile_out

end foldWhile

end IsPolyT

end Groundwork
