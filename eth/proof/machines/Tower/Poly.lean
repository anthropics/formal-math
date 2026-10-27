/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Defs
public import QueryMachines.Poly
public import ToTuring.Lib.List1b

/-! # Polynomial-time steps of `selfCall M`

The states of `selfCall M` are lists of states of M, written as lists of their words (the instance
of `Enc` for lists over the coding that comes with the certificate of M). One step looks at the
first two entries of the list only, and
calls a bounded number of the five functions of M on them; so it is a composition of polynomial-time
functions, whatever the length of the list. Each function is first written with eliminators (the
form in which the tactic `fun_prop`
knows the closure lemmas), then shown equal to the definition by cases. The coding of the states of
M is found through the instance `IsPolyQ.under` of proof/machines/QueryMachines/Poly.lean. -/

@[expose] public section

namespace QueryMachines.Tower

open Groundwork Groundwork.PolyT QueryMachines.QueryMachine

/-! ### A machine that calls itself -/

section selfCall

variable {Q A α β : Type} [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β) [IsPolyQ M]

/-- One step of the stack. -/
theorem rstep_poly : PolyT (rstep M) := by
  have h1 := IsPolyQ.init (M := M); have h2 := IsPolyQ.step (M := M); have h3 := IsPolyQ.out (M := M)
  have h4 := IsPolyQ.ask (M := M); have h5 := IsPolyQ.resume (M := M)
  refine (by fun_prop : PolyT fun l : List M.σ => l.head?.elim [] fun s =>
    (M.out s).elim
      ((M.ask s).elim (M.step s :: l.tail) fun x => x.elim (fun _ => l) fun a' => M.init a' :: l)
      fun b => l.tail.head?.elim l fun s' => M.resume s' (Sum.inr b) :: l.tail.tail).congr fun l => ?_
  rcases l with _ | ⟨s, rest⟩
  · rfl
  · simp only [rstep, List.head?_cons, Option.elim_some, List.tail_cons]
    cases M.out s with
    | none => cases M.ask s with
      | none => rfl
      | some x => cases x <;> rfl
    | some b => cases rest <;> rfl

/-- The query of the whole. -/
theorem rask_poly : PolyT (rask M) := by
  have h3 := IsPolyQ.out (M := M); have h4 := IsPolyQ.ask (M := M)
  refine (by fun_prop : PolyT fun l : List M.σ => l.head?.elim (none : Option Q) fun s =>
    (M.out s).elim ((M.ask s).elim none fun x => x.elim (fun x => some x) fun _ => none) fun _ => none).congr fun l => ?_
  rcases l with _ | ⟨s, rest⟩
  · rfl
  · simp only [rask, List.head?_cons, Option.elim_some]
    cases M.out s with
    | none => cases M.ask s with
      | none => rfl
      | some x => cases x <;> rfl
    | some b => rfl

/-- The answer goes to the running activation. -/
theorem rresume_poly : PolyT fun p : List M.σ × A => rresume M p.1 p.2 := by
  have h5 := IsPolyQ.resume (M := M)
  refine (by fun_prop : PolyT fun p : List M.σ × A => p.1.head?.elim [] fun s => M.resume s (Sum.inl p.2) :: p.1.tail).congr fun p => ?_
  rcases p with ⟨_ | ⟨s, rest⟩, a⟩ <;> rfl

/-- The result of the whole. -/
theorem rout_poly : PolyT (rout M) := by
  have h3 := IsPolyQ.out (M := M)
  refine (by fun_prop : PolyT fun l : List M.σ => l.head?.elim (none : Option β) fun s => bif l.tail.isEmpty then M.out s else none).congr fun l => ?_
  rcases l with _ | ⟨s, _ | ⟨s', rest⟩⟩ <;> rfl

/-- The certificate of `selfCall M`. -/
@[instance_reducible] def selfCallIsPoly : IsPolyQ (selfCall M) where
  enc := (inferInstance : Enc (List M.σ))
  carried := (inferInstance : Carried (List M.σ))
  init := by
    have h1 := IsPolyQ.init (M := M)
    exact (by fun_prop : PolyT fun a : α => [M.init a])
  step := rstep_poly M
  out := rout_poly M
  ask := rask_poly M
  resume := rresume_poly M

end selfCall

/-- `selfCall M` has polynomial-time steps, once and for all depths of the recursion, if M has. -/
theorem selfCallPoly : SelfCallPoly := fun _ _ _ _ _ _ _ _ M ⟨h⟩ => ⟨@selfCallIsPoly _ _ _ _ _ _ _ _ M h⟩

end QueryMachines.Tower
