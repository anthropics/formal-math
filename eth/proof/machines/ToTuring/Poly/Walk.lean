/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.IsPoly
public import StepMachines.Prog.Walk

/-! `IsPolyT` for `guard` and the depth-first walk of `StepMachines/Prog/Walk.lean`. -/

@[expose] public section

namespace Groundwork

namespace IsPolyT

open Stepped

variable {α β τ ν : Type}

section guard

variable [Enc τ] [Enc ν] [Enc β] {sel : τ → Option ν} {T : Stepped ν β} [IsPolyT T] {d : β}

theorem guard_init (hs : PolyT sel) : PolyT (fun x => (sel x).map T.init) := by
  have := IsPolyT.init (M := T); fun_prop

theorem guard_step : PolyT (fun s : Option T.σ => Option.map T.step s) := by
  have := IsPolyT.step (M := T); fun_prop

theorem guard_out : PolyT (fun s : Option T.σ => match s with | none => some d | some s => T.out s) := by
  have := IsPolyT.out (M := T)
  exact (by fun_prop : PolyT fun s : Option T.σ => s.elim (some d) fun s => T.out s).congr fun s => by cases s <;> rfl

/-- `guard sel T d` runs `T` on `sel x` when that is `some`, and otherwise answers `d` at once. Its
steps are
polynomial-time if `sel` is and the steps of `T` are. -/
@[instance_reducible] def guard (hs : PolyT sel) : IsPolyT (guard sel T d) where
  enc := (inferInstance : Enc (Option T.σ))
  carried := (inferInstance : Carried (Option T.σ))
  init := guard_init hs
  step := guard_step
  out := guard_out

end guard

section walk

variable [Enc ν] {step : ν → Option (ν × ν)}

theorem walkNext_polyT (hs : PolyT step) : PolyT (walkNext step) := by
  have h : PolyT fun p : List ν × ν × List ν => some ((step p.2.1).elim p.2.2 fun q => q.1 :: q.2 :: p.2.2) := by fun_prop
  refine (PolyT.listCases (l := fun st : List ν => st) (d := fun _ => none)
    (f := fun _ s r => some ((step s).elim r fun q => q.1 :: q.2 :: r)) (by fun_prop) (by fun_prop) h).congr fun st => ?_
  rcases st with _ | ⟨s, r⟩
  · rfl
  · simp only [walkNext]; cases step s <;> rfl

theorem walkSel_polyT (hs : PolyT step) : PolyT (walkSel step) := by
  have h : PolyT fun p : List ν × ν × List ν => (step p.2.1).elim (some p.2.1) fun _ => none := by fun_prop
  refine (PolyT.listCases (l := fun st : List ν => st) (d := fun _ => none)
    (f := fun _ s _ => (step s).elim (some s) fun _ => none) (by fun_prop) (by fun_prop) h).congr fun st => ?_
  rcases st with _ | ⟨s, r⟩
  · rfl
  · simp only [walkSel]; cases step s <;> rfl

variable [HasSize ν] [Carried ν] [Enc α] {root : α → ν} {T : Stepped ν Bool} [IsPolyT T]

/-- The depth-first walk from `root x` of the binary tree given by `step` (`none` at a leaf, else
the two children), which
runs `T` at every leaf it visits. Its steps are polynomial-time if `step`, `root` and the steps of
`T` are. -/
@[instance_reducible] def walk (hs : PolyT step) (hr : PolyT root) : IsPolyT (walk step root T) :=
  haveI := guard (T := T) (d := false) (walkSel_polyT hs)
  foldWhile (by fun_prop) (walkNext_polyT hs) (by fun_prop) (by fun_prop)

end walk

end IsPolyT

end Groundwork
