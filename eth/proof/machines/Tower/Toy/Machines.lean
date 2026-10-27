/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Toy.Defs
public import Tower.PolyTower
public import ToTuring.Lib.Nat1

/-! # A toy recursion: the certificates

The ten functions of the two machines (Toy/Defs.lean) are written with eliminators and «if», so
`fun_prop` proves nine of them polynomial-time as they stand; the tenth, the step of the procedure,
is the identity and is certified by `PolyT.id'`. The tower has its certificate from `towerPoly`. -/

@[expose] public section

namespace QueryMachines.Tower.Toy

open Groundwork Groundwork.PolyT QueryMachines.QueryMachine

/-- The certificate of the solver. -/
@[instance_reducible] def solIsPoly : IsPolyQ Sol where
  enc := (inferInstance : Enc (ℕ × Ph))
  carried := (inferInstance : Carried (ℕ × Ph))
  init := (by unfold solInit; fun_prop : PolyT solInit)
  step := (by unfold solStep; fun_prop : PolyT solStep)
  out := (by unfold solOut; fun_prop : PolyT solOut)
  ask := (by unfold solAsk; fun_prop : PolyT solAsk)
  resume := (by unfold solResume; fun_prop : PolyT fun p : (ℕ × Ph) × ℕ => solResume p.1 p.2)

/-- The certificate of the procedure. -/
@[instance_reducible] def innIsPoly : IsPolyQ Inn where
  enc := (inferInstance : Enc ((Bool × List Bool) ⊕ ℕ))
  carried := (inferInstance : Carried ((Bool × List Bool) ⊕ ℕ))
  init := (by unfold innInit; fun_prop : PolyT innInit)
  step := (PolyT.id' : PolyT fun s : (Bool × List Bool) ⊕ ℕ => s)
  out := (by unfold innOut; fun_prop : PolyT innOut)
  ask := (by unfold innAsk; fun_prop : PolyT innAsk)
  resume := (by unfold innResume; fun_prop : PolyT fun p : ((Bool × List Bool) ⊕ ℕ) × ℕ => innResume p.1 p.2)

/-- The tower of the toy has polynomial-time steps; the depth is part of its input. -/
theorem toyPoly : ToyPoly := towerPoly _ _ _ _ Sol Inn ⟨solIsPoly⟩ ⟨innIsPoly⟩

end QueryMachines.Tower.Toy
