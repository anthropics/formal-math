/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Unary
public import StepMachines.Prog.Brute

/-! The functions of StepMachines/Prog/Chunks.lean and Brute.lean that the machines run (`block`,
`tri`, `query0`) are
polynomial-time; `ofWord`, `toWord` and `chunks` are in ToTuring/Lib/List2.lean. -/

@[expose] public section

namespace Groundwork

variable {α : Type} [Enc α]

@[fun_prop] theorem block_polyT {ℓ j : α → ℕ} {w : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT j) (h3 : PolyT w) :
    PolyT fun x => block (ℓ x) (j x) (w x) := by unfold block; fun_prop

@[fun_prop] theorem tri_polyT {a b : α → ℕ} (h1 : PolyT a) (h2 : PolyT b) : PolyT fun x => tri (a x) (b x) := by
  unfold tri; fun_prop

@[fun_prop] theorem query0_polyT (K : ℕ) {ℓ v : α → ℕ} {d w : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT d) (h3 : PolyT w)
    (h4 : PolyT v) : PolyT fun x => query0 K (ℓ x) (d x) (w x) (v x) := by
  unfold query0; fun_prop

end Groundwork
