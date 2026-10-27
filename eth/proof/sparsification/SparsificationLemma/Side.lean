/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
import StepMachines.Math.SparsifyList

/-! # No choice depends on the side list

This file proves four statements of proof/sparsification/SparsificationLemma/Defs.lean: `StSide`,
`StUnchanged`, `StOutputsSame` and `StNodup`.
The rule looks only at the first component of a node. So a map that changes only side lists, or
forgets them, carries one step to one step, and therefore the leaves of one tree to the leaves of
the other, in the same order (`Groundwork.Sparsify.leaves_sim`).
For `StOutputsSame`: the output `out` keeps only the side clauses of one literal, and the clauses xᵢ
∨ ¬xᵢ have two. `StNodup` holds because `out` writes every clause once. -/

public section

namespace SparsificationLemma

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate

/-- The tree that starts with the side list X has the same first components, and X behind every side
list. -/
theorem stSide : StSide := by
  intro θ k D r X
  have h := (leaves_sim (step' := stepC θ k) (step := stepC θ k) (f := fun x : CNode => (x.1, x.2 ++ X)) (I := fun _ => True)
    (fun s _ => by cases hp : pickK θ k s.1 <;> simp [stepC, hp]) (fun _ _ _ _ _ => ⟨trivial, trivial⟩) D (r, []) trivial).1
  simpa using h.symm

/-- The first components of the nodes are the nodes of the unchanged procedure. -/
theorem stUnchanged : StUnchanged := by
  intro θ k D r X
  exact (leaves_sim (step' := stepC θ k) (step := stepK θ k) (f := Prod.fst) (I := fun _ => True)
    (fun s _ => by cases hp : pickK θ k s.1 <;> simp [stepC, stepK, hp]) (fun _ _ _ _ _ => ⟨trivial, trivial⟩) D (r, X) trivial).1

/-- The clauses xᵢ ∨ ¬xᵢ do not reach the output: they have two literals. -/
theorem sideU_append_taut (X : PFml) (n : ℕ) : sideU (X ++ taut n) = sideU X := by
  have h : ((taut n).filter fun C => C.length == 1) = [] := by
    refine List.filter_eq_nil_iff.2 fun C hC => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
    simp
  rw [sideU, List.filter_append, h, List.append_nil, sideU]

/-- The outputs are those of the tree whose root has the n clauses xᵢ ∨ ¬xᵢ as its side list. -/
theorem stOutputsSame : StOutputsSame := by
  intro θ k D n ψ
  have h : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
  rw [h, stSide θ k D (rootP ψ) (taut n), List.map_map, outputs, tree, root]
  refine List.map_congr_left fun x _ => ?_
  simp [out, leafM, sideU_append_taut]

/-- No output has a clause twice. -/
theorem stNodup : StNodup := by
  intro θ k D ψ Φ hΦ
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hΦ
  exact List.nodup_dedup _

end SparsificationLemma
