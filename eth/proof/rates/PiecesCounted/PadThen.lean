/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCountedStatement
public import ToTuring.Poly.Comb
import PiecesCounted.Sizes
import Mathlib.Tactic

/-! # From a padding string to counted operations

In `AppRunningTimeStatement.lean`, «within T operations» is rendered by a padding string: a function
f of the input and a list of units that is polynomial-time in both and gives the right value once
the list has at least T units. `padThen N f` is the step machine that writes N a units, one in each
step, and then applies f in one step.
It halts within N a + 1 steps with the value of f at exactly N a units, its states hold the input,
the number N a and the units written so far, and its steps are polynomial-time if N and f are. This
is the extreme case (3) of the head of proof/machines/QueryMachines/Kernel.lean: the number of steps
means something only together with the bound on the states. -/

public section

namespace PiecesCounted

open Groundwork

variable {α β : Type}

/-- Write N a units, one in each step; then f of the input and the units, in one step. A state is
(input, N a, units written so far), or the result. -/
@[expose] def padThen [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) : Stepped α β where
  σ := (α × ℕ × List Unit) ⊕ β
  init a := .inl (a, N a, [])
  step s := s.elim (fun p => if p.2.2.length < p.2.1 then .inl (p.1, p.2.1, () :: p.2.2) else .inr (f (p.1, p.2.2))) fun b => .inr b
  out s := s.elim (fun _ => none) fun b => some b

/-- From the state with j units written, where j + k = N a, the machine halts after k + 1 more steps
with the value of f at N a units. -/
theorem padThen_reaches [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) (a : α) {S : ℕ} (h1 : size a + size (N a) + (2 * N a + 1) + 1 ≤ S)
    (h2 : size (f (a, List.replicate (N a) ())) + 1 ≤ S) (k : ℕ) :
    ∀ j, j + k = N a → (padThen N f).Reaches S (f (a, List.replicate (N a) ())) (.inl (a, N a, List.replicate j ())) (k + 1) := by
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = N a := by omega
    refine .step rfl ?_ ?_
    · change size a + (size (N a) + size (List.replicate (N a) ())) + 1 ≤ S
      rw [size_units, List.length_replicate]
      omega
    · have hn : ¬ (List.replicate (N a) ()).length < N a := by rw [List.length_replicate]; omega
      have e : (padThen N f).step (.inl (a, N a, List.replicate (N a) ())) = .inr (f (a, List.replicate (N a) ())) := if_neg hn
      rw [e]
      exact .halt rfl (by change size (f (a, List.replicate (N a) ())) + 1 ≤ S; exact h2)
  | succ k ih =>
    intro j hj
    refine .step rfl ?_ ?_
    · change size a + (size (N a) + size (List.replicate j ())) + 1 ≤ S
      rw [size_units, List.length_replicate]
      omega
    · have hn : (List.replicate j ()).length < N a := by rw [List.length_replicate]; omega
      have e : (padThen N f).step (.inl (a, N a, List.replicate j ())) = .inl (a, N a, List.replicate (j + 1) ()) := if_pos hn
      rw [e]
      exact ih (j + 1) (by omega)

/-- The machine halts within N a + 1 steps with the value of f at N a units; S bounds the input with
the number and the units, and the result. -/
theorem padThen_runs [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) (a : α) {S : ℕ} (h1 : size a + size (N a) + (2 * N a + 1) + 1 ≤ S)
    (h2 : size (f (a, List.replicate (N a) ())) + 1 ≤ S) : (padThen N f).Runs a (N a + 1) S (f (a, List.replicate (N a) ())) :=
  padThen_reaches N f a h1 h2 (N a) 0 (by omega)

section poly

variable [Enc α] [Enc β] {N : α → ℕ} {f : α × List Unit → β}

/-- The hand-over of the input is polynomial-time. -/
theorem padThen_init (hN : PolyT N) : PolyT fun a : α => (.inl (a, N a, []) : (α × ℕ × List Unit) ⊕ β) := by fun_prop

/-- A step is polynomial-time. -/
theorem padThen_step (hf : PolyT f) : PolyT fun s : (α × ℕ × List Unit) ⊕ β =>
    s.elim (fun p => if p.2.2.length < p.2.1 then (.inl (p.1, p.2.1, () :: p.2.2) : (α × ℕ × List Unit) ⊕ β) else .inr (f (p.1, p.2.2))) fun b => .inr b := by fun_prop

/-- Reading the result is polynomial-time. -/
theorem padThen_out : PolyT fun s : (α × ℕ × List Unit) ⊕ β => s.elim (fun _ => (none : Option β)) fun b => some b := by fun_prop

/-- The steps of the machine are polynomial-time if N and f are. -/
@[instance_reducible] def padThenIsPolyT [HasSize α] [HasSize β] [Carried α] [Carried β] (hN : PolyT N) (hf : PolyT f) : IsPolyT (padThen N f) where
  enc := (inferInstance : Enc ((α × ℕ × List Unit) ⊕ β))
  carried := (inferInstance : Carried ((α × ℕ × List Unit) ⊕ β))
  init := padThen_init hN
  step := padThen_step hf
  out := padThen_out

end poly

end PiecesCounted
