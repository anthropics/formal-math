/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NetworkStatements

/-! # The algorithm as a step machine: definitions

The time of an algorithm for 3-SAT needs a model of computation. `NetworkStatements.lean` states
what
needs no machine. This file states what the step machines of proof/machines/StepMachines/ add: a
simple model of a computation cut into
steps, and what it means that such a machine decides 3-SAT within c·2^{δn} steps. It has definitions
only, and imports
`NetworkStatements` only (and through it `ThreeSatStatement` and Mathlib).

Read the warning at `DecidesInSteps` before quoting anything from this file. -/

@[expose] public section

namespace Groundwork

/-! ## Step machines -/

/-- The size of a value: about the number of bits needed to write it down. -/
class HasSize (α : Type) where
  size : α → ℕ

export HasSize (size)

section sizes

variable {α β : Type}

instance : HasSize ℕ := ⟨fun n => n.size + 1⟩
instance : HasSize ℤ := ⟨fun z => z.natAbs.size + 1⟩
instance : HasSize Bool := ⟨fun _ => 1⟩
instance : HasSize Unit := ⟨fun _ => 1⟩
instance [HasSize α] [HasSize β] : HasSize (α × β) := ⟨fun p => size p.1 + size p.2⟩
instance [HasSize α] [HasSize β] : HasSize (α ⊕ β) :=
  ⟨fun x => match x with | .inl a => size a + 1 | .inr b => size b + 1⟩
instance [HasSize α] : HasSize (Option α) :=
  ⟨fun x => match x with | none => 1 | some a => size a + 1⟩
instance [HasSize α] : HasSize (List α) := ⟨fun l => (l.map fun x => size x + 1).sum + 1⟩

end sizes

/-- A computation cut into steps: a type `σ` of states with a measure of size (a part of the
machine), the state `init a` in which
the input `a` is handed over, the function `step` from a state to the next, and `out`, where
`out s = some b` means: halted with
result `b`. Nothing restricts `init`, `step`, `out` or the measure of size: they are arbitrary
functions. -/
structure Stepped (α β : Type) : Type 1 where
  σ : Type
  [sz : HasSize σ]
  init : α → σ
  step : σ → σ
  out : σ → Option β

attribute [instance] Stepped.sz

namespace Stepped

variable {α β : Type}

/-- From the state s: halts with b within t steps, all states of size ≤ S. -/
inductive Reaches (M : Stepped α β) (S : ℕ) (b : β) : M.σ → ℕ → Prop
  | halt {s : M.σ} {t : ℕ} : M.out s = some b → size s ≤ S → Reaches M S b s t
  | step {s : M.σ} {t : ℕ} : M.out s = none → size s ≤ S → Reaches M S b (M.step s) t →
      Reaches M S b s (t + 1)

/-- From init a: halts with b within t steps, all states of size ≤ S. -/
def Runs (M : Stepped α β) (a : α) (t S : ℕ) (b : β) : Prop := M.Reaches S b (M.init a) t

end Stepped

/-! ## 3-SAT on a step machine -/

/-- The machine `M`, started on the code of an instance of 3-SAT on n variables, halts within
c·2^{δn} steps with the bit
«satisfiable», and all its states have size polynomial in the length of the input; one constant c
for all instances.

WARNING. `init`, `step` and `out` of a `Stepped` machine are arbitrary Lean functions, and only
applications of `step` are
counted. A machine may decide satisfiability while the input is handed over, in no step at all. The
measure of size is a
field of the machine too, so a machine may call all its states small. So «∃ M, DecidesInSteps M δ»
is trivially true for
every δ and says nothing. What this development
proves is that explicit machines have this property: for every δ > 0, one machine of an explicit
family has
it. These machines are defined in `StepMachines/Prog` and built from the algorithm of Theorem 2, and
their
states are measured by the `HasSize` instances of this file, not by a measure chosen for them. That
statement has content only
together with the definition of these machines: the reader has to look there to judge what the
hand-over, one step and the
reading of the result do (the hand-over, for one, decodes the input). This file does not say whether
each of the three can be done in
polynomial time on a Turing machine. -/
def DecidesInSteps (M : Stepped (List Bool) Bool) (δ : ℝ) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ →
    ∃ (T : ℕ) (b : Bool), M.Runs (Sat3.enc φ) T (c * ((Sat3.enc φ).length + 1) ^ c) b ∧
      (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

end Groundwork
