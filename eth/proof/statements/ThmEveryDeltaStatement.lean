/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement

/-! # Theorem 2 in its decision form: for every constant δ > 0, 3-SAT on n variables can be decided in time O(2^{δn})

This file only *states* the theorem: it has definitions and no proofs, and it imports only
`ThreeSatStatement.lean` (definitions only; that file imports Mathlib only).
The statement is `Sat3.ThmEveryDelta`, at the end.

"Algorithm" means a deterministic Turing machine with finitely many stacks, as defined in Mathlib
(`Turing.FinTM2`);
"time" is its number of steps. -/

@[expose] public section

namespace Sat3

open Turing

/-! The definitions of 3-SAT and of the input string of an instance (`Lit`, `CNF`, `Satisfiable`,
`Is3CNF`, `slot`, `enc`) are those of `ThreeSatStatement.lean`. -/

/-! ### Time -/

/-- The machine `M`, started with the input string of φ on its input stack and all other stacks
empty, halts after at most `t`
steps, with the single bit `b` on its output stack, all other stacks empty, and its internal state
back at its initial value.
(One step, `Turing.TM2.step`, runs the instructions at the current label as far as the next `goto`
or `halt`: a number of pushes and
pops that is bounded for a fixed machine.) -/
def HaltsWith (M : TM2ComputableAux Bool Bool) {n : ℕ} (φ : CNF n) (b : Bool) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((enc φ).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)

/-- "3-SAT can be decided in time O(2^{δn})": there are one machine `M` and one constant `c` such
that, for every n, on every
instance φ of 3-SAT on n variables, `M` halts after at most c · 2^{δn} steps and outputs whether φ
is satisfiable.
(Mathlib makes the sets of stacks, labels and internal states of a machine finite, and the alphabet
of the input stack; the
condition `Finite (M.tm.Γ k)` makes the alphabet of every stack finite. A machine can push only
finitely many different symbols
in any case, since its instructions compute them from the internal state; the condition makes the
finiteness explicit.) -/
def DecidedInTime (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → ∃ (b : Bool) (t : ℕ),
      (b = true ↔ Satisfiable φ) ∧ (t : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) ∧ HaltsWith M φ b t

/-- **Theorem 2 in its decision form.** For every constant δ > 0, 3-SAT on n variables can be
decided in time O(2^{δn}). -/
def ThmEveryDelta : Prop := ∀ δ : ℝ, 0 < δ → DecidedInTime δ

end Sat3
