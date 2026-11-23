/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Task

/-!
# Runs of automata

A letter of a run is `none` (idle) or a letter on a channel. The value of an automaton at an input is the sum,
over all runs of length `t` that put the same word on both sides of every tape and the input on the input
channels, of their weights.
-/

namespace Nc

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]

/-- A letter of a run. -/
abbrev Letter (S J Γ : Type*) := Option (Ch S J × Γ)

/-- What a run emits. -/
def emit (o : List (Letter S J Γ)) : Ch S J → List Γ := proj o.reduceOption

/-- The run is matched: both sides of every tape agree, and the inputs are `u`. -/
def Matched (o : List (Letter S J Γ)) (u : J → List Γ) : Prop :=
  (∀ s, emit o (.tp s false) = emit o (.tp s true)) ∧ ∀ j, emit o (.inp j) = u j

instance (o : List (Letter S J Γ)) (u : J → List Γ) : Decidable (Matched o u) := by
  unfold Matched; infer_instance

/-- The value of an automaton with transition matrices `mu`, initial state `i` and final state `e` at the input
`u`: the sum over the matched runs of length `t`. -/
def runVal (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (t : ℕ) (u : J → List Γ) : F :=
  ∑ o : Fin t → Letter S J Γ, if Matched (List.ofFn o) u then ((List.ofFn o).map mu).prod i e else 0

end Nc
