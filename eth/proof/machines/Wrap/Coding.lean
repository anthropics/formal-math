/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Wrap.Defs
public import CircuitLowerBound.Tab.Frame
public import ToTuring.EncLemmas

/-! # A coding of the configurations of a machine as data of the framework for polynomial time

`Coding M` bundles what the simulation uses: configurations of M written as values of the plain type
`Rep`; polynomial-time functions for the start (from bit strings to `Rep`), for one step (on `Rep`;
`CircuitLowerBound.Tab.stay M` is Mathlib's step, where a halted machine stays as it is) and for
reading the output (on `Rep`); and
bounds on the sizes. CodingExists.lean proves that every machine with finite alphabets has a coding;
Sim.lean derives the machine around M from a coding. -/

@[expose] public section

namespace Wrap

open Turing Groundwork

/-- The type in which configurations are written: (number of the label or «halted», number of the
state), and the stacks, in a fixed order, as lists of numbers of symbols. -/
abbrev Rep : Type := (ℕ × ℕ) × List (List ℕ)

/-- A coding of the configurations of M. -/
structure Coding (M : TM2ComputableAux Bool Bool) where
  /-- the value that stands for a configuration -/
  rep : M.tm.Cfg → Rep
  /-- one step, on values -/
  step : Rep → Rep
  /-- the start configuration on the bit string x, as a value -/
  init : List Bool → Rep
  /-- the output, if the value stands for a halted configuration -/
  out : Rep → Option (List Bool)
  /-- a constant for the two bounds on sizes -/
  a : ℕ
  /-- the step is polynomial-time -/
  step_poly : PolyT step
  /-- the start is polynomial-time -/
  init_poly : PolyT init
  /-- reading the output is polynomial-time -/
  out_poly : PolyT out
  /-- the step on values is the step of M -/
  step_rep : ∀ c : M.tm.Cfg, step (rep c) = rep (CircuitLowerBound.Tab.stay M c)
  /-- the start on values is the start configuration of M -/
  init_rep : ∀ x : List Bool, init x = rep (initList M.tm (x.map M.inputAlphabet.invFun))
  /-- on a halted configuration the output is the content of the output stack -/
  out_halted : ∀ c : M.tm.Cfg, c.l = none → out (rep c) = some ((c.stk M.tm.k₁).map M.outputAlphabet)
  /-- on a configuration that is not halted there is no output -/
  out_running : ∀ c : M.tm.Cfg, c.l ≠ none → out (rep c) = none
  /-- the start configuration is at most linear in the input -/
  size_init : ∀ x : List Bool, size (init x) ≤ a * (x.length + 1)
  /-- a step adds at most a constant to the size -/
  size_step : ∀ c : M.tm.Cfg, size (rep (CircuitLowerBound.Tab.stay M c)) ≤ size (rep c) + a

end Wrap
