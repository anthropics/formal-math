/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Defs

/-! # A toy recursion: definitions and statements

Definitions and statements only; nothing is proved here. The toy shows that the hypotheses of
`TowerRuns` and `TowerPoly` can be met by explicit machines, with the depth as a part of the input.

F(0, f) = f(ε), F(ℓ+1, f) = F(ℓ, q ↦ f(0q)) + F(ℓ, q ↦ f(1q)): the sum of f over all bit strings of
length ℓ. A context is a pair (ℓ, b): the depth, and the bit that the instance puts in front of its
queries to the tables of its caller.
The solver on (0, b) asks its tables for the entry of the empty string. On (ℓ+1, b) it calls (ℓ, 0)
and (ℓ, 1), and adds the two results in one step of its own. The procedure on ((ℓ, b), q) asks the
tables of the caller for the entry of bq.
There is no query of the second kind. All ten functions are written with eliminators and, in two
places, «if», so that the tactic `fun_prop` proves the certificates as they stand.

The specification is chosen for an outermost instance of depth at most ℓ0 whose entries are at most
M0, as the comment on `Spec` allows. -/

@[expose] public section

namespace QueryMachines.Tower.Toy

open Groundwork

/-- The empty type has nothing to write. The instance is active only where this namespace is open. -/
scoped instance encEmpty : Enc Empty := ⟨fun e => e.elim⟩

/-! ### The two machines -/

/-- Where the solver stands: at the start; with the first result; with both results; done. -/
abbrev Ph : Type := Unit ⊕ (ℕ ⊕ ((ℕ × ℕ) ⊕ ℕ))

/-- The solver starts with the depth. -/
def solInit (c : ℕ × Bool) : ℕ × Ph := (c.1, Sum.inl ())

/-- Its one step of its own: the two results are added. -/
def solStep (s : ℕ × Ph) : ℕ × Ph :=
  s.2.elim (fun _ => s) fun r => r.elim (fun _ => s) fun r' => r'.elim (fun p => (s.1, Sum.inr (Sum.inr (Sum.inr (p.1 + p.2))))) fun _ => s

/-- Its result, when it is done. -/
def solOut (s : ℕ × Ph) : Option ℕ :=
  s.2.elim (fun _ => none) fun r => r.elim (fun _ => none) fun r' => r'.elim (fun _ => none) fun v => some v

/-- At the start: at depth 0 the entry of the empty string, else the call of (ℓ − 1, 0). With the
first result: the call of (ℓ − 1, 1). -/
def solAsk (s : ℕ × Ph) : Option ((ℕ × Bool) ⊕ (List Bool ⊕ Empty)) :=
  s.2.elim (fun _ => if s.1 = 0 then some (Sum.inr (Sum.inl [])) else some (Sum.inl (s.1 - 1, false))) fun r => r.elim (fun _ => some (Sum.inl (s.1 - 1, true))) fun _ => none

/-- How it goes on with an answer. -/
def solResume (s : ℕ × Ph) (v : ℕ) : ℕ × Ph :=
  s.2.elim (fun _ => if s.1 = 0 then (s.1, Sum.inr (Sum.inr (Sum.inr v))) else (s.1, Sum.inr (Sum.inl v))) fun r => r.elim (fun u => (s.1, Sum.inr (Sum.inr (Sum.inl (u, v))))) fun _ => s

/-- The solver. -/
def Sol : QueryMachine ((ℕ × Bool) ⊕ (List Bool ⊕ Empty)) ℕ (ℕ × Bool) ℕ where
  σ := ℕ × Ph
  init := solInit
  step := solStep
  out := solOut
  ask := solAsk
  resume := solResume

/-- The procedure starts with the bit of the callee and the callee's query. -/
def innInit (x : (ℕ × Bool) × List Bool) : (Bool × List Bool) ⊕ ℕ := Sum.inl (x.1.2, x.2)

/-- Its result, when it has the answer. -/
def innOut (s : (Bool × List Bool) ⊕ ℕ) : Option ℕ := s.elim (fun _ => none) fun v => some v

/-- Its one query: the entry of bq in the tables of the caller. -/
def innAsk (s : (Bool × List Bool) ⊕ ℕ) : Option (List Bool ⊕ Empty) := s.elim (fun p => some (Sum.inl (p.1 :: p.2))) fun _ => none

/-- The answer is the result. -/
def innResume (s : (Bool × List Bool) ⊕ ℕ) (v : ℕ) : (Bool × List Bool) ⊕ ℕ := s.elim (fun _ => Sum.inr v) fun _ => s

/-- The procedure. -/
def Inn : QueryMachine (List Bool ⊕ Empty) ℕ ((ℕ × Bool) × List Bool) ℕ where
  σ := (Bool × List Bool) ⊕ ℕ
  init := innInit
  step := fun s => s
  out := innOut
  ask := innAsk
  resume := innResume

/-! ### The specification -/

/-- F(0, f) = f(ε), F(ℓ+1, f) = F(ℓ, q ↦ f(0q)) + F(ℓ, q ↦ f(1q)). A missing entry counts 0. -/
def sumF : ℕ → (List Bool → Option ℕ) → ℕ
  | 0, f => (f []).getD 0
  | l + 1, f => sumF l (fun q => f (false :: q)) + sumF l (fun q => f (true :: q))

/-- All bit strings of length ℓ. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | l + 1 => (words l).map (false :: ·) ++ (words l).map (true :: ·)

/-- The specification, for outermost instances of depth at most ℓ0 with entries at most M0. -/
def spec (ℓ0 M0 : ℕ) : Spec (ℕ × Bool) (List Bool) ℕ where
  lev c := c.1
  Good c f := c.1 ≤ ℓ0 ∧ ∀ q : List Bool, q.length = c.1 → ∃ a, a ≤ M0 ∧ f q = some a
  val c f := sumF c.1 f
  Child c _ c' := c'.1 + 1 = c.1
  tab c' f q := if q.length = c'.1 then f (c'.2 :: q) else none

/-- The cost of the solver: one query at depth 0; two calls and one step above. -/
def TS : ℕ → ℕ → ℕ → ℕ
  | 0, _, tq => tq
  | _ + 1, tc, _ => 2 * tc + 1

/-- The cost of the procedure: one query. -/
def TI (_ tq : ℕ) : ℕ := tq

/-- The bound on the sizes of the states of the solver. -/
def SS (ℓ0 M0 : ℕ) : ℕ := ℓ0.size + 2 * (2 ^ ℓ0 * M0).size + 6

/-- The bound on the sizes of the states of the procedure. -/
def SI (ℓ0 M0 : ℕ) : ℕ := 2 * ℓ0 + M0.size + 5

/-- The bound on the sizes of the contexts. -/
def SC (ℓ0 : ℕ) : ℕ := ℓ0.size + 2

/-- No query of the second kind: no answers. -/
def noG : Empty → Option ℕ := fun e => e.elim

/-- No query of the second kind: no prices. -/
def noW : Empty → ℕ := fun e => e.elim

/-! ### What is claimed -/

/-- The tower of the toy has polynomial-time steps; the depth is part of its input. -/
def ToyPoly : Prop := (tower Sol Inn).PolyTimeSteps

/-- The two machines meet the specification, so the hypotheses of `TowerRuns` are not empty. -/
def ToyMeets : Prop := ∀ ℓ0 M0 : ℕ, (spec ℓ0 M0).Meets noG noW Sol Inn TS TI (SS ℓ0 M0) (SI ℓ0 M0) (SC ℓ0)

/-- ONE machine, on the input (ℓ, b), with query access to a table f whose entries for the bit
strings of length ℓ are at most M0, at t operations per query: it returns the sum of f over all bit
strings of length ℓ within 2^ℓ·(t + 2ℓ + 5) operations. -/
def ToyRuns : Prop := ∀ (ℓ M0 t : ℕ) (b : Bool) (f : List Bool → Option ℕ), (∀ q : List Bool, q.length = ℓ → ∃ a, a ≤ M0 ∧ f q = some a) →
  (tower Sol Inn).Within (Sum.elim f noG) (Sum.elim (fun _ => t) noW) (ℓ, b) (2 ^ ℓ * (t + 2 * ℓ + 5)) (towerSize ℓ (SS ℓ M0) (SI ℓ M0) (SC ℓ)) (((words ℓ).map fun q => (f q).getD 0).sum)

end QueryMachines.Tower.Toy
