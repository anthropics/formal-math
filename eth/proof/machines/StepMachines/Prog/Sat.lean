/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Count
public import StepMachines.Prog.Walk
public import StepMachines.Prog.Comb
public import StepMachines.Prog.Decode
public import StepMachines.Math.SparsifyProg
public import ThreeSatStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import StepMachines.Math.SparsifyCount

/-! The 3-SAT machine as a program: decode the input, walk the sparsification tree depth-first, test
every leaf;
and bounds on the sizes of lists and literals. -/

namespace Groundwork.Prog

open Groundwork.Sparsify (leaves rootP stepP)

/-- The formula written in the input. -/
@[expose] public def decF (x : List Bool) : Fml := (Decode.dec x).2

/-- Is there an empty clause? -/
@[expose] public def hasNil (ψ : Fml) : Bool := ψ.any List.isEmpty

/-- Is the count positive? -/
@[expose] public def posZ (v : ℤ) : Bool := decide (0 < v)

/-- The 3-SAT machine: decode the input, answer false if there is an empty clause, otherwise walk
the sparsification
tree with parameter τ and answer true iff some leaf passes the test. M is the test of a leaf (a
count that is positive
iff the leaf is satisfiable). -/
@[expose] public def satM (τ : ℕ) (M : Stepped Fml ℤ) : Stepped (List Bool) Bool :=
  Stepped.mapIn decF (Stepped.ite hasNil (Stepped.const false)
    (Stepped.walk (stepP τ) rootP (Stepped.mapOut M posZ)))

/-! ### Sizes -/

theorem sum_size_le {α : Type} [HasSize α] {s : ℕ} (l : List α) (hs : ∀ x ∈ l, size x ≤ s) :
    (l.map fun x => size x + 1).sum ≤ l.length * (s + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := hs x (by simp)
    have h2 := ih fun y hy => hs y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem size_list_le {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k)
    (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by
  rw [size_list]
  exact Nat.succ_le_succ ((sum_size_le l hs).trans (Nat.mul_le_mul_right _ hl))

theorem size_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : size l ≤ n + 2 := by
  have : l.1.size ≤ n := Nat.size_le.2 (h.trans Nat.lt_two_pow_self)
  simp only [size_prod, size_nat, size_bool]
  omega

end Groundwork.Prog
