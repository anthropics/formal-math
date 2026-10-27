/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Definitions for a recursion with single-bit pieces, which the paper does not use

This file holds definitions only, for a variant of the recursion that the paper does not state: the
crossing is uncrossed bit by bit,
[x=v][y=u] = [x=u][y=v] − s(x,y)·s(u,v), as in Appendix H, and the pieces A_i group the terms by the
number of uncrossed bits; the constant ρ = ¼ log₂ 12
(the count by ranks for single bits in Appendix H) takes the place of the paper's ρ = 11/12. It also
defines the value Z of a clique of tensors, arithmetic formulas, the bound `Within`, and labels by
strings of Bell states.
It imports Mathlib and `ThreeSatStatement` only. `n` stands for λ throughout.

Time. The paper measures the time of an algorithm. In `Within` time is replaced by a measure that
needs no
machine: the size of an arithmetic formula (+, ×, integer constants) that computes Z from the
entries of the tensors.
This is a non-uniform measure, so `Within` is a statement on tensor networks, not on 3-SAT: a
constant of any size counts as one leaf, the bit lengths of the entries play no role, and a formula
gets for free what an
algorithm has to search for or decode. On the other hand a formula is a
tree: nothing computed once can be used twice. -/

@[expose] public section

namespace Groundwork

open Finset

/-! ## The problem -/

/-- A λ-bit index. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- An arbitrary tensor for every node of the complete graph on `J`: `W v h` is the entry of the
tensor of `v` at the
indices `h w` of the edges {v,w}. The argument `h v` is a dummy: `Z` reads only entries where it is
0…0. -/
abbrev Tensors (J : Type) (n : ℕ) : Type := J → (J → Bits n) → ℤ

/-- The ways to give every edge an index: `x a b = x b a` is the index of the edge {a,b}, and
`x a a` is 0…0. -/
def edgeIndices (J : Type) [Fintype J] [DecidableEq J] (n : ℕ) : Finset (J → J → Bits n) :=
  univ.filter fun x => (∀ a b, x a b = x b a) ∧ ∀ a, x a a = fun _ => false

/-- Z = Σ ∏_v W_v, summed over all index bits. -/
def Z {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} (W : Tensors J n) : ℤ :=
  ∑ x ∈ edgeIndices J n, ∏ v, W v (x v)

/-- N = C(K,2)·λ, the number of index bits. -/
def N (K n : ℕ) : ℕ := K.choose 2 * n

/-- Arithmetic formulas over the variables `V`. -/
inductive Formula (V : Type) : Type
  | var (v : V)
  | const (c : ℤ)
  | add (a b : Formula V)
  | mul (a b : Formula V)

/-- The value of a formula. -/
def Formula.eval {V : Type} (x : V → ℤ) : Formula V → ℤ
  | .var v => x v
  | .const c => c
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- The size of a formula: its number of leaves. -/
def Formula.size {V : Type} : Formula V → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add a b => a.size + b.size
  | .mul a b => a.size + b.size

/-- The variables of the problem: one for every entry of every tensor. -/
abbrev Entry (J : Type) (n : ℕ) : Type := J × (J → Bits n)

/-- The formula `φ` computes Z, for all tensors. -/
def Formula.ComputesZ {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} (φ : Formula (Entry J n)) : Prop :=
  ∀ W : Tensors J n, φ.eval (fun p => W p.1 p.2) = Z W

/-- Formulas of size 2^{eN}·poly(λ) compute Z, for fixed K and all λ: formula size in place of time.
The constant `C` may
depend on `K` and `e`, not on λ. -/
def Within (K : ℕ) (e : ℝ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∃ φ : Formula (Entry (Fin K) n), φ.ComputesZ ∧
    (φ.size : ℝ) ≤ C * ((n : ℝ) + 1) ^ C * (2 : ℝ) ^ (e * (N K n : ℝ))

/-- ρ = ¼ log₂ 12. -/
noncomputable def ρ : ℝ := Real.logb 2 12 / 4

/-! ## Uncrossing -/

/-- s(p,q) = (−1)^p [p ≠ q]. -/
def s (p q : Bool) : ℤ := if p = q then 0 else if p then -1 else 1

/-- One bit of the crossing: [x = v][y = u] (the two diagonals of the rectangle with x, y on top and
u, v below). -/
def X₁ (x y u v : Bool) : ℤ := if x = v ∧ y = u then 1 else 0

/-- One bit of the uncrossed term: [x = u][y = v] (the two vertical sides). -/
def I₁ (x y u v : Bool) : ℤ := if x = u ∧ y = v then 1 else 0

/-- The crossing of two λ-bit diagonals: [x = v][y = u]. -/
def cross {n : ℕ} (x y u v : Bits n) : ℤ := if x = v ∧ y = u then 1 else 0

/-! ## Grouping -/

/-- A_i: the sum, over the sets S of i bit positions, of the product of −s(x_k,y_k)·s(u_k,v_k) for k
∈ S and [x_k = u_k][y_k = v_k] for the other k. -/
def A (n i : ℕ) (x y u v : Bits n) : ℤ :=
  ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
    (∏ k ∈ S, -(s (x k) (y k) * s (u k) (v k))) * ∏ k ∈ Sᶜ, I₁ (x k) (y k) (u k) (v k)

/-- The names of the four Bell states: (false,false) is Φ⁺, (false,true) is Φ⁻, (true,false) is Ψ⁺,
(true,true) is the singlet. -/
abbrev Bell : Type := Bool × Bool

/-- The number of singlets in a string. -/
def singlets {n : ℕ} (β : Fin n → Bell) : ℕ := #{k | β k = (true, true)}

/-- The number of states other than Φ⁺ in a string. -/
def others {n : ℕ} (β : Fin n → Bell) : ℕ := #{k | β k ≠ (false, false)}

/-- The strings with at least i singlets. -/
def rowLabels (n i : ℕ) : Finset (Fin n → Bell) := univ.filter fun β => i ≤ singlets β

/-- The strings with at most i states other than Φ⁺. -/
def colLabels (n i : ℕ) : Finset (Fin n → Bell) := univ.filter fun β => others β ≤ i

end Groundwork
