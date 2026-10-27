/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.BigOperators

/-! # Pieces with parameters (ρ, c), and blocks of bits (pure mathematics; definitions only; imports Mathlib only) -/

@[expose] public section

namespace Pieces

open Finset Polynomial

/-- A string of n bits. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- A function of the four strings x, y, u, v. -/
abbrev Four (n : ℕ) : Type := Bits n → Bits n → Bits n → Bits n → ℤ

/-- [x = v][y = u]. -/
def cross {n : ℕ} : Four n := fun x y u v => if x = v ∧ y = u then 1 else 0

/-- Definition 1, with a bound: F(z,z') = Σ_θ f(z,θ)·f'(z',θ) over θ ∈ {0,1}^c, and all values of f
and f' are below b in absolute value. -/
def FactorsThrough {X X' : Type} (F : X → X' → ℤ) (c : ℕ) (b : ℤ) : Prop :=
  ∃ (f : X → Bits c → ℤ) (f' : X' → Bits c → ℤ),
    (∀ z z', F z z' = ∑ θ, f z θ * f' z' θ) ∧ (∀ z θ, |f z θ| < b) ∧ ∀ z' θ, |f' z' θ| < b

/-- A as a function of (x,y) and (u,v): «row-wise». -/
def rowwise {n : ℕ} (A : Four n) : Bits n × Bits n → Bits n × Bits n → ℤ := fun p q => A p.1 p.2 q.1 q.2

/-- A as a function of (x,u) and (y,v): «column-wise». -/
def colwise {n : ℕ} (A : Four n) : Bits n × Bits n → Bits n × Bits n → ℤ := fun p q => A p.1 q.1 p.2 q.2

/-! ## Pieces with parameters (ρ, c) (Definition 7): parts (a), (b) and the size bounds of (c); the running time is not stated here -/

/-- The data for one λ. -/
structure Family (lam : ℕ) where
  d : ℤ
  I : Finset ℤ
  A : ℤ → Four lam
  crow : ℤ → ℕ
  ccol : ℤ → ℕ

/-- The family has the properties of pieces with parameters (ρ, c) at this λ. -/
structure Family.Is {lam : ℕ} (P : Family lam) (ρ : ℝ) (c : ℕ) : Prop where
  d_pos : 1 ≤ P.d
  sum_eq : ∀ x y u v, ∑ i ∈ P.I, P.A i x y u v = P.d * cross x y u v
  row : ∀ i ∈ P.I, FactorsThrough (rowwise (P.A i)) (P.crow i) (2 ^ (2 * lam) ^ c)
  col : ∀ i ∈ P.I, FactorsThrough (colwise (P.A i)) (P.ccol i) (2 ^ (2 * lam) ^ c)
  caps : ∀ i ∈ P.I, ((P.crow i + P.ccol i : ℕ) : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  card_I : #P.I ≤ (2 * lam) ^ c
  abs_d : P.d < 2 ^ (2 * lam) ^ c
  abs_I : ∀ i ∈ P.I, |i| < 2 ^ (2 * lam) ^ c
  abs_A : ∀ i ∈ P.I, ∀ x y u v, |P.A i x y u v| < 2 ^ (2 * lam) ^ c

/-! ## Blocks of h positions, labels, and the mean μ (a construction that the paper does not state) -/

section Blocks

/-- A label β ∈ {00,01,10,11}^λ. -/
abbrev Lab (n : ℕ) : Type := Fin n → Bool × Bool

variable (n h : ℕ)

/-- ⌈n/h⌉, the number of blocks of h positions in a string of n bits. Position k lies in block k /
h. -/
def nblk : ℕ := (n + h - 1) / h

/-- The positions of block b. -/
def blk (b : ℕ) : Finset (Fin n) := univ.filter fun k => k.val / h = b

variable {n}

/-- The number of blocks b in which β has an odd number of entries 11. -/
def odd (β : Lab n) : ℕ := #{b ∈ range (nblk n h) | Odd #{k ∈ blk n h b | β k = (true, true)}}

variable (n)

/-- μ: the mean of odd(β) over all β, rounded down. -/
def mu : ℕ := (∑ β : Lab n, odd h β) / 4 ^ n

variable {n}

variable (n)

end Blocks

end Pieces
