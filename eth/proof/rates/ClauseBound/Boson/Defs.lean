/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import PartitionStatement

/-! # Operators on ℤ[t₁, t₂, …] as matrices: definitions

A monomial is a multiset of positive integers. An operator is given by its matrix K: `K π σ` is the
coefficient of t^π in the image of t^σ. All sums below are finite, so no formal
series are needed. ∇₋ₗ is the multiplication by t_l and ∇ₖ = k·∂/∂t_k (k, l ≥ 1). For a list a of
positive integers (the parts of a monomial), `op a r` is the matrix of the operator a[r] of
Appendix B of the paper, defined by the recursion that the paper calls (O2). Definitions only. -/

@[expose] public section

namespace ClauseBound.Boson

open Finset

/-- The matrix of an operator. -/
abbrev Ker : Type := Multiset ℕ → Multiset ℕ → ℤ

/-- The coefficient of ∇₋ᵣ in the series that belongs to t_n: C(r − 1, n − 1) for r ≠ 0, and 0 for r = 0. -/
def bet (n : ℕ) (r : ℤ) : ℤ := if r = 0 then 0 else Ring.choose (r - 1) (n - 1)

/-- ∇₋ₗ ∘ K. -/
def cre (l : ℕ) (K : Ker) : Ker := fun π σ => if l ∈ π then K (π.erase l) σ else 0

/-- K ∘ ∇ₖ. -/
def ann (K : Ker) (k : ℕ) : Ker := fun π σ => k * σ.count k * K π (σ.erase k)

/-- The normally ordered product of the series of t_n with a family of operators F: Σ_{l ≥ 1} C(l−1,
n−1)·∇₋ₗ∘F(r − l) + Σ_{k ≥ 1} C(−k−1, n−1)·F(r + k)∘∇ₖ. At (π, σ) only the l in π and the k in σ
count. -/
def nop (n : ℕ) (F : ℤ → Ker) (r : ℤ) : Ker := fun π σ =>
  ∑ l ∈ π.toFinset, bet n l * cre l (F (r - l)) π σ + ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ

/-- The identity. -/
def one : Ker := fun π σ => if π = σ then 1 else 0

/-- a[r], for the monomial whose parts are listed in a. -/
def op : List ℕ → ℤ → Ker
  | [], r => if r = 0 then one else 0
  | n :: a, r => nop n (op a) r

/-- The monomials of weight m: the multisets of positive integers with sum m. -/
def P (m : ℕ) : Finset (Multiset ℕ) := (univ : Finset (Nat.Partition m)).image fun q => q.parts

/-- The same for an integer m; empty for m < 0. -/
def Pz (m : ℤ) : Finset (Multiset ℕ) := if 0 ≤ m then P m.toNat else ∅

/-- The matrix of a[r] ∘ b[r']. -/
def mul2 (a : List ℕ) (r : ℤ) (b : List ℕ) (r' : ℤ) : Ker := fun π σ => ∑ τ ∈ Pz (σ.sum + r'), op a r π τ * op b r' τ σ

/-- Γ_{j,n} = n·C(−n−1, j−1) = (−1)^{j−1}·(j+n−1)!/((j−1)!·(n−1)!). -/
def Gam (j n : ℕ) : ℤ := n * Ring.choose (-(n : ℤ) - 1) (j - 1)

/-- All parts are positive. -/
def Pos (a : List ℕ) : Prop := ∀ n ∈ a, 1 ≤ n

end ClauseBound.Boson
