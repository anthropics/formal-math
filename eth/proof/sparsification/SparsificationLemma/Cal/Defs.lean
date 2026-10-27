/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Log

/-! # The sparsification theorem with Calabro's thresholds: definitions and statements

The numbers x = 32(k−1)²/ε and α = ⌈2(k−1)²·ε⁻¹·⌈log₂ x⌉⌉ are those of Step 5 of Appendix D, here
with ceilings; θ₀ = 2, β₁ = 2, θ_c = α·β_c for c ≥ 1 and
β_c = Σ_{h=1}^{c−1} 4α·β_{c−h}·β_h for c ≥ 2 are Calabro's thresholds, which the paper does not
print. The statements include (i) a bound on the length of a path (`FactI`), (iii) a bound on the
number of leaves of the tree,
and (iv) a bound on β₁ + … + β_{k−1} (`FactIV`); Step 5 of Appendix D cites the bound on the leaves
from Calabro's dissertation.
(i) and (iii) follow from the general theorem `SparsificationLemma.StGen`, as these thresholds
    satisfy `SparsificationLemma.ThrC` with τ = α.
This file has definitions only; the statements are propositions, proved in other files. -/

@[expose] public section

namespace SparsificationLemma.Cal

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

/-! ### The numbers -/

/-- x = 32(k−1)²/ε. -/
def xC (k : ℕ) (ε : ℚ) : ℚ := 32 * ((k : ℚ) - 1) ^ 2 / ε

/-- ⌈log₂ x⌉, computed as the least m with x ≤ 2^m. -/
def logC (k : ℕ) (ε : ℚ) : ℕ := Nat.clog 2 ⌈xC k ε⌉₊

/-- α = ⌈2(k−1)²·ε⁻¹·⌈log₂ x⌉⌉. -/
def alphaC (k : ℕ) (ε : ℚ) : ℕ := ⌈2 * ((k : ℚ) - 1) ^ 2 / ε * (logC k ε : ℚ)⌉₊

/-- β₁ = 2 and β_c = Σ_{h=1}^{c−1} 4α·β_{c−h}·β_h for c ≥ 2. (β₀ = 0 is a convention of this file.) -/
def betaC (α : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | c + 2 => ∑ h : Fin (c + 1), 4 * α * betaC α (c + 1 - h) * betaC α (h + 1)

/-- θ₀ = 2 and θ_c = α·β_c for c ≥ 1. -/
def thetaC (α : ℕ) : ℕ → ℕ
  | 0 => 2
  | c + 1 => α * betaC α (c + 1)

/-- (β₁ + … + β_{k−1})·n: no path of the tree has more steps. -/
def depthC (α k n : ℕ) : ℕ := (∑ c ∈ range k, betaC α c) * n

/-- y = 32(k−1)²·log₂(32α)/(32α). -/
noncomputable def yC (k α : ℕ) : ℝ := 32 * ((k : ℝ) - 1) ^ 2 * Real.logb 2 (32 * (α : ℝ)) / (32 * (α : ℝ))

/-- The formulas Φ₁, …, Φ_s that the procedure outputs on k, n, ε and φ: clauses that contain a
variable together with its negation are deleted first. -/
def sparsify (k n : ℕ) (ε : ℚ) (φ : PFml) : List PFml :=
  outputs (thetaC (alphaC k ε)) k (depthC (alphaC k ε) k n) (noTaut φ)

/-! ### The numbers: statements -/

/-- `logC` is ⌈log₂ x⌉, for k ≥ 2 and ε ∈ (0,1] (then x ≥ 32). -/
def StLogC : Prop := ∀ (k : ℕ) (ε : ℚ), 2 ≤ k → 0 < ε → ε ≤ 1 → ((logC k ε : ℕ) : ℤ) = ⌈Real.logb 2 ((xC k ε : ℚ) : ℝ)⌉

/-- The recursion for β_c in the form of the module docstring. -/
def StBetaRec : Prop := ∀ α c : ℕ, 2 ≤ c → betaC α c = ∑ h ∈ Ico 1 c, 4 * α * betaC α (c - h) * betaC α h

/-- β_c = 2·(8α)^(c−1)·Cat_(c−1), for c ≥ 1. -/
def StBetaCat : Prop := ∀ α c : ℕ, betaC α (c + 1) = 2 * (8 * α) ^ c * catalan c

/-- Cat_j ≤ 4^j. -/
def StCatLe : Prop := ∀ j : ℕ, catalan j ≤ 4 ^ j

/-- β_c ≤ 2·(32α)^(c−1), for c ≥ 1. -/
def StBetaLe : Prop := ∀ α c : ℕ, betaC α (c + 1) ≤ 2 * (32 * α) ^ c

/-- Fact (iv): β₁ + … + β_{k−1} ≤ 4·(32α)^(k−2), for k ≥ 2 and α ≥ 1. -/
def FactIV : Prop := ∀ α k : ℕ, 1 ≤ α → 2 ≤ k → ∑ c ∈ Ico 1 k, betaC α c ≤ 4 * (32 * α) ^ (k - 2)

/-- Calabro's thresholds satisfy the conditions of `ThrC` with τ = α, for every k and every α ≥ 1. -/
def StThrCal : Prop := ∀ α k : ℕ, 1 ≤ α → ThrC k α (thetaC α) (betaC α)

/-- The facts on x and α that are used, for k ≥ 3 and ε ∈ (0,1]: x ≥ 128, α ≥ 2, 32α ≥ 2x·log₂ x,
32α ≤ 2x·⌈log₂ x⌉ + 32; and k² ≤ α. -/
def StAlpha : Prop := ∀ (k : ℕ) (ε : ℚ), 3 ≤ k → 0 < ε → ε ≤ 1 →
  128 ≤ xC k ε ∧ 2 ≤ alphaC k ε ∧ k ^ 2 ≤ alphaC k ε ∧
  2 * ((xC k ε : ℚ) : ℝ) * Real.logb 2 ((xC k ε : ℚ) : ℝ) ≤ 32 * (alphaC k ε : ℝ) ∧
  32 * (alphaC k ε : ℚ) ≤ 2 * xC k ε * (logC k ε : ℚ) + 32

/-- y ≤ ε whenever 32α ≥ 2x·log₂ x, x = 32(k−1)²/ε ≥ 128. -/
def StYLe : Prop := ∀ (k α : ℕ) (ε : ℝ), 2 ≤ k → 0 < ε → 128 ≤ 32 * ((k : ℝ) - 1) ^ 2 / ε →
  2 * (32 * ((k : ℝ) - 1) ^ 2 / ε) * Real.logb 2 (32 * ((k : ℝ) - 1) ^ 2 / ε) ≤ 32 * (α : ℝ) → yC k α ≤ ε

/-- For x ≥ 128: log₂ x + 1 + 16/x ≤ √x. -/
def StSqrt : Prop := ∀ x : ℝ, 128 ≤ x → Real.logb 2 x + 1 + 16 / x ≤ Real.sqrt x

/-- 32α ≤ (8k/ε)³, for k ≥ 3 and ε ∈ (0,1]. -/
def StAlphaLe : Prop := ∀ (k : ℕ) (ε : ℚ), 3 ≤ k → 0 < ε → ε ≤ 1 → 32 * (alphaC k ε : ℝ) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ 3

/-- θ₀ + … + θ_{k−1} = 2 + α·(β₁ + … + β_{k−1}) ≤ 2 + 4α·(32α)^(k−2), which is Calabro's bound on
the number of clauses of a leaf that contain a given literal; and 8·(2 + 4α·(32α)^(k−2)) = 16 +
(32α)^(k−1). -/
def StDegSum : Prop := ∀ α k : ℕ, 1 ≤ α → 2 ≤ k →
  ∑ j ∈ range k, thetaC α j = 2 + α * ∑ c ∈ Ico 1 k, betaC α c ∧
  ∑ j ∈ range k, thetaC α j ≤ 2 + 4 * α * (32 * α) ^ (k - 2) ∧ 8 * (2 + 4 * α * (32 * α) ^ (k - 2)) = 16 + (32 * α) ^ (k - 1)

/-- 2 + 4α·(32α)^(k−2) ≤ (8k/ε)^(3k), for k ≥ 3 and ε ∈ (0,1]. -/
def StDegLe : Prop := ∀ (k : ℕ) (ε : ℚ), 3 ≤ k → 0 < ε → ε ≤ 1 →
  ((2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) : ℕ) : ℝ) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * k)

/-! ### Facts on the tree of the procedure -/

/-- Fact (i): the procedure has stopped at every node that is reached after at most (β₁ + … +
β_{k−1})·n steps, so no path is longer. -/
def FactI : Prop := ∀ (α k n : ℕ) (ψ : PFml), 1 ≤ α → 1 ≤ k → IsKCNF k n ψ →
  ∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, stepC (thetaC α) k x = none

/-- Fact (iii), first part (the second part, y ≤ ε, is `StYLe`): the tree has at most 2^(yn) leaves. -/
def FactIIIy : Prop := ∀ (α k n : ℕ) (ψ : PFml), 1 ≤ α → 2 ≤ k → IsKCNF k n ψ →
  ((tree (thetaC α) k (depthC α k n) ψ).length : ℝ) ≤ (2 : ℝ) ^ (yC k α * (n : ℝ))

/-! ### The theorem -/

/-- **Sparsification of k-CNFs with Calabro's thresholds, as Step 5 of Appendix D uses it.** For k ≥
3, every n, a rational ε ∈ (0,1] and a k-CNF φ on n variables, the outputs are k-CNFs on the same
variables, none with a clause written twice; (a) there are at most 2^(εn) of them; (b) every
assignment that satisfies φ satisfies exactly one of them, and every other assignment satisfies
none; (c) in each of them every variable occurs in at most
2·(8k/ε)^(3k) + 2 clauses. -/
def SparsABC : Prop := ∀ (k n : ℕ) (ε : ℚ) (φ : PFml), 3 ≤ k → 0 < ε → ε ≤ 1 → IsKCNF k n φ →
  (∀ Φ ∈ sparsify k n ε φ, IsKCNF k n Φ ∧ Φ.Nodup) ∧
  ((sparsify k n ε φ).length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) ∧
  (∀ b, ExactlyOne b φ (sparsify k n ε φ)) ∧
  ∀ Φ ∈ sparsify k n ε φ, ∀ v, (occN Φ v : ℝ) ≤ 2 * (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * k) + 2

end SparsificationLemma.Cal
