/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CliqueLevelsStatement
public import LevelsStatement

/-! # «K_ℓ … can be computed from ℓ in time polynomial in K_ℓ», for the numbers K_ℓ of Theorem A

Definitions and two statements; nothing is proved here. The hypothesis of Theorem D (a) asks that
K_ℓ can be computed from ℓ in time polynomial in K_ℓ (`CliqueLevels.ComputesLevels`: a
polynomial-time function that gets ℓ and a bound b in unary and returns K_ℓ in unary if K_ℓ ≤ b, and
nothing otherwise). For the numbers of display (40),
K₀ = 2^{x₀}, g_ℓ = 2^{3ℓ+x₀}K_ℓ, K_{ℓ+1} = g_ℓ², this file names such a function. It makes ℓ rounds
on the pair (2^{3j+x₀}, K_j), in binary, and gives up as soon as K_j would exceed b; since the K_j
increase, it gives up if and only if K_ℓ > b. -/

@[expose] public section

namespace CliqueLevels

open Groundwork Printed

/-- One round under the bound b: (2^{3j+x₀}, K_j) becomes (8·2^{3j+x₀}, (2^{3j+x₀}K_j)²) if the new
K is at most b; else nothing. -/
def roundUnder (b : ℕ) (s : Option (ℕ × ℕ)) : Option (ℕ × ℕ) := s.bind fun pk => if (pk.1 * pk.2) ^ 2 ≤ b then some (8 * pk.1, (pk.1 * pk.2) ^ 2) else none

/-- From (ℓ, b) in unary: K_ℓ in unary if K_ℓ ≤ b, else nothing. -/
def levelsUnder (x₀ : ℕ) (p : List Unit × List Unit) : Option (List Unit) :=
  (p.1.foldl (fun s _ => roundUnder p.2.length s) (if 2 ^ x₀ ≤ p.2.length then some (2 ^ x₀, 2 ^ x₀) else none)).map fun pk => unary pk.2

/-- The numbers K_ℓ of display (40) are computed from ℓ in time polynomial in K_ℓ, by
`levelsUnder x₀`. -/
def LevelsAreComputed : Prop := ∀ x₀ : ℕ, ComputesLevels (Levels.Gen.K x₀) (levelsUnder x₀)

/-- `Solves` and `SolvesInFactor` only weaken when the constant C₀ grows (for K_ℓ ≥ 1). -/
def SolvesGrowsWithTheConstant : Prop := ∀ (M : QueryMachines.QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ C₁ : ℕ), (∀ l, 1 ≤ K l) → C₀ ≤ C₁ →
  (Solves M K e C₀ → Solves M K e C₁) ∧ (SolvesInFactor M K e C₀ → SolvesInFactor M K e C₁)

end CliqueLevels
