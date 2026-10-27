/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top
public import LevelsStatement

/-! # The general recursion as a schedule: definitions and an interface statement

Square grids of side g_l = 2^{3l+x₀}·K_l, any pieces. The numbers K_l, g_l are those of
`LevelsStatement.lean`; the precision of the grouping at level l (Lemma 8) is D_l = 3·m·2^{l+4}, so
that
3·m/D_l = 2ζ_l. -/

@[expose] public section

namespace ClauseBound.Gen

open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

/-- n in unary. -/
def rep (n : ℕ) : U := List.replicate n ()

/-- Pieces as programs with parameters (ρ, c): the definition of the paper, with the running time
replaced by the exponent of the pad. -/
structure Par (P : PiecesF) (ρ : ℝ) (c : ℕ) : Prop where
  spec : ∀ h lam, 1 ≤ lam → P.Spec h lam
  caps : ∀ h lam, 1 ≤ lam → (capSum P h lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  cnt : ∀ h lam, 1 ≤ lam → P.cnt h lam ≤ (2 * lam) ^ c
  bits : ∀ h lam, 1 ≤ lam → P.bits h lam ≤ (2 * lam) ^ c
  d : ∀ h lam, 1 ≤ lam → P.d h lam < 2 ^ (2 * lam) ^ c
  need : ∀ h lam, 1 ≤ lam → P.need h lam ≤ c * lam
  m_le : P.m ≤ c

/-- The step from K_{l+1} = g_l² nodes to K_l nodes. -/
def step (P : PiecesF) (x₀ l : ℕ) : Step :=
  ((rep (K x₀ l), rep (g x₀ l), rep (g x₀ l)), (rep (3 * P.m * 2 ^ (l + 4)), []), (false, [], []))

/-- The steps from K_l nodes down to K₀ nodes. -/
def sched (P : PiecesF) (x₀ : ℕ) : ℕ → List Step
  | 0 => []
  | l + 1 => step P x₀ l :: sched P x₀ l

/-- The index of level l. -/
def idx (P : PiecesF) (x₀ l : ℕ) : List Step × U := (sched P x₀ l, rep (K x₀ 0))

/-! ### Pick.lean -/

/-- From a bound in unary: the largest l with K_l ≤ bound, and its index, in polynomial time. -/
def StPick : Prop := ∀ (P : PiecesF) (x₀ : ℕ), ∃ pick : U → U × (List Step × U), PolyT pick ∧
  (∀ b, (pick b).2 = idx P x₀ (pick b).1.length) ∧ (∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length) ∧
  ∀ b, b.length < K x₀ ((pick b).1.length + 1)

end ClauseBound.Gen
