/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Statements on the number of partitions (pure mathematics; definitions and statements only; imports Mathlib only) -/

@[expose] public section

namespace Partitions

/-- p(E), the number of partitions of E; p(0) = 1. -/
def p (E : ℕ) : ℕ := Fintype.card (Nat.Partition E)

/-- π·√(2/3). -/
noncomputable def cHR : ℝ := Real.pi * Real.sqrt (2 / 3)

/-- κ = π·√(2/3)/ln 2. -/
noncomputable def kappa : ℝ := cHR / Real.log 2

/-- κ·√E − B·log₂ E − C ≤ log₂ p(E) for E ≥ 1, and log₂ p(E) ≤ κ·√E + C for E ≥ 0. With B = 1 this
follows from the asymptotic formula of Hardy and Ramanujan. -/
def Bounds (B C : ℝ) : Prop :=
  (∀ E : ℕ, 1 ≤ E → kappa * Real.sqrt E - B * Real.logb 2 E - C ≤ Real.logb 2 (p E)) ∧
    ∀ E : ℕ, Real.logb 2 (p E) ≤ kappa * Real.sqrt E + C

end Partitions
