/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ChallengeDeps/Union.lean — TRUSTED Mathlib-only definition layer for the `Union` comparator topic:
the two counting functions beyond ChallengeDeps.lean that the simple-or-on-line inclusion–exclusion
statements of Challenge/Union.lean mention. Each `def` line is character-for-character the one in
Zeta23/Statement.lean §1 (root namespace here, `Zeta23` there, so that Solution/Union.lean can import
both without name clashes).
-/
import ChallengeDeps

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

/-- N₀(T₁,T₂): the zeros ON the critical line Re ρ = 1/2 with T₁ < Im ρ ≤ T₂, with multiplicity. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- Nˢ(T₁,T₂): the number of simple zeros with T₁ < Im ρ ≤ T₂ (anywhere in the strip). -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

end
