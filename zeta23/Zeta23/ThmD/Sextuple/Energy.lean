/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Kernel
import Mathlib.Data.Matrix.Basic

open scoped BigOperators

noncomputable section

namespace Zeta23.ThmD.Sextuple

/-- The exact affine intercept in the six-translate certificate. -/
def A6 : ℝ := 1 / 80

/-- The exact span slope in the six-translate certificate. -/
def B6 : ℝ := 1094977 / 5000000000

/-- The ordered translate positions `0, g₀, g₀+g₁, …`. -/
def sextuplePosition (g : Fin 5 → ℝ) (i : Fin 6) : ℝ :=
  ((List.ofFn g).take i.val).sum

/-- The ideal normalized `6 × 6` Montgomery--Taylor Gram matrix. -/
def sextupleGram (g : Fin 5 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => mtKernel (sextuplePosition g i - sextuplePosition g j)

/-- Its off-diagonal Hilbert--Schmidt energy
`2 * ∑_{0 ≤ i < j ≤ 5} k(x_j-x_i)^2`. -/
def sextupleEnergy (g : Fin 5 → ℝ) : ℝ :=
  2 * ∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·),
    (sextupleGram g i j) ^ 2

/-- The five-gap span. -/
def sextupleSpan (g : Fin 5 → ℝ) : ℝ := ∑ i, g i

end Zeta23.ThmD.Sextuple
