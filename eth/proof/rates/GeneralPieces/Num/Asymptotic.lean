/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Num.PartA

/-! # Two facts of Appendix A: the value of α' for ρ = 1/√2, and a remark at the close of the proof of Theorem A(c)

Pure arithmetic on the schedule K_ℓ, e_ℓ, for every x₀ ≥ 18; nothing here is about a machine.
`alpha_half`: for ρ = 1/√2 the number α' = log(1/ρ) is 1/2, as the paper says after Theorem A.
`between`: as remarked at the close of the proof of part (c), a number between 0.85·ρ^ℓ and ρ^ℓ lies
in [e_ℓ, 2e_ℓ]. -/

@[expose] public section

namespace GeneralPieces.Asymptotic

open Levels.Gen ClauseBound.Gen GeneralPieces.PartA

/-! ## The value of α' for ρ = 1/√2 -/

/-- «… with those of Appendix B, α' = 1/2»: for ρ = 1/√2. -/
theorem alpha_half : Real.logb 2 (1 / (1 / Real.sqrt 2)) = 1 / 2 := by
  rw [one_div_one_div, Real.sqrt_eq_rpow, Real.logb_rpow (by norm_num) (by norm_num)]

/-! ## A remark at the close of the proof of part (c) -/

/-- «… a number between 0.85·ρ^ℓ and ρ^ℓ lies in [e_ℓ, 2e_ℓ].» -/
theorem between (ρ : ℝ) (x₀ l : ℕ) (t : ℝ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (h1 : 0.85 * ρ ^ l ≤ t) (h2 : t ≤ ρ ^ l) :
    e ρ x₀ l ≤ t ∧ t ≤ 2 * e ρ x₀ l :=
  ⟨le_trans (e_le_of_y ρ x₀ l hρ hx) h1, by linarith [e_ge_half_pow ρ x₀ l hρ]⟩

end GeneralPieces.Asymptotic
