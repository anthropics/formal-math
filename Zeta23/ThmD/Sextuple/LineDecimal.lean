/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Unconditional

/-!
# Fixed decimal headline for the sextuple improvement

Public unconditional statements with the fixed rational constants
`6727556 / 10^7` and the tighter `672755620655 / 10^12`.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple

/-- Tighter rational lower enclosure obtained from `HD_one_decimal.1` and
Mathlib's certified 20-decimal upper bound for pi. -/
theorem sextupleLowerConstant_gt_672755620655 :
    (672755620655 / 10 ^ 12 : ℝ) < sextupleLowerConstant := by
  rw [sextupleLowerConstant, feedbackConstant]
  have hBMT := HD_one_decimal.1
  have hpi := Real.pi_lt_d20
  have hden : (0 : ℝ) < 6 - 1 / 80 := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num at hBMT hpi ⊢
  linarith

/-- Unconditional fixed `0.6727556` dyadic headline. -/
theorem thmD₀_sextuple_6727556 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727556 / 10 ^ 7 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  thmD₀_sextuple_6727556_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional fixed `0.6727556` cumulative headline. -/
theorem thmD₀_sextuple_cumulative_6727556 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727556 / 10 ^ 7 : ℝ) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T :=
  thmD₀_sextuple_cumulative_6727556_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Optional tighter fixed dyadic statement. -/
theorem thmD₀_sextuple_672755620655 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (672755620655 / 10 ^ 12 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  let q : ℝ := 672755620655 / 10 ^ 12
  obtain ⟨T₀, hT₀⟩ := thmD₀_sextuple
    (sextupleLowerConstant - q)
    (sub_pos.mpr sextupleLowerConstant_gt_672755620655)
  refine ⟨T₀, fun T hT => ?_⟩
  change q * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)
  convert hT₀ T hT using 1 <;> dsimp [q] <;> ring

/-- Optional tighter fixed cumulative statement. -/
theorem thmD₀_sextuple_cumulative_672755620655 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (672755620655 / 10 ^ 12 : ℝ) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T := by
  let q : ℝ := 672755620655 / 10 ^ 12
  obtain ⟨T₀, hT₀⟩ := thmD₀_sextuple_cumulative
    (sextupleLowerConstant - q)
    (sub_pos.mpr sextupleLowerConstant_gt_672755620655)
  refine ⟨T₀, fun T hT => ?_⟩
  change q * (Ncount 0 T : ℝ) ≤ N0simple 0 T
  convert hT₀ T hT using 1 <;> dsimp [q] <;> ring

end Sextuple
end ThmD
end Zeta23

end
