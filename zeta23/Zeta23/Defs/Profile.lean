/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Profile.lean — a concrete taper profile.
The paper: "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)" [subsec:family]. Mathlib's Real.smoothTransition is such a function (even C^∞), so the
headline theorems need not quantify over ϱ.
-/
import Zeta23.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section

namespace Zeta23

/-- Real.smoothTransition is a taper profile in the paper's sense. -/
theorem taperProfile_smoothTransition : TaperProfile Real.smoothTransition where
  contDiff := Real.smoothTransition.contDiff
  monotone := Real.smoothTransition.monotone
  eq_zero := fun _ hx => Real.smoothTransition.zero_of_nonpos hx
  eq_one := fun _ hx => Real.smoothTransition.one_of_one_le hx

/-- The canonical profile used for the headline theorems. -/
def stdProfile : ℝ → ℝ := Real.smoothTransition

theorem taperProfile_stdProfile : TaperProfile stdProfile := taperProfile_smoothTransition

/-- "such a ϱ exists". -/
theorem exists_taperProfile : ∃ ϱ : ℝ → ℝ, TaperProfile ϱ := ⟨_, taperProfile_smoothTransition⟩

end Zeta23
