/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/Reexpansion.lean — the ξ′ instance (base L_T = l/2 + iπ/4) of the generic δ-re-expansion
Coeff/ReexpansionGen.lean; discharges `Reexpansion xiCoeffFamily` of Zeta23/XiPrime/Transfer/Inputs.lean
(consumed by Final.lean via xiReexpansion).  [XF′ §6, Lemma 6.1 input]

  eXi := eGen LT;   C(N; L_T+δ) − C(N; L_T) = Σ_{r≥1} eXi T r N · δ^r;   (H1)–(H3)_r with ρ₀ = 4, A = CF, T₀ = T0re.
-/
import Zeta23.XiPrime.Transfer.Inputs
import Zeta23.XiPrime.Coeff.ReexpansionGen
import Zeta23.XiPrime.Coeff.LT

open scoped BigOperators ArithmeticFunction
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-- e_r(N) for the ξ′ family: the generic coefficients about the base L_T. -/
def eXi : ℝ → ℕ → ℕ → ℂ := eGen LT

/-- **Reexpansion for the ξ′ coefficient family** with the explicit e = eXi, ρ₀ = 4, A = CF, T₀ = T0re. -/
theorem xiReexpansion_eXi : ∃ ρ₀ A T₀ : ℝ, 0 ≤ ρ₀ ∧ Reexpansion xiCoeffFamily eXi ρ₀ A T₀ := by
  refine ⟨4, CF, T0re, by norm_num, ?_⟩
  exact
    { expand := fun T hT δ hδ N => by
        have hl := l_ge_of_T0re_le hT
        have hKe : 0 ≤ 128 * Real.exp 1 * KM := mul_nonneg (by positivity) KM_nonneg
        exact eGen_expand LT re_LT (T := T) (by linarith) hδ N
      e_one := fun T r => eGen_one LT T r
      H1 := fun T hT r _ x hx2 hxl => eGen_H1 LT re_LT hT r hx2 hxl
      H2 := fun T hT r _ x hx2 hxl => eGen_H2 LT re_LT hT r hx2 hxl
      H3 := fun T hT r _ x hx2 hxl => eGen_H3 LT re_LT hT r hx2 hxl }

/-- **Reexpansion for the ξ′ coefficient family**, in the ∃-e form. -/
theorem xiReexpansion :
    ∃ (e : ℝ → ℕ → ℕ → ℂ) (ρ₀ A T₀ : ℝ), 0 ≤ ρ₀ ∧ Reexpansion xiCoeffFamily e ρ₀ A T₀ :=
  ⟨eXi, xiReexpansion_eXi⟩

end XiPrime
end Zeta23
