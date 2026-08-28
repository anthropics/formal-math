/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/ReexpansionW.lean — the δ-re-expansion of C(N; L + δ) about a GENERAL base L = Lb(T) with
Re Lb(T) = l(T)/2, and its instance at the REAL base ½l for the Z′ (Hardy W) coefficients  [XF′ §6 at §9.3(ii)]
(discharges ReexpansionW wCoeffFamily of Zeta23/XiPrime/Transfer/InputsW.lean).

This is Coeff/Reexpansion.lean (base L_T = l/2 + iπ/4) made base-generic: every step there uses only
Re L = l/2 (⇒ ‖L‖ ≥ l/2, L ≠ 0, L + δ ≠ 0), so the same e_r(N) := Σ_{j<Ω N}(−1)^r C(r+j,j) L^{-(j+1+r)}[(Λlog)∗Λ^{∗j}](N),
the same expansion C(N;L+δ) − C(N;L) = Σ_{r≥1} e_r δ^r (0 ≤ δ ≤ 1/2, l ≥ 2) and the same bounds (ρ₀ = 4, A = CF, T₀ = T0re)
hold verbatim.  The generic section lives in Coeff/ReexpansionGen.lean; this file is the Z′ instance.
-/
import Zeta23.XiPrime.Transfer.InputsW
import Zeta23.XiPrime.Coeff.ReexpansionGen

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### the Z′ instance: base ½l (real) -/

/-- the real base of the Z′ coefficients: ½ l(T). -/
def halfL (T : ℝ) : ℂ := ((l T / 2 : ℝ) : ℂ)

@[simp] lemma halfL_re (T : ℝ) : (halfL T).re = l T / 2 := by simp [halfL]

/-- e_r(N) for the Z′ family. -/
def eW : ℝ → ℕ → ℕ → ℂ := eGen halfL

/-- **ReexpansionW for the Z′ coefficient family** with e = eW, ρ₀ = 4, A = CF, T₀ = T0re. -/
theorem wReexpansion_eW : ∃ ρ₀ A T₀ : ℝ, 0 ≤ ρ₀ ∧ ReexpansionW wCoeffFamily eW ρ₀ A T₀ := by
  refine ⟨4, CF, T0re, by norm_num, ?_⟩
  exact
    { expand := fun T hT δ hδ N => by
        have hl := l_ge_of_T0re_le hT
        have hKe : 0 ≤ 128 * Real.exp 1 * KM := mul_nonneg (by positivity) KM_nonneg
        have h := eGen_expand halfL halfL_re (T := T) (by linarith) hδ N
        simpa [eW, halfL, wCoeffFamily] using h
      e_one := fun T r => eGen_one halfL T r
      H1 := fun T hT r _ x hx2 hxl => eGen_H1 halfL halfL_re hT r hx2 hxl
      H2 := fun T hT r _ x hx2 hxl => eGen_H2 halfL halfL_re hT r hx2 hxl
      H3 := fun T hT r _ x hx2 hxl => eGen_H3 halfL halfL_re hT r hx2 hxl }

/-- **ReexpansionW for the Z′ coefficient family**, ∃-e form (the sentence InputsW.lean asks for). -/
theorem wReexpansion :
    ∃ (e : ℝ → ℕ → ℕ → ℂ) (ρ₀ A T₀ : ℝ), 0 ≤ ρ₀ ∧ ReexpansionW wCoeffFamily e ρ₀ A T₀ :=
  ⟨eW, wReexpansion_eW⟩

end XiPrime
end Zeta23
