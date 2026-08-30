/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/RvMChi.lean — H-RvM(χ) for Mathlib's Dirichlet L-functions.
Main statement:
  theorem rvmChi (hq : 1 < q) (hprim : χ.IsPrimitive) : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim))
i.e. main: |N_χ(T,2T) − (T/2π)·ell1q q T| ≤ C log T (T ≥ T₀) and the two-sided local count
N_χ(t,t+1] ≤ A₀ log(|t|+3) — constants depending on q (fixed).
Decomposition (mirrors the Riemann–von Mangoldt argument for ζ; each piece in its own file):
 • Zeta23/ThmE/LGrowth.lean : ‖L(s,χ)‖ ≤ q‖s‖/Re s on Re s > 0; σ ≥ 2 two-sided bounds.
 • Zeta23/ThmE/LocalCountChi.lean: localCountChi — Jensen/ZerosBound disc at 2+(t+½)i after halving by
   ρ ↦ 1−ρ̄ (Zeta23.ZeroConfig.N_le_two_mul_half applies verbatim to LZeros), both signs of t directly.
 • Zeta23/ThmE/MainTermChi.lean: mainChi — argument principle for Λ(s,χ) = completedLFunction on
   [−1,2]×[T₁,T₂] (Zeta23.Analytic.rectangleIntegral'_mul_logDeriv; Λ(·,χ) entire for primitive χ, q>1),
   fold by Λ(1−s̄,χ) = ε(χ)·conj Λ(s,χ) (ε drops out of Λ'/Λ), Γ-side = ∫μ_χ (GammaFactsChi),
   Backlund for L via g(z) = (L(z+iT,χ)+L(z−iT,χ̄))/2, non-ordinate perturbation.
-/
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.MainTermChi

open Complex Set DirichletCharacter

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **H-RvM(χ)** for a primitive character χ mod q > 1. -/
theorem rvmChi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)) := by
  refine ⟨?_, ?_⟩
  · simpa using mainChi hq hprim
  · simpa using localCountChi hq hprim

end ThmE
end Zeta23
