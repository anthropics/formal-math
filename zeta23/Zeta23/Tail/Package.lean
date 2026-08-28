/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Package.lean — [prop:tail] with all its analytic inputs discharged from the
repository's other files, in the exact shape Zeta23/Main.lean consumes ("hTailPkg").

Inputs discharged here: A₀ and the local count from PaperInputs.RvM.local_count
(Hypotheses.lean); [eq:hfbound] for φ = Zeta23.Params.norm_phiHat_sub_I_mul_le, a ≥ 1/2 =
Zeta23.Params.half_le_a, C₁ ≤ 2‖ϱ″‖₁ = Zeta23.Params.C1_le (Taper.lean);
conj φ̂(z̄) = φ̂(z) = Zeta23.GzGp.phiHat_conj (hypothesis-free). The side condition 8w ≤ L
[eq:wrange] holds eventually since L = λ log(T/2π) → ∞ (Zeta23.Tail.tendsto_L_atTop).
-/
import Zeta23.Tail
import Zeta23.Taper
import Zeta23.Hypotheses.GzGp

noncomputable section

open Filter Complex

namespace Zeta23
namespace Tail

/-- C₁ = ‖φ″‖₁ ≥ 0. -/
lemma C1_nonneg (P : Params) (T : ℝ) : 0 ≤ P.C1 T :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _

/-- **[prop:tail] package for Main.lean**: for an abstract zero configuration Z satisfying the
paper's inputs and valid parameters P, there is θ₀ : ℝ → ℝ (namely
θ₀(T) = 4A₀C₁²X^{1/2}log(4T)/D₀² = theta0 A₀ (e^{L/4}·C₁) T) such that eventually in T
Assembly.TailInputs Z P T (θ₀ T) holds ("‖Ẽ‖ ≤ θ₀", "‖Ê‖₁ ≤ θ₀/(aL)"), and
θ₀(T) ≤ C · l(T) · T^{λ/2−1} eventually ("θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1}"). -/
theorem eventually_tailPackage (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z P T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := (tendsto_L_atTop P hP).eventually_ge_atTop _
  refine ⟨fun T => theta0 A₀ (Real.exp (P.L T / 4) * P.C1 T) T, ?_, ?_⟩
  · refine eventually_tailInputs Z P hP hA₀ hloc (fun T => P.C1 T) (fun T => C1_nonneg P T)
      ?_ ?_ ?_
    · filter_upwards [hwL] with T hwL
      exact fun r y hy hz => Params.norm_phiHat_sub_I_mul_le hP hwL r y hy hz
    · filter_upwards [hwL] with T hwL
      linarith [Params.half_le_a hP hwL]
    · exact Eventually.of_forall fun T z => GzGp.phiHat_conj P T z
  · exact eventually_theta0_le P hP hA₀ (fun T => P.C1 T) (fun T => C1_nonneg P T)
      (hwL.mono fun T hwL => Params.C1_le hP hwL)

end Tail
end Zeta23
