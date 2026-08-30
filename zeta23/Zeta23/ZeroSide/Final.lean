/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide/Final.lean — prop:block with the analytic inputs discharged.

Zeta23/ZeroSide.lean proves §4's block structure / prop:block with three analytic facts as explicit
hypotheses (PhiHatConj, PhiHatReal, PoissonSq) and positivity of L and aL². Here they are supplied
from Zeta23.Hypotheses.GzGp (phiHat_conj, phiHat_ofReal), Zeta23.Taper (Params.half_le_a) and
Zeta23.Poisson (Params.hasSum_phiHatR_sq = lem:poisson), leaving only the standing assumptions
(hP : P.Valid) and (hwL : 8 * P.w ≤ P.L T) [eq:wrange]; and the `∀ᶠ T` form that
thmA_abstract consumes (hwL holds eventually since L = λ log(T/2π) → ∞).
-/
import Zeta23.ZeroSide
import Zeta23.Hypotheses.GzGp
import Zeta23.Taper
import Zeta23.Poisson
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Matrix RHLinalg Filter
open scoped ComplexOrder

namespace Zeta23.ZeroSide

variable {P : Params} {T : ℝ}

lemma L_pos (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T) : 0 < P.L T := by linarith [hP.one_le_w]

lemma aLsq_pos (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T) : 0 < P.a T * P.L T ^ 2 :=
  mul_pos (by linarith [Params.half_le_a hP hwL]) (pow_pos (L_pos hP hwL) 2)

/-- From Zeta23.GzGp.phiHat_conj (uses only that φ is real and even). -/
lemma phiHatConj : PhiHatConj T P := fun z => GzGp.phiHat_conj P T z

/-- From Zeta23.GzGp.phiHat_ofReal. -/
lemma phiHatReal : PhiHatReal T P := fun r => GzGp.phiHat_ofReal P T r

lemma poissonSq (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T) : PoissonSq T P :=
  fun γ => Params.hasSum_phiHatR_sq hP hwL γ

/-- prop:block + [eq:Ncount] packaged for Assembly at height T, under the standing assumptions only. -/
theorem blockInputs_of_hwL (Z : ZeroConfig) (P : Params) (T : ℝ) (hP : P.Valid)
    (hwL : 8 * P.w ≤ P.L T) : Assembly.BlockInputs Z P T :=
  blockInputsAt Z P T phiHatConj phiHatReal (poissonSq hP hwL) (L_pos hP hwL) (aLsq_pos hP hwL)

/-- L = λ·log(T/2π) → ∞. -/
lemma tendsto_L_atTop (P : Params) (hlam : 0 < P.lam) : Tendsto P.L atTop atTop := by
  have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  exact (h.const_mul_atTop hlam).congr fun T => by simp [Params.L, l]

/-- **The input `thmA_abstract` consumes**: eventually in T, prop:block holds. -/
theorem blockInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z P T := by
  filter_upwards [(tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
  exact blockInputs_of_hwL Z P T hP hT

/-- Alias of `blockInputs` in the shape used by Main.lean. -/
theorem eventually_blockInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z P T :=
  blockInputs Z P hP

/-! ### The individual statements with hypotheses discharged (convenience re-exports) -/

variable (Z : ZeroConfig) (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-- **[prop:block] (i)** "n₊(Ã) ≤ s₁ + s₂ + p". -/
theorem prop_block_i_posIndex (h : (P.tilde T (Z.Az P T)).IsHermitian) :
    posIndex h ≤ Z.s1 T + Z.s2 T + Z.p T :=
  posIndex_tilde_Az_le Z T P phiHatConj (L_pos hP hwL) h

/-- **[prop:block] (i)** "rank(Ã) ≤ s₁ + s₂ + 2p = #𝒵(I')". -/
theorem prop_block_i_rank : (P.tilde T (Z.Az P T)).rank ≤ Z.s1 T + Z.s2 T + 2 * Z.p T :=
  rank_tilde_Az_le Z T P phiHatConj (L_pos hP hwL)

omit hP hwL in
/-- **[prop:block] (ii)** "Â = P + Q" (Â := A/(aL²) [eq:hatunits] = P.hat T (Z.Az P T)). -/
theorem prop_block_ii_decomp :
    P.hat T (Z.Az P T) = hatP Z T P phiHatConj + hatQ Z T P phiHatConj :=
  hat_Az_eq_hatP_add_hatQ Z T P phiHatConj

/-- **[prop:block] (ii)** "P ⪰ 0". -/
theorem prop_block_ii_P_posSemidef : (hatP Z T P phiHatConj).PosSemidef :=
  hatP_posSemidef Z T P phiHatConj (aLsq_pos hP hwL)

/-- **[prop:block] (ii)** "rank P ≤ s₁ + s₂". -/
theorem prop_block_ii_rank_P : (hatP Z T P phiHatConj).rank ≤ Z.s1 T + Z.s2 T :=
  rank_hatP_le Z T P phiHatConj (aLsq_pos hP hwL)

/-- **[prop:block] (ii)** "tr P ≤ N_on(I')" (by lem:poisson). -/
theorem prop_block_ii_trace_P : rtrace (hatP Z T P phiHatConj) ≤ (Z.NonIprime T : ℝ) :=
  rtrace_hatP_le Z T P phiHatConj phiHatReal (poissonSq hP hwL) (aLsq_pos hP hwL)

/-- **[prop:block] (ii)** "n₊(Q) ≤ p" (by lem:inertia). -/
theorem prop_block_ii_posIndex_Q (h : (hatQ Z T P phiHatConj).IsHermitian) : posIndex h ≤ Z.p T :=
  posIndex_hatQ_le Z T P phiHatConj (aLsq_pos hP hwL) h

end Zeta23.ZeroSide
