/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/Main.lean — umbrella + final (EF4) theorem of the ξ′ explicit-formula
development.  Consumers should import this module.
Components: §2 (F2) ZeroFree.lean; §4 (EF1) FullLine.lean;
§5 Archimedean + Expansion; §6 DirichletLine; §7 (EF4) = XiEFAssembly.xiEF_of,
instantiated here with GramBridge, Coeff/LSeries, and the test-weight bounds
(from TestWeight.lean, reshaped into TestWeightFacts by the adapter below).
-/
import Zeta23.XiPrime.ExplicitFormula.XiEFAssembly
import Zeta23.XiPrime.ExplicitFormula.GramBridge
import Zeta23.XiPrime.ExplicitFormula.TestWeight
import Zeta23.XiPrime.Coeff.LSeries

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn Hfn_mirror)

/-! ### adapter: TestWeight.lean → TestWeightFacts (pure reshaping) -/


theorem five_four_cast : (((5/4:ℝ):ℂ)) = (5/4 : ℂ) := by push_cast; ring

theorem cauchyK_mul_eq (a b t : ℝ) :
    cauchyK a t * cauchyK b t = 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) := by
  unfold cauchyK; rw [one_div, mul_inv]

theorem cauchyK_neg_mul_eq (a b t : ℝ) :
    cauchyK (-a) t * cauchyK (-b) t = 1 / ((1 + (t + a) ^ 2) * (1 + (t + b) ^ 2)) := by
  unfold cauchyK; rw [one_div, mul_inv, sub_neg_eq_add, sub_neg_eq_add]

/-- TestWeight.lean provides TestWeightFacts. -/
theorem testWeightFacts_hosted {Pf : ℝ → Params} (hPf : FamilyHyps Pf) : TestWeightFacts Pf := by
  obtain ⟨T₀, hreg⟩ := testWeight_regular hPf
  obtain ⟨C₁, T₁, hC₁, h₁⟩ := testWeight_norm_le hPf
  obtain ⟨C₂, T₂, hC₂, h₂⟩ := testWeight_moment_norm_le hPf
  obtain ⟨C₃, T₃, hC₃, h₃⟩ := testWeight_neg_norm_le hPf
  refine ⟨max (max C₁ C₂) C₃, max (max T₀ T₁) (max T₂ T₃), by positivity, fun T hT k l => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT₂ : T₂ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT₃ : T₃ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  obtain ⟨⟨hLpos, -⟩, hkl⟩ := hreg T hT₀
  obtain ⟨⟨hcd, hcs, hsupp⟩, -⟩ := hkl k l
  have hXr : 0 ≤ (Pf T).X T ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Real.exp_pos _).le _
  have hC₁' : C₁ ≤ max (max C₁ C₂) C₃ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₂' : C₂ ≤ max (max C₁ C₂) C₃ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC₃' : C₃ ≤ max (max C₁ C₂) C₃ := le_max_right _ _
  have hmir : ∀ t : ℝ, Hfn (kfun (Pf T) T k l) (1 - (5/4:ℝ) - t * I)
      = Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I) := by
    intro t; rw [Hfn_mirror, five_four_cast]
  refine ⟨hcd, hcs, hsupp, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [five_four_cast, cauchyK_mul_eq, mul_one_div]
    refine (h₁ T hT₁ k l t).trans (div_le_div_of_nonneg_right ?_ (by positivity))
    gcongr
  · rw [five_four_cast, cauchyK_mul_eq, mul_one_div]
    refine (h₂ T hT₂ k l t).trans (div_le_div_of_nonneg_right ?_ (by positivity))
    gcongr
  · rw [hmir, cauchyK_neg_mul_eq, mul_one_div]
    refine (h₃ T hT₃ k l t).1.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    gcongr
  · rw [hmir, cauchyK_neg_mul_eq, mul_one_div]
    refine (h₃ T hT₃ k l t).2.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    gcongr


/-! ### the three input Props of XiEFAssembly, discharged -/

theorem gramBridgeFacts : GramBridgeFacts :=
  ⟨fun Z hZ hm P T h1 h2 k l => Gz_eq_tsum_xi P T Z hZ hm h1 h2 k l,
   fun Z hZ hm P T h1 h2 k l h => summable_Gsummand_of P T Z hZ hm h1 h2 k l h,
   fun P T h1 h2 hL k l => literatureRHS_pairTest_eq_Gentry P T h1 h2 hL k l,
   fun P T h1 h2 hL k l cJ hn hi => Gentry1_eq P T h1 h2 hL k l cJ hn hi,
   fun P T hL hT k => tau_mem P T hL hT k⟩

theorem xiCoeffJ'_eq (Λs : ℂ) : xiCoeffJ' Λs = xiCoeffJ Λs := by
  funext N
  rw [xiCoeffJ', xiCoeff_eq_neg_add_xiCoeffJ]
  ring

theorem coeffFacts : CoeffFacts := by
  obtain ⟨R₀, hR₀, h⟩ := LSeries_xiCoeffJ
  refine ⟨⟨R₀, hR₀, fun Λs hΛ => ?_⟩, fun Λs N => ?_⟩
  · have h0 := h Λs hΛ (((5/4:ℝ):ℂ)) (by simp)
    refine ⟨?_, fun t => ?_⟩
    · have := h0.1
      rw [xiCoeffJ'_eq]
      simpa using this
    · obtain ⟨-, -, h3⟩ := h Λs hΛ (((5/4:ℝ):ℂ) + t * I) (by simp)
      rw [xiCoeffJ'_eq]
      rw [Dfro, Afn, Bfn]
      exact h3
  · rw [xiCoeffJ'_eq, xiCoeffJ'_eq, xiCoeffJ_conj]

theorem testWeightFacts {Pf : ℝ → Params} (hPf : FamilyHyps Pf) : TestWeightFacts Pf :=
  testWeightFacts_hosted hPf

/-! ### §7 (EF4) -/

/-- **(EF4)** [XF′ Thm 4.2]: Statement.XiEF — the explicit formula for ξ′ with frozen
coefficients, entrywise, with the T-uniform entry error C·T^{−δ}·(1/max(1,(τ_k−τ_l)²) + 1/T).
(hF2 is the theorem
xiDerivZerosInStrip_holds and is not used.) -/
theorem xiEF (_hF2 : XiDerivZerosInStrip) (Z : ZeroConfig) (hZ : Z.carrier = {ρ : ℂ | IsXiDerivZero ρ})
    (hm : ∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ)
    (Pf : ℝ → Params) (hPf : FamilyHyps Pf) : XiEF Z Pf :=
  xiEF_of gramBridgeFacts coeffFacts Z hZ hm Pf hPf (testWeightFacts hPf)

/-- the same for Statement's own instance. -/
theorem xiEF_xiDerivZeros (hs : XiDerivSeam) (Pf : ℝ → Params) (hPf : FamilyHyps Pf) :
    XiEF (xiDerivZeros xiDerivZerosInStrip_holds hs) Pf :=
  xiEF xiDerivZerosInStrip_holds _ rfl (fun _ _ => rfl) Pf hPf

end XiPrime
end Zeta23
