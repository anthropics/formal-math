/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Base

/-!
# Span and endpoint asymptotics for the sextuple ledger

This file records the asymptotic adapters used after finite six-point packing.
It does not import or assume a packing certificate.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple

open Assembly

/-- At `lambda = 1`, the positive surplus `2 log 2 - 1` in the
Riemann--von Mangoldt main term eventually absorbs its `O(log T)` error.  Thus
the normalized physical span has no asymptotic remainder at all. -/
theorem eventually_montgomeryTaylor_span_le :
    ∀ᶠ T in atTop,
      montgomeryTaylorParams.L T * T ≤
        2 * Real.pi * (Ncount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hmain⟩ := paperInputs_zeta.RvM.main
  have hc0 : 0 < Assembly.c₀ := Assembly.c₀_pos
  have heps : 0 < Assembly.c₀ / (2 * Real.pi) := by positivity
  have hsmall := (Real.isLittleO_log_id_atTop.const_mul_left C).def heps
  filter_upwards [eventually_ge_atTop T₀, hsmall,
    eventually_ge_atTop (0 : ℝ)] with T hT hsmallT hT0
  have hRvM := (abs_le.mp (hmain T hT)).1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hsmallT
  change |C * Real.log T| ≤
    (Assembly.c₀ / (2 * Real.pi)) * |T| at hsmallT
  rw [abs_of_nonneg hT0] at hsmallT
  have herr : C * Real.log T ≤ T * Assembly.c₀ / (2 * Real.pi) := by
    calc
      C * Real.log T ≤ |C * Real.log T| := le_abs_self _
      _ ≤ (Assembly.c₀ / (2 * Real.pi)) * T := hsmallT
      _ = T * Assembly.c₀ / (2 * Real.pi) := by ring
  have hdecomp : T / (2 * Real.pi) * (l T + Assembly.c₀) =
      T * l T / (2 * Real.pi) +
        T * Assembly.c₀ / (2 * Real.pi) := by ring
  rw [Assembly.ell1_eq, hdecomp] at hRvM
  have hN : T * l T / (2 * Real.pi) ≤
      (Ncount T (2 * T) : ℝ) := by
    simpa only [zetaZeroConfig_N] using (show
      T * l T / (2 * Real.pi) ≤
          (zetaZeroConfig.N T (2 * T) : ℝ) by
        linarith)
  have hmul := mul_le_mul_of_nonneg_left hN
    (show 0 ≤ 2 * Real.pi by positivity)
  calc
    montgomeryTaylorParams.L T * T = T * l T := by
      simp [montgomeryTaylorParams, paramsOf, Params.L]
      ring
    _ = (2 * Real.pi) * (T * l T / (2 * Real.pi)) := by field_simp
    _ ≤ 2 * Real.pi * (Ncount T (2 * T) : ℝ) := hmul

/-- Number of zeros, with multiplicity, in the lower unit boundary strip
`(T,T+1]`, viewed as a real-valued error function. -/
def lowerBoundaryStripCount (T : ℝ) : ℝ :=
  (Ncount T (T + 1) : ℝ)

/-- Number of zeros, with multiplicity, in the upper unit boundary strip
`(2T-1,2T]`, viewed as a real-valued error function. -/
def upperBoundaryStripCount (T : ℝ) : ℝ :=
  (Ncount (2 * T - 1) (2 * T) : ℝ)

/-- Total number of zeros in the two unit boundary strips. -/
def boundaryStripCount (T : ℝ) : ℝ :=
  lowerBoundaryStripCount T + upperBoundaryStripCount T

/-- Both unit boundary strips together contain `o(N(T,2T))` zeros. -/
theorem boundaryStripCount_isLittleO :
    boundaryStripCount =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := paperInputs_zeta.RvM.local_count
  have hO : boundaryStripCount =O[atTop] l := by
    refine IsBigO.of_bound (4 * A₀) ?_
    filter_upwards [eventually_ge_atTop Tail.T₀,
      eventually_ge_atTop (2 : ℝ), Assembly.eventually_l_pos]
      with T hT₀ hT2 hl
    have hT0 : 0 ≤ T := by linarith
    have habsT : |T| = T := abs_of_nonneg hT0
    have habs2T : |2 * T - 1| = 2 * T - 1 :=
      abs_of_nonneg (by linarith)
    have hlogLeft : Real.log (|T| + 3) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [habsT]
      linarith
    have hlogRight : Real.log (|2 * T - 1| + 3) ≤
        Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [habs2T]
      linarith
    have hlog4 := Tail.log_four_mul_le_two_mul_l hT₀
    have hleft : lowerBoundaryStripCount T ≤ 2 * A₀ * l T := by
      calc
        lowerBoundaryStripCount T ≤ A₀ * Real.log (|T| + 3) := by
          simpa [lowerBoundaryStripCount] using hloc T
        _ ≤ A₀ * Real.log (4 * T) :=
          mul_le_mul_of_nonneg_left hlogLeft (by linarith)
        _ ≤ A₀ * (2 * l T) :=
          mul_le_mul_of_nonneg_left hlog4 (by linarith)
        _ = 2 * A₀ * l T := by ring
    have hrightRaw := hloc (2 * T - 1)
    have hrightEndpoint : 2 * T - 1 + 1 = 2 * T := by ring
    have hrightLocal : upperBoundaryStripCount T ≤
        A₀ * Real.log (|2 * T - 1| + 3) := by
      simpa only [upperBoundaryStripCount, zetaZeroConfig_N,
        hrightEndpoint] using hrightRaw
    have hright : upperBoundaryStripCount T ≤ 2 * A₀ * l T := by
      calc
        upperBoundaryStripCount T ≤
            A₀ * Real.log (|2 * T - 1| + 3) := hrightLocal
        _ ≤ A₀ * Real.log (4 * T) :=
          mul_le_mul_of_nonneg_left hlogRight (by linarith)
        _ ≤ A₀ * (2 * l T) :=
          mul_le_mul_of_nonneg_left hlog4 (by linarith)
        _ = 2 * A₀ * l T := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      abs_of_pos hl]
    change boundaryStripCount T ≤ 4 * A₀ * l T
    calc
      boundaryStripCount T =
          lowerBoundaryStripCount T + upperBoundaryStripCount T := rfl
      _ ≤ 2 * A₀ * l T + 2 * A₀ * l T := add_le_add hleft hright
      _ = 4 * A₀ * l T := by ring
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl zetaZeroConfig
      paperInputs_zeta.RvM Assembly.isLittleO_l_Tl)

/-- The at-most ten ungrouped points left by six-point packing. -/
def tenPointLoss (_T : ℝ) : ℝ := 10

/-- A constant loss of ten points is `o(N(T,2T))`. -/
theorem tenPointLoss_isLittleO :
    tenPointLoss =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  have hO : tenPointLoss =O[atTop] l := by
    refine IsBigO.of_bound 10 ?_
    filter_upwards [Assembly.eventually_one_le_l] with T hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, tenPointLoss,
      abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith)]
    nlinarith
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl zetaZeroConfig
      paperInputs_zeta.RvM Assembly.isLittleO_l_Tl)

/-- Total endpoint loss: the two unit strips and the ten ungrouped points. -/
def endpointLoss (T : ℝ) : ℝ :=
  boundaryStripCount T + tenPointLoss T

/-- The complete endpoint loss is negligible relative to the dyadic count. -/
theorem endpointLoss_isLittleO :
    endpointLoss =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) :=
  boundaryStripCount_isLittleO.add tenPointLoss_isLittleO

end Sextuple
end ThmD
end Zeta23

end
