/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Kernel
import Zeta23.ThmD.Sextuple.TrigInterval

noncomputable section

namespace Zeta23.ThmD.Sextuple

open RatInterval

/-- Tight rational enclosure of `√2`. -/
def rootTwoInterval : RatInterval :=
  ⟨1414213562373095 / 10^15, 1414213562373096 / 10^15⟩

theorem rootTwo_mem : Holds rootTwoInterval (Real.sqrt 2) := by
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · apply (sq_le_sq₀ (by norm_num [rootTwoInterval]) hr0).mp
    rw [hr2]
    norm_num [rootTwoInterval]
  · apply (sq_le_sq₀ hr0 (by norm_num [rootTwoInterval])).mp
    rw [hr2]
    norm_num [rootTwoInterval]

/-- Enclosure of `1/√2 = √2/2`. -/
def thetaInterval : RatInterval := scale (1/2) rootTwoInterval

def thetaTrig : RatInterval × RatInterval := trigRange thetaInterval 0

lemma theta_mem : Holds thetaInterval (Real.sqrt 2 / 2) := by
  simpa [thetaInterval, div_eq_mul_inv, mul_comm] using holds_scale (q := (1/2 : ℚ)) rootTwo_mem

lemma thetaTrig_sound :
    Holds thetaTrig.1 (Real.sin (Real.sqrt 2 / 2)) ∧
      Holds thetaTrig.2 (Real.cos (Real.sqrt 2 / 2)) := by
  apply trigRange_sound (i := thetaInterval) (x := Real.sqrt 2 / 2) 0
  · norm_num [thetaInterval, rootTwoInterval, scale]
  · norm_num [thetaInterval, rootTwoInterval, scale, reducedMid]
  · exact theta_mem

/-- Closed-form interval evaluation of the MT kernel on one rational cell.
The natural number is the range-reduction quarter-turn index for `x/2`. -/
def kernelRange (i : RatInterval) (turn : ℕ) : RatInterval :=
  let xt := trigRange (scale (1/2) i) turn
  let st := thetaTrig.1
  let ct := thetaTrig.2
  let num := sub (mul (mul (mul rootTwoInterval i) ct) xt.1)
    (mul (scale 2 st) xt.2)
  let den := mul (sub (sq i) ⟨2,2⟩) st
  divPos num den

/-- The denominator interval used by `kernelRange`. -/
def kernelDenRange (i : RatInterval) : RatInterval :=
  mul (sub (sq i) ⟨2,2⟩) thetaTrig.1

lemma kernelRange_sound {i : RatInterval} {x : ℝ} (turn : ℕ)
    (hlo : 2 ≤ i.lo) (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hden : (0 : ℚ) < (kernelDenRange i).lo) (hx : Holds i x) :
    Holds (kernelRange i turn) (mtKernel x) := by
  have hhalf : Holds (scale (1/2) i) (x/2) := by
    simpa [div_eq_mul_inv, mul_comm] using holds_scale (q := (1/2 : ℚ)) hx
  have hhalfOrd : (scale (1/2) i).lo ≤ (scale (1/2) i).hi := by
    simp only [scale]
    norm_num
    linarith
  obtain ⟨hsx,hcx⟩ := trigRange_sound turn hhalfOrd hred hhalf
  obtain ⟨hst,hct⟩ := thetaTrig_sound
  have ha := rootTwo_mem
  have hnum : Holds
      (sub (mul (mul (mul rootTwoInterval i) thetaTrig.2) (trigRange (scale (1/2) i) turn).1)
        (mul (scale 2 thetaTrig.1) (trigRange (scale (1/2) i) turn).2))
      (Real.sqrt 2 * x * Real.cos (Real.sqrt 2 / 2) * Real.sin (x/2) -
        2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (x/2)) := by
    exact holds_sub (holds_mul (holds_mul (holds_mul ha hx) hct) hsx)
      (holds_mul (holds_scale (q := (2:ℚ)) hst) hcx)
  have hx2 := holds_sq hx
  have htwo : Holds (⟨2,2⟩ : RatInterval) (2:ℝ) := holds_point 2
  have hdenReal : Holds (kernelDenRange i)
      ((x^2-2) * Real.sin (Real.sqrt 2/2)) := by
    exact holds_mul (holds_sub hx2 htwo) hst
  have hclosed : Holds (kernelRange i turn) (mtKernelClosed x) := by
    exact holds_divPos hden hnum hdenReal
  have hloR : (2:ℝ) ≤ (i.lo : ℝ) := by exact_mod_cast hlo
  have hxge : (2:ℝ) ≤ x := hloR.trans hx.1
  have hne : x^2 ≠ 2 := by nlinarith [sq_nonneg (x-2)]
  rw [mtKernel_eq_closed hne]
  simpa [kernelRange, kernelDenRange] using hclosed

end Zeta23.ThmD.Sextuple
