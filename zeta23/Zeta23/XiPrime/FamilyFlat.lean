/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/FamilyFlat.lean — the window-regularity class FamilyHyps (Zeta23/XiPrime/ExplicitFormula.lean §7)
holds for the FLAT taper family T ↦ paramsOf ϱ λ at a Gevrey profile ϱ.

FamilyHyps asks, from some T₀ on: φ_T := (Pf T).phi T is C³, tsupport φ_T ⊆ [−L/2, L/2], even, |φ_T| ≤ 1, and
‖φ_T^{(j)}‖_{L¹} ≤ C for j = 1,2,3 with C INDEPENDENT of T.  For the ramp taper φ(u) = ϱ((L/2−|u|)/w) the
derivatives live on the two ramps of width w and scale like w^{−j}, so the L¹ norms are O_w(1) uniformly in L:
Zeta23/Taper/GevreyRamps.lean proves exactly  ∫|φ^{(k)}| ≤ 2B·w·(A/w)^k·k^{sk}  for a GevreyProfile
(s, A, B) ϱ, and Zeta23/Taper/Gevrey.lean supplies the instance rhoTwo (gevreyProfile_rhoTwo).  That is all the
unconditional headline needs (Final.lean instantiates at ϱ := rhoTwo).  The generic C³-TaperProfile version
is not treated here. -/
import Zeta23.XiPrime.ExplicitFormula
import Zeta23.XiPrime.Assembly
import Zeta23.Taper.GevreyRamps
import Zeta23.Taper.Gevrey
import Zeta23.Taper.Params

noncomputable section

open Filter Set MeasureTheory

namespace Zeta23
namespace XiPrime

/-- derivatives of every order of a compactly supported function are compactly supported. -/
lemma hasCompactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => simpa [iteratedDeriv_succ] using ih.deriv

/-- **FamilyHyps for the flat family at a Gevrey taper profile** (λ ∈ (0,1), w = 1). -/
theorem familyHyps_flat_gevrey {s A B : ℝ} {ϱ : ℝ → ℝ} (hϱ : Taper.GevreyProfile s A B ϱ) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1) : FamilyHyps (fun _ => paramsOf ϱ lam) := by
  have hP : (paramsOf ϱ lam).Valid := paramsOf_valid hϱ.taper h0 h1.le
  have hA := hϱ.A_pos
  have hB := hϱ.B_pos
  refine ⟨⟨lam, h0, h1, fun _ => rfl⟩, ?_⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    ((Assembly.tendsto_L_atTop (paramsOf ϱ lam) hP.lam_pos).eventually_ge_atTop 8)
  refine ⟨∑ k ∈ Finset.Icc (1:ℕ) 3, 2 * B * (1:ℝ) * (A / 1) ^ k * ((k : ℕ) : ℝ) ^ (s * (k : ℕ)), T₀,
    fun T hT => ?_⟩
  have hL8 : 8 ≤ (paramsOf ϱ lam).L T := hT₀ T hT
  have h8 : 8 * (paramsOf ϱ lam).w ≤ (paramsOf ϱ lam).L T := by
    show 8 * (1:ℝ) ≤ (paramsOf ϱ lam).L T; linarith
  have hwL : 2 * (1:ℝ) ≤ (paramsOf ϱ lam).L T := by linarith
  have hcd : ContDiff ℝ 3 ((paramsOf ϱ lam).phi T) := Params.phi_contDiff hP h8
  refine ⟨hcd, closure_minimal (Params.phi_support_subset hP) isClosed_Icc,
    fun u => Params.phi_even' u,
    fun u => abs_le.mpr ⟨by linarith [Params.phi_nonneg hP (T := T) u], Params.phi_le_one hP u⟩,
    fun j hj1 hj3 => ⟨?_, ?_⟩⟩
  · exact ((hcd.continuous_iteratedDeriv j (by exact_mod_cast hj3)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv (Params.phi_hasCompactSupport hP) j))
  · have hb := Taper.integral_abs_iteratedDeriv_phi_le (L := (paramsOf ϱ lam).L T) hϱ one_pos hwL hj1
    refine hb.trans ?_
    refine Finset.single_le_sum (f := fun k : ℕ => 2 * B * (1:ℝ) * (A / 1) ^ k * ((k : ℕ) : ℝ) ^ (s * (k : ℕ)))
      (fun k _ => by positivity) (Finset.mem_Icc.mpr ⟨hj1, hj3⟩)

end XiPrime
end Zeta23

end
