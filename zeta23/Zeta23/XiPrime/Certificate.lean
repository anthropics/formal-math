/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Certificate.lean — **the ξ′ window certificates**: discharges the interface Props  CertFlat
and  CertQuartic  of Zeta23/XiPrime/Statement.lean §4, and re-exports the sharp constants.

[XF′ Thm 8.2 "Certified constants"]:
  flat window      1/c = κ₉ + (tail ≤ ε₉) ≤ 1.1416163  ⟹  simple∧on-line ≥ 0.858383,  distinct ≥ 0.929191;
  quartic window   1/c = κ₉ + (tail ≤ ε₉) ≤ 1.1313598  ⟹  simple∧on-line ≥ 0.868640,  distinct ≥ 0.934320.
Route:
  Certificate/D1.lean    D1trunc 9 ≤ D₁ ≤ D1trunc 9 + ε₉ on [0,1], ε₉ = 1024/2990212875 (tail on the side that
                         makes 1/c LARGER, so the bound is honest);
  Certificate/Poly.lean  exact rational ∫v, ∫v², (v⋆v), 2∫₀¹ D1trunc 9·(v⋆v) for v = vFlat, vQuartic;
  Certificate/AtOne.lean κ₉ ≤ κ₁(1,v) ≤ κ₉ + ε₉ and the sharp decimals at λ = 1 (cert_*_one);
  Window.lean            λ ↦ κ₁(λ,v) continuous on (0,1]  ⟹  the strict inequalities persist at some λ < 1.
-/
import Zeta23.XiPrime.Certificate.AtOne
import Zeta23.XiPrime.Window

open Set

noncomputable section

namespace Zeta23
namespace XiPrime

/-- generic: two strict inequalities about κ₁(1,v) move to some λ ∈ [1/2,1) by continuity. -/
theorem cert_of_strict_at_one {v : ℝ → ℝ} {c cd : ℝ}
    (hcont : ContinuousOn (fun lam => kappaXi lam v) (Ioc 0 1))
    (h : c < 2 - kappaXi 1 v ∧ cd < 3 / 2 - kappaXi 1 v / 2) :
    ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧
      c < 2 - kappaXi lam v ∧ cd < 3 / 2 - kappaXi lam v / 2 := by
  have hsub : Icc (1/2 : ℝ) 1 ⊆ Ioc 0 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hk : ContinuousOn (fun lam => kappaXi lam v) (Icc (1/2) 1) := hcont.mono hsub
  have hf1 : ContinuousOn (fun lam => 2 - kappaXi lam v - c) (Icc (1/2) 1) :=
    (continuousOn_const.sub hk).sub continuousOn_const
  have hf2 : ContinuousOn (fun lam => 3 / 2 - kappaXi lam v / 2 - cd) (Icc (1/2) 1) :=
    (continuousOn_const.sub (hk.div_const 2)).sub continuousOn_const
  have hf : ContinuousOn (fun lam => min (2 - kappaXi lam v - c) (3 / 2 - kappaXi lam v / 2 - cd))
      (Icc (1/2) 1) := ContinuousOn.inf hf1 hf2
  obtain ⟨lam, h1, h2, h3⟩ := exists_lt_one_pos hf (lt_min (by linarith [h.1]) (by linarith [h.2]))
  refine ⟨lam, h1, h2, ?_, ?_⟩
  · linarith [min_le_left (2 - kappaXi lam v - c) (3 / 2 - kappaXi lam v / 2 - cd)]
  · linarith [min_le_right (2 - kappaXi lam v - c) (3 / 2 - kappaXi lam v / 2 - cd)]

/-- **CertFlat** (Statement.lean §4): ∃ λ ∈ [1/2,1), 0.85838 < 2 − κ₁(λ, flat) ∧ 0.92919 < 3/2 − κ₁(λ, flat)/2. -/
theorem certFlat : CertFlat :=
  cert_of_strict_at_one continuousOn_kappaXi_vFlat cert_flat_one_strict

/-- **CertQuartic** (Statement.lean §4): ∃ λ ∈ [1/2,1), 0.86864 < 2 − κ₁(λ, quartic) ∧ 0.93432 < 3/2 − κ₁/2. -/
theorem certQuartic : CertQuartic :=
  cert_of_strict_at_one continuousOn_kappaXi_vQuartic cert_quartic_one_strict

/-- the sharp seven-digit versions, also at some λ < 1. -/
theorem certFlat_sharp : ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧
    (0.858383 : ℝ) < 2 - kappaXi lam vFlat ∧ (0.929191 : ℝ) < 3 / 2 - kappaXi lam vFlat / 2 :=
  cert_of_strict_at_one continuousOn_kappaXi_vFlat
    ⟨by linarith [cert_flat_one], by linarith [cert_flat_dist_one]⟩

theorem certQuartic_sharp : ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧
    (0.868640 : ℝ) < 2 - kappaXi lam vQuartic ∧ (0.934320 : ℝ) < 3 / 2 - kappaXi lam vQuartic / 2 :=
  cert_of_strict_at_one continuousOn_kappaXi_vQuartic
    ⟨by linarith [cert_quartic_one], by linarith [cert_quartic_dist_one]⟩

end XiPrime
end Zeta23
