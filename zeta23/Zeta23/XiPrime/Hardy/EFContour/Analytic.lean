/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFContour/Analytic.lean — analytic data for the W explicit-formula contour INCLUDING THE REAL AXIS.

Hardy/Basic.lean proves everything about χ, L₂, W at points with Im s ≠ 0.  The contour
[1−c, c] × [−R, R] (1 < c ≤ 5/4) crosses the real axis, so here we redo the analytic facts on the vertical strip
−2 < Re s < 3 minus the two genuine singular points 0 and 1, using ONE device: G := (Γℝ)⁻¹ = π^{s/2}/Γ(s/2) is
ENTIRE (Mathlib's differentiable_one_div_Gamma), Γℝ = G⁻¹ literally, and Γℝ s ≠ 0 ↔ s is not a pole of Γℝ
(Mathlib's junk value at the poles is 0 and Γℝ has no genuine zeros).  Hence
  * Γℝ analytic at s ⇔ Γℝ s ≠ 0;  χ = Γℝ(1−·)·G analytic where Γℝ(1−s) ≠ 0, nonzero where moreover Γℝ s ≠ 0;
    L₂ = −½χ′/χ and W = ζ′ + L₂ζ analytic on {−2 < Re < 3} \ {0, 1};
  * G has a SIMPLE zero at 0 (G(s) = s·G(s+2)/(2π), from Gammaℝ_add_two), so G∘(1−·) has a simple zero at 1,
    s·(G′/G)(s) → 1 at 0, and therefore  s·L₂(s) → −½ (s → 0),  (s−1)·L₂(s) → ½ (s → 1);
  * with Mathlib's tendsto_riemannZeta_sub_one_div (ζ(s) − 1/(s−1) → γ) and a removable singularity:
    (s−1)²ζ′(s) → −1, whence the POLE DATA of W:  s·W(s) → ¼ (s → 0),  (s−1)²·W(s) → −½ (s → 1);
  * Wreg := s(s−1)²·W(s), filled in with ¼ at 0 and −½ at 1, is analytic on {−2 < Re < 3}, nonzero at 0, 1,
    and has the zeros and orders of W elsewhere.
-/
import Zeta23.XiPrime.Hardy.TwoLine
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy
namespace EFContour

/-! ### §1. G := (Γℝ)⁻¹ is entire; Γℝ is analytic exactly where it is nonzero -/

/-- G(s) := (Γℝ s)⁻¹. -/
def invGammaℝ (s : ℂ) : ℂ := (Gammaℝ s)⁻¹

lemma invGammaℝ_eq (s : ℂ) : invGammaℝ s = (Real.pi : ℂ) ^ (s / 2) * (1 / Complex.Gamma (s / 2)) := by
  rw [invGammaℝ, Gammaℝ_def, mul_inv, ← cpow_neg, one_div]
  congr 2; ring

/-- G is entire. -/
theorem differentiable_invGammaℝ : Differentiable ℂ invGammaℝ := by
  have e : invGammaℝ = fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / Complex.Gamma (s / 2)) := funext invGammaℝ_eq
  rw [e]
  refine Differentiable.mul ?_ ?_
  · intro s
    exact DifferentiableAt.const_cpow (differentiableAt_id.div_const 2)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · have h := Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const (2:ℂ))
    intro s
    have := h s
    simpa [Function.comp_def, one_div] using this

theorem analyticAt_invGammaℝ (s : ℂ) : AnalyticAt ℂ invGammaℝ s := differentiable_invGammaℝ.analyticAt s

lemma Gammaℝ_eq_inv_invGammaℝ : Gammaℝ = invGammaℝ⁻¹ := by
  funext s; rw [Pi.inv_apply, invGammaℝ, inv_inv]

lemma invGammaℝ_ne_zero_iff {s : ℂ} : invGammaℝ s ≠ 0 ↔ Gammaℝ s ≠ 0 := by
  rw [invGammaℝ, ne_eq, inv_eq_zero]

lemma invGammaℝ_eq_zero_iff {s : ℂ} : invGammaℝ s = 0 ↔ Gammaℝ s = 0 := by
  rw [invGammaℝ, inv_eq_zero]

/-- Γℝ is analytic at every point where it is nonzero (= every non-pole). -/
theorem analyticAt_Gammaℝ {s : ℂ} (hs : Gammaℝ s ≠ 0) : AnalyticAt ℂ Gammaℝ s := by
  rw [Gammaℝ_eq_inv_invGammaℝ]
  exact (analyticAt_invGammaℝ s).fun_inv (invGammaℝ_ne_zero_iff.mpr hs)

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : Gammaℝ s ≠ 0) : DifferentiableAt ℂ Gammaℝ s :=
  (analyticAt_Gammaℝ hs).differentiableAt

/-- Γℝ s ≠ 0 unless s ∈ {0, −2, −4, …}; in particular on −2 < Re s, s ≠ 0. -/
theorem Gammaℝ_ne_zero_of_re {s : ℂ} (hre : -2 < s.re) (h0 : s ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp at hn; exact h0 hn
  · have : s.re = -(2 * n) := by rw [hn]; simp
    have : (1 : ℝ) ≤ n := by exact_mod_cast h
    linarith

/-- Γℝ (1 − s) ≠ 0 on Re s < 3, s ≠ 1. -/
theorem Gammaℝ_one_sub_ne_zero_of_re {s : ℂ} (hre : s.re < 3) (h1 : s ≠ 1) : Gammaℝ (1 - s) ≠ 0 :=
  Gammaℝ_ne_zero_of_re (by simp; linarith) (sub_ne_zero.mpr (Ne.symm h1))

/-- logDeriv Γℝ = −logDeriv G where Γℝ ≠ 0. -/
theorem logDeriv_Gammaℝ_eq_neg {s : ℂ} (hs : Gammaℝ s ≠ 0) : logDeriv Gammaℝ s = -logDeriv invGammaℝ s := by
  rw [Gammaℝ_eq_inv_invGammaℝ]
  have hG := invGammaℝ_ne_zero_iff.mpr hs
  rw [logDeriv_apply, logDeriv_apply, deriv_inv'' (differentiable_invGammaℝ s) hG, Pi.inv_apply]
  field_simp

/-! ### §2. The simple zero of G at 0 -/

/-- G(s) = s · G(s+2)/(2π) for every s (at s = 0 both sides vanish). -/
theorem invGammaℝ_eq_mul (s : ℂ) : invGammaℝ s = s * (invGammaℝ (s + 2) / (2 * Real.pi)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [invGammaℝ_eq_zero_iff, Gammaℝ_eq_zero_iff]
  · rw [invGammaℝ, invGammaℝ, Gammaℝ_add_two hs]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rcases eq_or_ne (Gammaℝ s) 0 with h0 | h0
    · simp [h0]
    · field_simp

lemma invGammaℝ_two : invGammaℝ 2 = Real.pi := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [invGammaℝ, Gammaℝ_def, show (-(2:ℂ)) / 2 = -1 by norm_num, show (2:ℂ) / 2 = 1 by norm_num,
    Complex.Gamma_one, cpow_neg_one, mul_one, inv_inv]

/-- the cofactor h(s) := G(s+2)/(2π), entire with h(0) = ½. -/
def invGammaℝCof (s : ℂ) : ℂ := invGammaℝ (s + 2) / (2 * Real.pi)

lemma differentiable_invGammaℝCof : Differentiable ℂ invGammaℝCof :=
  (differentiable_invGammaℝ.comp (differentiable_id.add_const 2)).div_const _

lemma invGammaℝCof_zero : invGammaℝCof 0 = 1 / 2 := by
  rw [invGammaℝCof, zero_add, invGammaℝ_two]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma invGammaℝ_eq_id_mul : invGammaℝ = fun s => id s * invGammaℝCof s := by
  funext s; rw [id, invGammaℝCof]; exact invGammaℝ_eq_mul s

lemma invGammaℝ_eq_id_mul' : invGammaℝ = id * invGammaℝCof := by
  rw [invGammaℝ_eq_id_mul]; rfl

/-- G has a simple zero at 0. -/
theorem analyticOrderAt_invGammaℝ_zero : analyticOrderAt invGammaℝ 0 = 1 := by
  rw [invGammaℝ_eq_id_mul', analyticOrderAt_mul analyticAt_id (differentiable_invGammaℝCof.analyticAt 0)]
  have h1 : analyticOrderAt (id : ℂ → ℂ) 0 = (1 : ℕ) := by
    rw [analyticAt_id.analyticOrderAt_eq_natCast]
    exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z => by simp⟩
  have h2 : analyticOrderAt invGammaℝCof 0 = 0 :=
    (differentiable_invGammaℝCof.analyticAt 0).analyticOrderAt_eq_zero.mpr (by rw [invGammaℝCof_zero]; norm_num)
  rw [h1, h2, add_zero]; rfl

theorem analyticOrderNatAt_invGammaℝ_zero : analyticOrderNatAt invGammaℝ 0 = 1 := by
  rw [analyticOrderNatAt, analyticOrderAt_invGammaℝ_zero]; rfl

/-- G ∘ (1 − ·) has a simple zero at 1. -/
theorem analyticOrderAt_invGammaℝ_one_sub_one : analyticOrderAt (fun s => invGammaℝ (1 - s)) 1 = 1 := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) 1 := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) 1 ≠ 0 := by rw [deriv_const_sub]; simp
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := invGammaℝ) hg hg'
  simp only [Function.comp_def, sub_self] at this
  rw [this, analyticOrderAt_invGammaℝ_zero]

theorem analyticOrderNatAt_invGammaℝ_one_sub_one : analyticOrderNatAt (fun s => invGammaℝ (1 - s)) 1 = 1 := by
  rw [analyticOrderNatAt, analyticOrderAt_invGammaℝ_one_sub_one]; rfl

/-- **s·(G′/G)(s) → 1 as s → 0.** -/
theorem tendsto_mul_logDeriv_invGammaℝ_zero :
    Tendsto (fun s : ℂ => s * logDeriv invGammaℝ s) (𝓝[≠] 0) (𝓝 1) := by
  -- near 0, s ≠ 0: logDeriv G s = 1/s + logDeriv h s  (h = invGammaℝCof, h 0 = 1/2 ≠ 0)
  have hh0 : invGammaℝCof 0 ≠ 0 := by rw [invGammaℝCof_zero]; norm_num
  have hcont : ContinuousAt (logDeriv invGammaℝCof) 0 := by
    have ha := differentiable_invGammaℝCof.analyticAt 0
    exact ha.deriv.continuousAt.div ha.continuousAt hh0
  -- h ≠ 0 near 0
  have hne : ∀ᶠ s in 𝓝 (0:ℂ), invGammaℝCof s ≠ 0 :=
    differentiable_invGammaℝCof.continuous.continuousAt.eventually_ne hh0
  have hev : ∀ᶠ s in 𝓝[≠] (0:ℂ), s * logDeriv invGammaℝ s = 1 + s * logDeriv invGammaℝCof s := by
    have h1 : ∀ᶠ s in 𝓝[≠] (0:ℂ), s ≠ 0 := self_mem_nhdsWithin
    filter_upwards [h1, mem_nhdsWithin_of_mem_nhds hne] with s hs hhs
    rw [invGammaℝ_eq_id_mul, logDeriv_mul s (by simpa using hs) hhs differentiableAt_id (differentiable_invGammaℝCof s)]
    rw [logDeriv_id]
    field_simp
  have hlim : Tendsto (fun s : ℂ => 1 + s * logDeriv invGammaℝCof s) (𝓝[≠] 0) (𝓝 1) := by
    have h2 : Tendsto (fun s : ℂ => s * logDeriv invGammaℝCof s) (𝓝 0) (𝓝 0) := by
      have := (continuous_id.continuousAt (x := (0:ℂ))).tendsto.mul hcont.tendsto
      simpa using this
    have h3 : Tendsto (fun s : ℂ => s * logDeriv invGammaℝCof s) (𝓝[≠] 0) (𝓝 0) :=
      h2.mono_left nhdsWithin_le_nhds
    have := h3.const_add 1
    simpa using this
  exact hlim.congr' (hev.mono fun _ h => h.symm)

/-! ### §3. χ, L₂ and W on the strip off {0, 1} -/

lemma chiFE_eq_mul : chiFE = fun s => Gammaℝ (1 - s) * invGammaℝ s := by
  funext s; rw [chiFE, invGammaℝ, div_eq_mul_inv]

theorem analyticAt_Gammaℝ_one_sub {s : ℂ} (hs : Gammaℝ (1 - s) ≠ 0) : AnalyticAt ℂ (fun z => Gammaℝ (1 - z)) s :=
  (analyticAt_Gammaℝ hs).comp (analyticAt_const.sub analyticAt_id)

/-- χ is analytic wherever Γℝ(1−s) ≠ 0 (in particular at 0, where it has a simple zero). -/
theorem chiFE_analyticAt' {s : ℂ} (hs : Gammaℝ (1 - s) ≠ 0) : AnalyticAt ℂ chiFE s := by
  rw [chiFE_eq_mul]; exact (analyticAt_Gammaℝ_one_sub hs).mul (analyticAt_invGammaℝ s)

theorem chiFE_ne_zero' {s : ℂ} (h1 : Gammaℝ (1 - s) ≠ 0) (h0 : Gammaℝ s ≠ 0) : chiFE s ≠ 0 := by
  rw [chiFE]; exact div_ne_zero h1 h0

/-- logDeriv χ = logDeriv (Γℝ∘(1−·)) + logDeriv G wherever both factors are nonzero. -/
theorem logDeriv_chiFE_eq {s : ℂ} (h1 : Gammaℝ (1 - s) ≠ 0) (h0 : Gammaℝ s ≠ 0) :
    logDeriv chiFE s = logDeriv (fun z => Gammaℝ (1 - z)) s + logDeriv invGammaℝ s := by
  rw [chiFE_eq_mul, logDeriv_mul s h1 (invGammaℝ_ne_zero_iff.mpr h0)
    (analyticAt_Gammaℝ_one_sub h1).differentiableAt (differentiable_invGammaℝ s)]

/-- logDeriv (Γℝ∘(1−·)) = −logDeriv (G∘(1−·)) wherever Γℝ(1−s) ≠ 0. -/
theorem logDeriv_Gammaℝ_one_sub_eq {s : ℂ} (h1 : Gammaℝ (1 - s) ≠ 0) :
    logDeriv (fun z => Gammaℝ (1 - z)) s = -logDeriv (fun z => invGammaℝ (1 - z)) s := by
  have e : (fun z => Gammaℝ (1 - z)) = (fun z => invGammaℝ (1 - z))⁻¹ := by
    funext z; rw [Pi.inv_apply, invGammaℝ, inv_inv]
  have hd : DifferentiableAt ℂ (fun z => invGammaℝ (1 - z)) s :=
    (differentiable_invGammaℝ _).comp s ((differentiableAt_const _).sub differentiableAt_id)
  have hG : invGammaℝ (1 - s) ≠ 0 := invGammaℝ_ne_zero_iff.mpr h1
  rw [e, logDeriv_apply, logDeriv_apply, deriv_inv'' hd hG, Pi.inv_apply]
  field_simp

theorem L2_analyticAt' {s : ℂ} (h1 : Gammaℝ (1 - s) ≠ 0) (h0 : Gammaℝ s ≠ 0) : AnalyticAt ℂ L2 s := by
  have e : L2 = fun z => -(1/2) * (deriv chiFE z / chiFE z) := by
    funext z; rw [L2, logDeriv_apply]
  rw [e]
  exact analyticAt_const.mul ((chiFE_analyticAt' h1).deriv.div (chiFE_analyticAt' h1) (chiFE_ne_zero' h1 h0))

theorem hardyW_analyticAt' {s : ℂ} (hs1 : s ≠ 1) (h1 : Gammaℝ (1 - s) ≠ 0) (h0 : Gammaℝ s ≠ 0) :
    AnalyticAt ℂ hardyW s := by
  have hζ : AnalyticAt ℂ riemannZeta s := by
    refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact differentiableAt_riemannZeta hz
  have e : hardyW = fun z => deriv riemannZeta z + L2 z * riemannZeta z := rfl
  rw [e]
  exact hζ.deriv.add ((L2_analyticAt' h1 h0).mul hζ)

/-- the working region: the vertical strip −2 < Re s < 3 minus {0, 1}. -/
def stripReg : Set ℂ := {s : ℂ | -2 < s.re ∧ s.re < 3 ∧ s ≠ 0 ∧ s ≠ 1}

lemma isOpen_stripReg : IsOpen stripReg := by
  have e : stripReg = ({s : ℂ | -2 < s.re} ∩ {s : ℂ | s.re < 3}) ∩ ({s : ℂ | s ≠ 0} ∩ {s : ℂ | s ≠ 1}) := by
    ext s; simp only [stripReg, mem_setOf_eq, mem_inter_iff]; tauto
  rw [e]
  exact ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter (isOpen_ne.inter isOpen_ne)

theorem hardyW_analyticAt_of_mem {s : ℂ} (hs : s ∈ stripReg) : AnalyticAt ℂ hardyW s :=
  hardyW_analyticAt' hs.2.2.2 (Gammaℝ_one_sub_ne_zero_of_re hs.2.1 hs.2.2.2) (Gammaℝ_ne_zero_of_re hs.1 hs.2.2.1)

theorem L2_analyticAt_of_mem {s : ℂ} (hs : s ∈ stripReg) : AnalyticAt ℂ L2 s :=
  L2_analyticAt' (Gammaℝ_one_sub_ne_zero_of_re hs.2.1 hs.2.2.2) (Gammaℝ_ne_zero_of_re hs.1 hs.2.2.1)

theorem hardyW_analyticOnNhd_stripReg : AnalyticOnNhd ℂ hardyW stripReg := fun _ hs => hardyW_analyticAt_of_mem hs

end EFContour
end Hardy
end XiPrime
end Zeta23

end
