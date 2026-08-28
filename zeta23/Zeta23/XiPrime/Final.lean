/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The theorems of the ξ′ development, with full types written out.
See Zeta23/XiPrime/Statement.lean for every definition and named proposition used below.

Each theorem's binder list is its list of assumptions.
  • xiDeriv_simple_on_line / _cumulative / headlineFlat_unconditional — no hypotheses.  The flat-window ξ′
    theorem at the Gevrey taper profile ϱ₂ (Zeta23.Taper.rhoTwo).
  • xiDeriv_simple_on_line_flat (any C³ taper profile ϱ; binder hϱ only, conclusion ϱ-free), _flat_std
    (ϱ := smoothTransition, no binders), xiDeriv_fixedLamBounds (every λ ∈ (0,1)), _limitForm (the literal
    λ → 1⁻ sentence) — all unconditional.
  • xiDeriv_simple_on_line_quartic_std (0.86864 / 0.93432, the near-optimal quartic window) — no
    hypotheses; _quartic for any C³ taper (binder hϱ only).
  • hardyW_simple_on_line (Z′: simple real stationary points of Hardy's Z, 0.85838 / 0.92919 of the zeros of
    W = ζ′ + L₂ζ) — no hypotheses; hardyW_simple_on_line_flat for any C³ taper (binder hϱ only).
Proved in this tree:
  (F2) all zeros of ξ′ lie in 0 < Re s < 1 — xiDerivZerosInStrip_holds (Re ξ′/ξ > 0 on Re s ≥ 1
       without the Hadamard product, via the partial fraction of ξ′/ξ over zeta zeros);  (F1) the seam —
  xiDerivSeam_of_strip;  (F3) Riemann–von Mangoldt + local count for ξ′ — xiDeriv_riemannVonMangoldt;
  (E1) the ξ′ explicit formula with frozen coefficients, entrywise — xiEF (with the Gram bridge and TestWeight);
  (C1) (H1)–(H3) for b_N = C(N; L_T) incl. the diagonal law with density D₁ — xiCoeffFamily_hyps (with MainTerm);
  (C2) the coefficient re-expansion — xiReexpansion;  the certified constants certFlat / certQuartic;  the
  quartic-window zero side + admissibility;  the two moments of the fixed-coefficient prime-side
  matrix incl. prop:PP for general coefficients (PP.lean);  the two-trace transfer;
  H-Γ (Zeta23.gammaFacts) and Montgomery–Vaughan (Zeta23.MV.mv_hilbert).

Prior art.  For "simple and on the critical line", unconditionally, the ξ′
constants 0.8584 (flat) / 0.8686 (quartic) exceed the best previous value 0.79874 (Conrey's method,
J. reine angew. Math. 399 (1989), with θ = 4/7, building on J. Number Theory 16 (1983) and, for simple zeros of the
derivatives, J. Number Theory 17 (1983) 71–75; the value is the one recorded in
Farmer, Electron. J. Combin. 2 (1995) and quoted in Farmer–Gonek, arXiv:0803.0425 = Farmer–Gonek–Lee,
J. London Math. Soc. (2) 90 (2014)); they equal Farmer–Gonek–Lee's RH-conditional value with RH removed.  They do not exceed the best known on-line-only proportion (multiplicity
allowed): X. Wu, Quart. J. Math. 66 (2015) 759–771 (arXiv:1206.3737) has 0.86957.
Z′ simple-and-real: Hall 2004:
"Z′ has not been studied directly"; Rolle from PRZZ gives ≈ 0.417.  RH-conditional comparators:
0.8825 simple / 0.9412 distinct (Chirre–Gonçalves–de Laat 2020).  For ξ^{(k)} in short windows (not the dyadic windows of
this file) cf. I. S. Rezvyakova, "Zeros of the derivatives of the Riemann ξ-function", Izv. Math. 69 (2005) 539–605 (proportion
of zeros of ξ^{(k)} on the line > 1 − (3/5)k⁻²) and "On simple zeros of derivatives of the Riemann ξ-function", Izv. Math.
70 (2006) 265–276 (simple zeros of ξ^{(k)} on the line in windows U = T(log(T/2π))^{−10}: proportion ≥ 1 − (e²+2)/(16k²),
uniformly for k ≤ log log T/(2 log log log T)); at k = 1 these are 0.4 and 0.413, below the long-window constants above.

ϱ is the taper profile of the test window (any TaperProfile; the tree's stdProfile = Real.smoothTransition
is supplied in the *_std corollaries so that no profile variable remains).
-/
import Zeta23.XiPrime.Assembly
import Zeta23.XiPrime.Inputs
import Zeta23.XiPrime.Certificate
import Zeta23.XiPrime.Window
import Zeta23.XiPrime.QuarticWindow.ZeroSide
import Zeta23.XiPrime.Seam
import Zeta23.XiPrime.ZeroCount
import Zeta23.XiPrime.ExplicitFormula.ZeroFree
import Zeta23.XiPrime.ExplicitFormula.Main
import Zeta23.XiPrime.Coeff
import Zeta23.XiPrime.Coeff.Reexpansion
import Zeta23.XiPrime.FamilyFlat
import Zeta23.XiPrime.FamilyHyps
import Zeta23.XiPrime.FamilyHypsV
import Zeta23.XiPrime.Hardy.ZeroFree
import Zeta23.XiPrime.Hardy.Seam
import Zeta23.XiPrime.Hardy.Count
import Zeta23.XiPrime.Hardy.EFFinal
import Zeta23.XiPrime.Hardy.ZFunction
import Zeta23.Taper.Gevrey
import Zeta23.Defs.Profile
import Zeta23.RvM.Statement
import Zeta23.Statement.SeamClosed

noncomputable section

open Filter

namespace Zeta23
namespace XiPrime

/-- **The zeros of ξ′, all of them, with multiplicity — hypothesis-free.**  Both (F2) := xiDerivZerosInStrip_holds
and (F1) := xiDerivSeam_of_strip are theorems, so the configuration of
Statement.xiDerivZeros takes no arguments.  carrier = {ρ | ξ′ ρ = 0}, mult = analytic order (rfl). -/
def xiDerivZeros₀ : ZeroConfig :=
  xiDerivZeros xiDerivZerosInStrip_holds (xiDerivSeam_of_strip xiDerivZerosInStrip_holds)

@[simp] lemma xiDerivZeros₀_carrier : xiDerivZeros₀.carrier = {ρ | IsXiDerivZero ρ} := rfl
@[simp] lemma xiDerivZeros₀_mult : xiDerivZeros₀.mult = xiDerivMult := rfl

/-- (F3) for ξ′, hypothesis-free: Riemann–von Mangoldt + local count. -/
theorem xiDerivZeros₀_rvm : RiemannVonMangoldt xiDerivZeros₀ :=
  xiDeriv_riemannVonMangoldt xiDerivZerosInStrip_holds (xiDerivSeam_of_strip xiDerivZerosInStrip_holds)

/-- **The ξ′ explicit formula for the flat family, ANY C³ taper profile, every λ ∈ (0,1)** — xiEF with
(F2) := xiDerivZerosInStrip_holds, the seam := xiDerivSeam_of_strip, and the window-regularity class FamilyHyps :=
familyHyps_flat (Zeta23/XiPrime/FamilyHyps.lean). -/
theorem xiEF_flat {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    XiEF xiDerivZeros₀ (fun _ => paramsOf ϱ lam) :=
  xiEF_xiDerivZeros _ _ (familyHyps_flat (paramsOf_valid hϱ h0 h1.le) h1)

section Flat

variable {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)

include hϱ in
/-- **[XF′ Thm 8.2] — ξ′, flat window, dyadic heights, certified ε-free decimals.**
There is T₀ such that for every T ≥ T₀:
  0.85838 · N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T)  — at least 85.838 % of the zeros ρ₁ of ξ′ with T < Im ρ₁ ≤ 2T,
      counted with multiplicity and with no condition on Re ρ₁, are simple and satisfy Re ρ₁ = 1/2;
  0.92919 · N_{ξ′}(T,2T) ≤ N_{d,ξ′}(T,2T) — at least 92.919 % of them are distinct.
No hypotheses beyond "ϱ is a C³ taper profile" (the test-function family's shape parameter; the conclusion does not
mention ϱ).  See xiDeriv_simple_on_line / _flat_std below for binder-free instances. -/
theorem xiDeriv_simple_on_line_flat :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certFlat
  have hl0 : 0 < lam := by linarith
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := xiReexpansion
  exact headline_of_strict (N := fun T => (Ncount T (2 * T) : ℝ))
    (lowS := fun T => (N0simple T (2 * T) : ℝ)) (lowD := fun T => (Ndist T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd
    (fixedLam_flat _ _ xiDerivZeros₀_rvm hϱ hl0 hl2
      (coeffMoments_flat_xi _ xiDerivZeros₀_rvm hϱ hl0 hl2 xiCoeffFamily_hyps)
      (traceTransfer_flat _ xiDerivZeros₀_rvm hϱ hl0 hl2 (xiEF_flat hϱ hl0 hl2) hρ₀ hE))

include hϱ in
/-- the same sentence, as the Prop HeadlineFlat stated in Statement.lean (rfl repackaging). -/
theorem headlineFlat : HeadlineFlat :=
  xiDeriv_simple_on_line_flat hϱ

include hϱ in
/-- **[XF′ Thm 8.2] — ξ′, flat window, cumulative heights (0,T].**  There is T₀ such that for every T ≥ T₀:
  0.85838 · N_{ξ′}(0,T) ≤ N⁰ˢ_{ξ′}(0,T)   and   0.92919 · N_{ξ′}(0,T) ≤ N_{d,ξ′}(0,T)
(i.e. liminf N⁰ˢ_{ξ′}(T)/N_{ξ′}(T) ≥ 0.85838).  From the dyadic form by dyadic summation (Zeta23.Assembly.dyadic),
using only interval-additivity of the three counts and N_{ξ′}(0,T) → ∞ (from (F3)).  Same conditions. -/
theorem xiDeriv_simple_on_line_flat_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) ∧
      (0.92919 : ℝ) * (Ncount 0 T : ℝ) ≤ (Ndist 0 T : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certFlat
  have hl0 : 0 < lam := by linarith
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := xiReexpansion
  exact headline_of_strict (N := fun T => (Ncount 0 T : ℝ))
    (lowS := fun T => (N0simple 0 T : ℝ)) (lowD := fun T => (Ndist 0 T : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd
    (cumulative_of_fixedLam _ _ xiDerivZeros₀_rvm
      (fixedLam_flat _ _ xiDerivZeros₀_rvm hϱ hl0 hl2
        (coeffMoments_flat_xi _ xiDerivZeros₀_rvm hϱ hl0 hl2 xiCoeffFamily_hyps)
        (traceTransfer_flat _ xiDerivZeros₀_rvm hϱ hl0 hl2 (xiEF_flat hϱ hl0 hl2) hρ₀ hE)))

include hϱ in
theorem headlineCumulative_flat : HeadlineCumulative 0.85838 0.92919 :=
  xiDeriv_simple_on_line_flat_cumulative hϱ

end Flat

/-! ### The same with the tree's concrete profile ϱ := stdProfile (= Real.smoothTransition), so that the
type mentions no profile variable. -/

section FlatStd

/-- Unconditional (ϱ := stdProfile = Real.smoothTransition). -/
theorem xiDeriv_simple_on_line_flat_std :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) :=
  xiDeriv_simple_on_line_flat taperProfile_stdProfile

/-- Unconditional, cumulative. -/
theorem xiDeriv_simple_on_line_flat_cumulative_std :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) ∧
      (0.92919 : ℝ) * (Ncount 0 T : ℝ) ≤ (Ndist 0 T : ℝ) :=
  xiDeriv_simple_on_line_flat_cumulative taperProfile_stdProfile

end FlatStd

/-! ## The hypothesis-free theorem

At the Gevrey taper profile ϱ₂ := Zeta23.Taper.rhoTwo (the C^∞ profile with certified derivative bounds,
Zeta23/Taper/Gevrey.lean) the window-regularity class FamilyHyps of the explicit formula holds for the flat family
(FamilyFlat.familyHyps_flat_gevrey), so xiEF_xiDerivZeros discharges the last binder. -/

section Unconditional

/-- The explicit formula for ξ′ for the flat family at ϱ₂, every λ ∈ (0,1) — a theorem: `xiEF`
with (F2) := `xiDerivZerosInStrip_holds`, the seam := `xiDerivSeam_of_strip`,
FamilyHyps := `familyHyps_flat_gevrey`. -/
theorem xiEF_flat_rhoTwo {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    XiEF xiDerivZeros₀ (fun _ => paramsOf Taper.rhoTwo lam) :=
  xiEF_xiDerivZeros _ _ (familyHyps_flat_gevrey Taper.gevreyProfile_rhoTwo h0 h1)

/-- **[XF′ Thm 8.2] for ξ′ — unconditional, no hypotheses.**  There is T₀ such that for every T ≥ T₀:
  0.85838 · N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T)   and   0.92919 · N_{ξ′}(T,2T) ≤ N_{d,ξ′}(T,2T),
where N_{ξ′}(T,2T) is the number of zeros ρ₁ of ξ′ (ξ = Riemann's xi-function, Defs.xi, identified with Mathlib's
completedRiemannZeta by Statement.xi_eq) with T < Im ρ₁ ≤ 2T counted with multiplicity and with no condition
on Re ρ₁, N⁰ˢ_{ξ′} counts those that are simple with Re ρ₁ = 1/2, and N_{d,ξ′} the distinct ones.  I.e. at
least 85.838 % of the zeros of ξ′ are simple and on the critical line, and at least 92.919 % are distinct. -/
theorem xiDeriv_simple_on_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) :=
  xiDeriv_simple_on_line_flat Taper.gevreyProfile_rhoTwo.taper

/-- **cumulative form, unconditional:** 0.85838·N_{ξ′}(0,T) ≤ N⁰ˢ_{ξ′}(0,T) and 0.92919·N_{ξ′}(0,T) ≤ N_{d,ξ′}(0,T)
for all large T (liminf_{T→∞} N⁰ˢ_{ξ′}(T)/N_{ξ′}(T) ≥ 0.85838). -/
theorem xiDeriv_simple_on_line_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) ∧
      (0.92919 : ℝ) * (Ncount 0 T : ℝ) ≤ (Ndist 0 T : ℝ) :=
  xiDeriv_simple_on_line_flat_cumulative Taper.gevreyProfile_rhoTwo.taper

/-- **[XF′ Thm 8.2] at every fixed λ ∈ (0,1), flat window — unconditional:** for every ε > 0 and all large T,
(2 − κ₁(λ) − ε)·N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T) and (3/2 − κ₁(λ)/2 − ε)·N_{ξ′}(T,2T) ≤ N_{d,ξ′}(T,2T), κ₁(λ) := kappaXi λ vFlat
= 1/c_λ(flat; D₁) with the full series D₁ (Statement.FixedLamBounds). -/
theorem xiDeriv_fixedLamBounds {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : FixedLamBounds vFlat lam := by
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := xiReexpansion
  exact fixedLam_flat _ _ xiDerivZeros₀_rvm Taper.gevreyProfile_rhoTwo.taper h0 h1
    (coeffMoments_flat_xi _ xiDerivZeros₀_rvm Taper.gevreyProfile_rhoTwo.taper h0 h1 xiCoeffFamily_hyps)
    (traceTransfer_flat _ xiDerivZeros₀_rvm Taper.gevreyProfile_rhoTwo.taper h0 h1 (xiEF_flat_rhoTwo h0 h1)
      hρ₀ hE)

/-- **[XF′ Thm 8.2], the literal λ → 1⁻ form, flat window — unconditional:** for every ε > 0 and all large T,
(2 − κ₁(1) − ε)·N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T) and (3/2 − κ₁(1)/2 − ε)·N_{ξ′}(T,2T) ≤ N_{d,ξ′}(T,2T), where
κ₁(1) = kappaXi 1 vFlat = 1/λ + 2∫₀¹(1−r)D₁(λr)dr at λ = 1 ([XF′]: 2 − κ₁(1) = 0.858383…).  From the fixed-λ form by
continuity of λ ↦ κ₁(λ) on (0,1] (continuousOn_kappaXi_vFlat + eps_form_of_continuousOn). -/
theorem xiDeriv_simple_on_line_limitForm :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - kappaXi 1 vFlat - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (3 / 2 - kappaXi 1 vFlat / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  have hκ : ContinuousOn (fun lam => kappaXi lam vFlat) (Set.Icc (1/2) 1) :=
    continuousOn_kappaXi_vFlat.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hA := eps_form_of_continuousOn (g := fun lam => 2 - kappaXi lam vFlat)
    (N := fun T => (Ncount T (2 * T) : ℝ)) (lower := fun T => (N0simple T (2 * T) : ℝ))
    (continuousOn_const.sub hκ) (fun _ => Nat.cast_nonneg _)
    (fun lam hl1 hl2 ε hε => by
      obtain ⟨T₀, hT₀⟩ := xiDeriv_fixedLamBounds (by linarith) hl2 ε hε
      exact ⟨T₀, fun T hT => (hT₀ T hT).1⟩)
  have hB := eps_form_of_continuousOn (g := fun lam => 3 / 2 - kappaXi lam vFlat / 2)
    (N := fun T => (Ncount T (2 * T) : ℝ)) (lower := fun T => (Ndist T (2 * T) : ℝ))
    (continuousOn_const.sub (hκ.div_const 2)) (fun _ => Nat.cast_nonneg _)
    (fun lam hl1 hl2 ε hε => by
      obtain ⟨T₀, hT₀⟩ := xiDeriv_fixedLamBounds (by linarith) hl2 ε hε
      exact ⟨T₀, fun T hT => (hT₀ T hT).2⟩)
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hA ε hε
  obtain ⟨T₂, hT₂⟩ := hB ε hε
  exact ⟨max T₁ T₂, fun T hT =>
    ⟨hT₁ T ((le_max_left _ _).trans hT), hT₂ T ((le_max_right _ _).trans hT)⟩⟩

/-- Non-vacuity companions.  The counted sets are finite — so Ncount (a finsum) and N0simple/Ndist (ncard's) are
honest cardinalities, not Lean's junk value 0 for infinite sets — and the denominator N_{ξ′}(T,2T) → ∞. -/
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  have h := xiDerivZeros₀.window_finite T₁ T₂
  rwa [show xiDerivZeros₀.window T₁ T₂ = zerosIn T₁ T₂ from xiDerivZeros_window _ _ _ _] at h

theorem tendsto_Ncount_atTop : Tendsto (fun T => (Ncount T (2 * T) : ℝ)) atTop atTop := by
  simpa [xiDerivZeros₀] using Assembly.tendsto_N_atTop xiDerivZeros₀ xiDerivZeros₀_rvm

/-- the Props stated in Statement.lean, unconditionally. -/
theorem headlineFlat_unconditional : HeadlineFlat := xiDeriv_simple_on_line

theorem headlineCumulative_unconditional : HeadlineCumulative 0.85838 0.92919 :=
  xiDeriv_simple_on_line_cumulative

end Unconditional

/-! ## The same proportions against the zeta zero count N(T,2T)  ([XF′ (F3)]: N_{ξ′}(T) = N(T) + O(log T))

Both configurations obey Riemann–von Mangoldt with the same main term (T/2π)ℓ₁ (ξ′: xiDerivZeros₀_rvm; ζ:
Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts), so N_{ξ′}(T,2T) ≥ (1−δ)N_ζ(T,2T) eventually for every δ > 0, and the strict
certificate margin absorbs the δ.  N_ζ = Zeta23.Ncount = the nontrivial zeros of Mathlib's riemannZeta in T < Im ≤ 2T
with multiplicity (Zeta23/Statement.lean). -/

section VsZeta

open Asymptotics in
/-- N_{ξ′}(T,2T) ≥ (1 − δ)·N_ζ(T,2T) eventually, every δ > 0. -/
theorem eventually_zetaCount_le_Ncount (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ T in atTop, (1 - δ) * (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) ≤ (Ncount T (2 * T) : ℝ) := by
  have hRζ : RiemannVonMangoldt Zeta23.zetaZeroConfig := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  obtain ⟨C₁, T₁, h₁⟩ := xiDerivZeros₀_rvm.main
  obtain ⟨C₂, T₂, h₂⟩ := hRζ.main
  -- (|C₁| + |C₂|)·log T = o(N_ζ)
  have ho : (fun T => (|C₁| + |C₂|) * Real.log T) =o[atTop] fun T => (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) :=
    Assembly.isLittleO_N_of_isLittleO_Tl _ hRζ (Assembly.isLittleO_log_Tl.const_mul_left _)
  filter_upwards [ho.def hδ, eventually_ge_atTop T₁, eventually_ge_atTop T₂, eventually_ge_atTop (1:ℝ)]
    with T hsmall hT₁ hT₂ hT1
  have hN0 : 0 ≤ (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0, abs_of_nonneg (by positivity)] at hsmall
  have a₁ := (abs_le.mp (h₁ T hT₁)).1
  have a₂ := (abs_le.mp (h₂ T hT₂)).2
  have e : (xiDerivZeros₀.N T (2 * T) : ℝ) = (Ncount T (2 * T) : ℝ) := by simp [xiDerivZeros₀]
  rw [e] at a₁
  have hC₁ : C₁ * Real.log T ≤ |C₁| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self _) hlog
  have hC₂ : C₂ * Real.log T ≤ |C₂| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self _) hlog
  nlinarith

/-- **vs. N_ζ — unconditional:** there is T₀ such that for every T ≥ T₀,
  0.85838 · N_ζ(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T)   and   0.92919 · N_ζ(T,2T) ≤ N_{d,ξ′}(T,2T),
N_ζ(T,2T) = Zeta23.Ncount T (2T) = # nontrivial zeros of ζ with T < Im ≤ 2T, with multiplicity.  ("At least 85.838 % of
N(T,2T)": that many simple critical-line zeros of ξ′ at height in (T,2T].) -/
theorem xiDeriv_simple_vs_zetaCount :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certFlat
  have hl0 : 0 < lam := by linarith
  have hfix := xiDeriv_fixedLamBounds hl0 hl2
  have hκ : 0 ≤ kappaXi lam vFlat := (kappaXi_pos_vFlat hl0 hl2.le).le
  refine headline_of_strict (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (lowS := fun T => (N0simple T (2 * T) : ℝ)) (lowD := fun T => (Ndist T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd ?_
  intro ε hε
  -- ε/2 on the ξ′ side, δ := ε/8 on the count side ((2−κ)·δ ≤ 2δ ≤ ε/4 ≤ ε/2)
  obtain ⟨T₁, hT₁⟩ := hfix (ε / 2) (by linarith)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_zetaCount_le_Ncount (ε / 8) (by linarith))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  obtain ⟨hA, hB⟩ := hT₁ T ((le_max_left _ _).trans hT)
  have hz := hT₂ T ((le_max_right _ _).trans hT)
  have ez : (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) = (Zeta23.Ncount T (2 * T) : ℝ) := by
    simp [Zeta23.zetaZeroConfig]
  rw [ez] at hz
  have hNζ : 0 ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hNξ : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hκ2 : kappaXi lam vFlat ≤ 2 := by linarith
  have hS0 : 0 ≤ (N0simple T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hD0 : 0 ≤ (Ndist T (2 * T) : ℝ) := Nat.cast_nonneg _
  show (2 - kappaXi lam vFlat - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
    (3 / 2 - kappaXi lam vFlat / 2 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ)
  constructor
  · by_cases h : 0 ≤ 2 - kappaXi lam vFlat - ε
    · have h2 : 0 ≤ 2 - kappaXi lam vFlat - ε / 2 := by linarith
      have step := mul_le_mul_of_nonneg_left hz h2
      have k1 : 0 ≤ 4 - (2 - kappaXi lam vFlat) + ε / 2 := by linarith
      have key := mul_nonneg (mul_nonneg hε.le k1) hNζ
      linarith [step, hA, key]
    · have h' : 2 - kappaXi lam vFlat - ε < 0 := lt_of_not_ge h
      nlinarith [h', hNζ, hS0]
  · by_cases h : 0 ≤ 3 / 2 - kappaXi lam vFlat / 2 - ε
    · have h2 : 0 ≤ 3 / 2 - kappaXi lam vFlat / 2 - ε / 2 := by linarith
      have step := mul_le_mul_of_nonneg_left hz h2
      have k1 : 0 ≤ 4 - (3 / 2 - kappaXi lam vFlat / 2) + ε / 2 := by linarith
      have key := mul_nonneg (mul_nonneg hε.le k1) hNζ
      linarith [step, hB, key]
    · have h' : 3 / 2 - kappaXi lam vFlat / 2 - ε < 0 := lt_of_not_ge h
      nlinarith [h', hNζ, hD0]

end VsZeta

/-! ## The quartic window  v(s) = 1 − (7/100)(2s)² − (51/200)(2s)⁴  [XF′ Thm 8.2, optimal-window line]

Same binder list as the flat case: the extra input (the zero-side facts for the height family
Pf := (paramsOf ϱ λ).atV vQuartic — Assembly.WindowZeroSide) is proved as windowZeroSide_atV
(XiPrime/QuarticWindow/ZeroSide.lean), and the quartic prime-side inputs are Inputs.coeffMoments_quartic_xi /
Inputs.traceTransfer_quartic. -/

/-- **The ξ′ explicit formula for the window family P.atV v, any C³ taper and any admissible profile v,
every λ ∈ (0,1)** — xiEF with FamilyHyps := familyHyps_atV (Zeta23/XiPrime/FamilyHypsV.lean). -/
theorem xiEF_atV {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {v : ℝ → ℝ}
    (hv : WindowProfile v) : XiEF xiDerivZeros₀ ((paramsOf ϱ lam).atV v) :=
  xiEF_xiDerivZeros _ _ (familyHyps_atV (paramsOf_valid hϱ h0 h1.le) h1 hv)

section Quartic

variable {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)

include hϱ in
/-- **[XF′ Thm 8.2] — ξ′, quartic window, dyadic heights, certified ε-free decimals.**
There is T₀ such that for every T ≥ T₀:
  0.86864 · N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T)   (≥ 86.864 % simple and on Re s = 1/2),
  0.93432 · N_{ξ′}(T,2T) ≤ N_{d,ξ′}(T,2T)  (≥ 93.432 % distinct).
No hypotheses beyond "ϱ is a C³ taper profile" (conclusion ϱ-free); see xiDeriv_simple_on_line_quartic_std for the
binder-free instance. -/
theorem xiDeriv_simple_on_line_quartic :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (0.93432 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certQuartic
  have hl0 : 0 < lam := by linarith
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := xiReexpansion
  exact headline_of_strict (N := fun T => (Ncount T (2 * T) : ℝ))
    (lowS := fun T => (N0simple T (2 * T) : ℝ)) (lowD := fun T => (Ndist T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd
    (fixedLam_family _ _ xiDerivZeros₀_rvm hϱ hl0 hl2
      (windowZeroSide_atV _ xiDerivZeros₀_rvm (paramsOf_valid hϱ hl0 hl2.le))
      (coeffMoments_quartic_xi _ xiDerivZeros₀_rvm hϱ hl0 hl2 xiCoeffFamily_hyps)
      (traceTransfer_quartic _ xiDerivZeros₀_rvm hϱ hl0 hl2 (xiEF_atV hϱ hl0 hl2 windowProfile_vQuartic)
          hρ₀ hE))

include hϱ in
theorem headlineQuartic : HeadlineQuartic :=
  xiDeriv_simple_on_line_quartic hϱ

include hϱ in
/-- **[XF′ Thm 8.2] — ξ′, quartic window, cumulative heights (0,T]:**
0.86864·N_{ξ′}(0,T) ≤ N⁰ˢ_{ξ′}(0,T) and 0.93432·N_{ξ′}(0,T) ≤ N_{d,ξ′}(0,T) for all large T.  Same conditions. -/
theorem xiDeriv_simple_on_line_quartic_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) ∧
      (0.93432 : ℝ) * (Ncount 0 T : ℝ) ≤ (Ndist 0 T : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certQuartic
  have hl0 : 0 < lam := by linarith
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := xiReexpansion
  exact headline_of_strict (N := fun T => (Ncount 0 T : ℝ))
    (lowS := fun T => (N0simple 0 T : ℝ)) (lowD := fun T => (Ndist 0 T : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd
    (cumulative_of_fixedLam _ _ xiDerivZeros₀_rvm
      (fixedLam_family _ _ xiDerivZeros₀_rvm hϱ hl0 hl2
        (windowZeroSide_atV _ xiDerivZeros₀_rvm (paramsOf_valid hϱ hl0 hl2.le))
        (coeffMoments_quartic_xi _ xiDerivZeros₀_rvm hϱ hl0 hl2 xiCoeffFamily_hyps)
        (traceTransfer_quartic _ xiDerivZeros₀_rvm hϱ hl0 hl2 (xiEF_atV hϱ hl0 hl2 windowProfile_vQuartic)
          hρ₀ hE)))

include hϱ in
theorem headlineCumulative_quartic : HeadlineCumulative 0.86864 0.93432 :=
  xiDeriv_simple_on_line_quartic_cumulative hϱ

end Quartic

/-- **[XF′ Thm 8.2], quartic (near-optimal) window — unconditional, no hypotheses:** for all large T,
0.86864·N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T) and 0.93432·N_{ξ′}(T,2T) ≤ N_{d,ξ′}(T,2T) — at least 86.864 % of the zeros of ξ′ are
simple and on the critical line, at least 93.432 % are distinct. -/
theorem xiDeriv_simple_on_line_quartic_std :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (0.93432 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) :=
  xiDeriv_simple_on_line_quartic taperProfile_stdProfile

theorem xiDeriv_simple_on_line_quartic_cumulative_std :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) ∧
      (0.93432 : ℝ) * (Ncount 0 T : ℝ) ≤ (Ndist 0 T : ℝ) :=
  xiDeriv_simple_on_line_quartic_cumulative taperProfile_stdProfile

theorem headlineQuartic_unconditional : HeadlineQuartic := xiDeriv_simple_on_line_quartic_std

theorem headlineCumulative_quartic_unconditional : HeadlineCumulative 0.86864 0.93432 :=
  xiDeriv_simple_on_line_quartic_cumulative_std

/-! ## Z′ — the stationary points of Hardy's function  [XF′ §9, Thm 9.4]

W := ζ′ + L₂ζ (Defs.hardyW) is the Mathlib-honest meromorphic function with Z′(t) = i e^{iϑ(t)} W(½+it)
[XF′ (Z3)], so "t ∈ (T,2T], Z′(t) = 0 ≠ Z″(t)" is "½+it is a simple zero of W" and NcountW counts all non-real
zeros of W in the height window.  The W headline is assembled by the same spine at Z := the zeros of W with
|Im| ≥ t_W.  Inputs, all proved in this tree: (Z6)(iii) — there is t_W > 0 above which every zero of W lies in
the open strip — wZerosInStrip_holds (reflection-symmetry positivity Σ_{|γ|≤T} m_ρ(1−β_ρ) = N_T/2 beats
Re L₋ = O(1/t²); no Littlewood gap theorem, no zero-free region); the W seam wSeam_of_strip; the
zero-side family facts (windowZeroSide_flat); the prime side for wCoeffFamily (wCoeffFamily_hyps + the ξ′ prime
side; same density D₁ ⇒ same κ₁ ⇒ the same certificate certFlat).  (Z7) H-RvM + local count for W —
riemannVonMangoldt_W.  The W two-trace transfer wTraceTransfer_of with wReexpansion
(Inputs.traceTransfer_flat_w).  The W explicit formula WEF (StatementW.lean) for the flat family
(wEF_flat below), so the W headlines carry no hypothesis beyond the taper binder hϱ. -/

/-- the height t_W > 0 above which all zeros of W are in the open critical strip (from wZerosInStrip_holds). -/
def wStripHeight : ℝ := Classical.choose wZerosInStrip_holds

theorem wStripHeight_pos : 0 < wStripHeight := (Classical.choose_spec wZerosInStrip_holds).1

theorem wZerosInStrip_wStripHeight : WZerosInStrip wStripHeight := (Classical.choose_spec wZerosInStrip_holds).2

/-- The W seam facts at `t_W`, obtained as a theorem via `wSeam_of_strip`. -/
theorem wSeam_wStripHeight : WSeam wStripHeight := wSeam_of_strip wStripHeight_pos wZerosInStrip_wStripHeight

/-- **The zeros of W with |Im| ≥ t_W, all of them, with multiplicity — hypothesis-free configuration.** -/
def wZeros₀ : ZeroConfig := wZeros wZerosInStrip_wStripHeight wSeam_wStripHeight

/-- (Z7) for W, hypothesis-free: Riemann–von Mangoldt + local count for the zeros of W above t_W. -/
theorem wZeros₀_rvm : RiemannVonMangoldt wZeros₀ := riemannVonMangoldt_W wZerosInStrip_wStripHeight wSeam_wStripHeight

/-- **The W explicit formula for the flat family, any C³ taper, every λ ∈ (0,1)** — the W explicit formula wEF
(assembled from EFExpansion, EFContour, the test-weight / Gram-bridge / low-zero facts and the pole + L-series facts) instantiated at
(Z6) := wZerosInStrip_holds, seam := wSeam_of_strip, (Z7) := riemannVonMangoldt_W, FamilyHyps := familyHyps_flat. -/
theorem wEF_flat {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    WEF wZeros₀ (fun _ => paramsOf ϱ lam) :=
  wEF wZerosInStrip_wStripHeight wSeam_wStripHeight wZeros₀_rvm _ (familyHyps_flat (paramsOf_valid hϱ h0 h1.le) h1)

section HardyFlat

variable {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)

include hϱ in
/-- **[XF′ Thm 9.4] — Z′, flat window:** there is T₀ such that for every T ≥ T₀,
  0.85838 · N_W(T,2T) ≤ #{ρ : W(ρ) = 0 simple, Re ρ = 1/2, T < Im ρ ≤ 2T}  (= #{t ∈ (T,2T] : Z′(t) = 0 ≠ Z″(t)}),
  0.92919 · N_W(T,2T) ≤ N_{d,W}(T,2T),
where N_W counts all zeros of W with T < Im ≤ 2T with multiplicity.  No hypotheses beyond "ϱ is a C³ taper profile"
(conclusion ϱ-free); hardyW_simple_on_line below is the binder-free instance. -/
theorem hardyW_simple_on_line_flat :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (N0simpleW T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (NdistW T (2 * T) : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certFlat
  have hl0 : 0 < lam := by linarith
  exact headline_of_strict (N := fun T => (NcountW T (2 * T) : ℝ))
    (lowS := fun T => (N0simpleW T (2 * T) : ℝ)) (lowD := fun T => (NdistW T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd
    (fixedLam_family_W wZerosInStrip_wStripHeight wSeam_wStripHeight wZeros₀_rvm hϱ hl0 hl2
      (windowZeroSide_flat wZeros₀ wZeros₀_rvm (paramsOf ϱ lam) (paramsOf_valid hϱ hl0 hl2.le))
      (coeffMoments_flat_w _ wZeros₀_rvm hϱ hl0 hl2 wCoeffFamily_hyps)
      (traceTransfer_flat_w _ wZeros₀_rvm hϱ hl0 hl2 (wEF_flat hϱ hl0 hl2)))

include hϱ in
theorem headlineW_flat : HeadlineW 0.85838 0.92919 :=
  hardyW_simple_on_line_flat hϱ

end HardyFlat

/-- **[XF′ Thm 9.4] — simple stationary points of Hardy's Z-function — unconditional, no hypotheses.**
There is T₀ such that for every T ≥ T₀:
  0.85838 · N_W(T,2T) ≤ N⁰ˢ_W(T,2T)   and   0.92919 · N_W(T,2T) ≤ N_{d,W}(T,2T),
where W := ζ′ + L₂ζ = ζ′ − ½(χ′/χ)ζ (Defs.hardyW; Z′(t) = i e^{iϑ(t)} W(½+it) [XF′ (Z3)]), N_W(T,2T) counts all zeros of W with
T < Im ≤ 2T with multiplicity (NcountW), N⁰ˢ_W those that are simple with Re = 1/2 — equivalently the t ∈ (T,2T] with
Z′(t) = 0 ≠ Z″(t) — and N_{d,W} the distinct ones.  So at least 85.838 % of the zeros of W (of "𝒵′") at height in (T,2T]
are simple and on the critical line, i.e. are simple real stationary points of Hardy's Z. -/
theorem hardyW_simple_on_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (N0simpleW T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (NdistW T (2 * T) : ℝ) :=
  hardyW_simple_on_line_flat taperProfile_stdProfile

theorem headlineW_unconditional : HeadlineW 0.85838 0.92919 := hardyW_simple_on_line

/-! ### Z′ with the quartic window  [XF′ Thm 9.4 "resp. 86.86 % (optimal window)"] -/

/-- the W explicit formula for the profiled family P.atV v, any C³ taper, any admissible profile. -/
theorem wEF_atV {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {v : ℝ → ℝ}
    (hv : WindowProfile v) : WEF wZeros₀ ((paramsOf ϱ lam).atV v) :=
  wEF wZerosInStrip_wStripHeight wSeam_wStripHeight wZeros₀_rvm _
    (familyHyps_atV (paramsOf_valid hϱ h0 h1.le) h1 hv)

/-- **[XF′ Thm 9.4], quartic window — any C³ taper:** 0.86864·N_W(T,2T) ≤ N⁰ˢ_W(T,2T) and 0.93432·N_W ≤ N_{d,W}, large T. -/
theorem hardyW_simple_on_line_quartic {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (N0simpleW T (2 * T) : ℝ) ∧
      (0.93432 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (NdistW T (2 * T) : ℝ) := by
  obtain ⟨lam, hl1, hl2, hc, hcd⟩ := certQuartic
  have hl0 : 0 < lam := by linarith
  exact headline_of_strict (N := fun T => (NcountW T (2 * T) : ℝ))
    (lowS := fun T => (N0simpleW T (2 * T) : ℝ)) (lowD := fun T => (NdistW T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) hc hcd
    (fixedLam_family_W wZerosInStrip_wStripHeight wSeam_wStripHeight wZeros₀_rvm hϱ hl0 hl2
      (windowZeroSide_atV wZeros₀ wZeros₀_rvm (paramsOf_valid hϱ hl0 hl2.le))
      (coeffMoments_quartic_w _ wZeros₀_rvm hϱ hl0 hl2 wCoeffFamily_hyps)
      (traceTransfer_quartic_w _ wZeros₀_rvm hϱ hl0 hl2 (wEF_atV hϱ hl0 hl2 windowProfile_vQuartic)))

/-- **[XF′ Thm 9.4], quartic window — unconditional, no hypotheses:** at least 86.864 % of the zeros of W at height in
(T,2T] are simple real stationary points of Hardy's Z, at least 93.432 % are distinct. -/
theorem hardyW_simple_on_line_quartic_std :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (N0simpleW T (2 * T) : ℝ) ∧
      (0.93432 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (NdistW T (2 * T) : ℝ) :=
  hardyW_simple_on_line_quartic taperProfile_stdProfile

theorem headlineW_quartic_unconditional : HeadlineW 0.86864 0.93432 := hardyW_simple_on_line_quartic_std

/-! ## Z′ literally: simple real stationary points of Hardy's Z-function  [XF′ (Z3) + Thm 9.4]

Zeta23/XiPrime/Hardy/ZFunction.lean defines Hardy's Z branch-free: sline t := 1/2 + t·I, Gfun t := Γℝ(sline t),
ephase t := Gfun t / ‖Gfun t‖ (= e^{iϑ(t)} — no arg/log branch), ZC t := ephase t · ζ(sline t), hardyZ t := (ZC t).re, and proves
ZC is real, HasDerivAt ZC (I · ephase t · hardyW (sline t)) t for t ≠ 0 [(Z3)], hence Z′(t) = 0 ↔ W(½+it) = 0 and then
Z″(t) ≠ 0 ↔ the zero is simple, and ncard_simpleStationaryZ : for 0 < T,
  #{t ∈ (T,2T] | Z′(t) = 0 ∧ Z″(t) ≠ 0} = N0simpleW T (2T). -/

section HardyZ

/-- **Simple real stationary points of Hardy's Z — unconditional, no hypotheses** ([XF′ Thm 9.4], flat window):
there is T₀ such that for every T ≥ T₀,
  0.85838 · N_W(T,2T) ≤ #{t ∈ (T,2T] : Z′(t) = 0 and Z″(t) ≠ 0},
N_W(T,2T) = NcountW T (2T) = the number of zeros of W = ζ′ − ½(χ′/χ)ζ with T < Im ≤ 2T, counted with multiplicity
(= N(T,2T) + O(log T), the zeta zero count, by Hardy.Count), Z = hardyZ Hardy's Z-function (ZFunction.lean). -/
theorem hardyZ_simple_stationary_points :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (NcountW T (2 * T) : ℝ)
        ≤ ({t ∈ Set.Ioc T (2 * T) | deriv hardyZ t = 0 ∧ deriv (deriv hardyZ) t ≠ 0}.ncard : ℝ) := by
  obtain ⟨T₀, h⟩ := hardyW_simple_on_line
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith [le_max_right T₀ 1]
  have := (h T (le_trans (le_max_left _ _) hT)).1
  rw [← ncard_simpleStationaryZ hT0] at this
  simpa [simpleStationaryZ] using this

/-- the same with the quartic window: **0.86864 · N_W(T,2T) ≤ #{t ∈ (T,2T] : Z′(t) = 0 ≠ Z″(t)}**, unconditionally. -/
theorem hardyZ_simple_stationary_points_quartic :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (NcountW T (2 * T) : ℝ)
        ≤ ({t ∈ Set.Ioc T (2 * T) | deriv hardyZ t = 0 ∧ deriv (deriv hardyZ) t ≠ 0}.ncard : ℝ) := by
  obtain ⟨T₀, h⟩ := hardyW_simple_on_line_quartic_std
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith [le_max_right T₀ 1]
  have := (h T (le_trans (le_max_left _ _) hT)).1
  rw [← ncard_simpleStationaryZ hT0] at this
  simpa [simpleStationaryZ] using this

end HardyZ

end XiPrime
end Zeta23

end
