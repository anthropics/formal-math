/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula.lean — interface of the ξ′ explicit-formula development.

This file contains the shared definitions (FamilyHyps, the ξ ↔ WeilEF.xi bridge; Lfn comes from
Seam.lean) and the catalogue of the interface statements (§§2–7 below, as documentation).  The
statements themselves live, under exactly these names in namespace Zeta23.XiPrime, in the proof files
Zeta23/XiPrime/ExplicitFormula/*.lean, all re-exported by Zeta23/XiPrime/ExplicitFormula/Main.lean —
that is the module consumers import; every catalogued statement is proved there.  Proof files
import this file.

Design decisions (do not rely on a body by rfl without checking these):
* ξ is Zeta23.XiPrime.xi (Defs.lean) = Zeta23.WeilEF.xi by rfl (Zeta23/WeilEF/Effective.lean), so
  xi_differentiable / xi_eq / xi_one_sub transfer.
* (F2) "all zeros of ξ′ lie in 0 < Re s < 1" is Statement.lean's named Prop XiDerivZerosInStrip.
  Everything that needs it takes it as an explicit hypothesis (hF2 : XiDerivZerosInStrip), so the
  development is conditional on it; `theorem xiDerivZerosInStrip_holds : XiDerivZerosInStrip`
  (§2, Hadamard-free contour proof, file ExplicitFormula/ZeroFree.lean) discharges it.
* The contour runs on the fixed line Re s = c, 1 < c ≤ 3/2 (we use c = 5/4, the WeilEF line),
  not on [XF′]'s σ₁ = 1 + 3/l.  Reason: every WeilEF line lemma (gamma_line_shift,
  norm_logDeriv_Gammaℝ_le, integrable_Hfn_mul_*, Hfn_mirror, tilted_inversion) is proved for
  1 < c ≤ 3/2 and is reused verbatim; the expansion |A/L| < 1 of [XF′ Lemma 2.2] is better at
  c = 5/4 (A(5/4) = O(1) vs |L| ≍ l); the price is the entry error X^{c−1/2} = X^{3/4} instead of
  X^{1/2}, which is still a power saving T^{−δ} for every λ ≤ 1 (δ = (1 − 3λ/4)/2), and a power
  saving is all the two traces consume ([XF′ Lemma 5.1]: |tr E| ≤ d·ε, ‖E‖_F² ≤ C·d·L·ε²).  Hence
  (EF4) is stated with error  C · T^{−δ} · (1/max(1, (τ_k−τ_l)²) + 1/T)  (the 1/T floor carries the
  Δ-independent far-region terms of [XF′ Thm 4.2 proof (b),(d)]).
* Zero sums are over the subtype of {ρ | IsXiDerivZero ρ} (= all zeros of ξ′, Defs) weighted by xiDerivMult
  (= analyticOrderAt, Defs.lean); (EF4) is stated for ANY Z : ZeroConfig whose carrier is {ρ | IsXiDerivZero ρ}
  and whose mult agrees with xiDerivMult on it, so it applies to Statement's xiDerivZeros however
  that instance is packaged.
-/
import Zeta23.XiPrime.Seam
import Zeta23.WeilEF.Main
import Zeta23.WeilEF.Effective

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn)

/-! ## 0. Bridge to Zeta23.WeilEF.xi (same body ⇒ rfl), so Effective.lean's ξ-bounds transfer.
(ξ entire, ξ(1−s) = ξ(s), ξ = ½s(s−1)Λ off {0,1}, ξ′ entire: Statement.lean §1, proved there.) -/

theorem xi_eq_weilXi : xi = Zeta23.WeilEF.xi := rfl

/-! ## 1. (F1) Symmetries and the seam (Zeta23/XiPrime/Seam.lean):
xiDeriv_one_sub, xi_conj, xiDeriv_conj, xiDeriv_reflect, xiDeriv_reflect_eq_zero_iff,
xiDerivMult_reflect, one_le_xiDerivMult_iff, analyticOrderAt_xiDeriv_ne_top,
xiDeriv_zeros_finite_of_isCompact, xiDerivSeam_of_strip (hF2 : XiDerivZerosInStrip) : XiDerivSeam;
Zeta23/XiPrime/ZeroCount.lean: xiDeriv_riemannVonMangoldt hF2 hs : XiDerivRvM hF2 hs; and
Zeta23/XiPrime/ZeroCount/GoodHeights.lean: xiDeriv_good_heights (signature in §3). -/

/-! ## 2. (F2) All zeros of ξ′ lie in the open critical strip  [XF′ §1 (F2)]
Proved in ExplicitFormula/ZeroFree.lean.  Hadamard-free route: for ξ(s) ≠ 0,
Re ξ′/ξ(s) = Σ_ρ m_ρ Re 1/(s−ρ) (sum over the zeros of ξ, absolutely convergent), by integrating
g(w)·ξ′/ξ(w), g(w) = 1/(s−w) − 1/(s′−w), s′ = 1 − s̄, over expanding rectangles (Zeta23.Analytic residue
calculus + WeilEF good heights); every term is > 0 when Re s ≥ 1.  STATEMENTS:
  theorem re_logDeriv_xi_pos {s : ℂ} (hs : 1 ≤ s.re) : 0 < (logDeriv xi s).re
  theorem xiDeriv_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiDeriv s ≠ 0
  theorem xiDeriv_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xiDeriv s ≠ 0
  theorem xiDerivZerosInStrip_holds : XiDerivZerosInStrip
Downstream statements that do not use the last theorem carry (hF2 : XiDerivZerosInStrip) explicitly. -/

/-! ## 3. (F3) Local count / good heights — proved elsewhere; consumed here:
  theorem xiDeriv_good_heights : ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R : ℝ,
      (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧ ∀ s : ℂ, (s.im = R ∨ s.im = -R) → -1 ≤ s.re → s.re ≤ 2 →
        xiDeriv s ≠ 0 ∧ ‖logDeriv xiDeriv s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2
  (xiDeriv_riemannVonMangoldt hF2 hs).local_count :
      ∃ A₀, 1 ≤ A₀ ∧ ∀ t, ((xiDerivZeros hF2 hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) -/

/-! ## 4. (EF1) The full-line identity for ξ″/ξ′  [XF′ Prop. 4.1]
Generic in the entire function f, instantiated at f = xiDeriv and at f = s(s−1).
H = WeilEF.Hfn k, H(s) = h_k((s−1/2)/i).  STATEMENT:
  (stated on the single line c = 5/4; the generic-f theorem behind it is for any c)
  theorem full_line_identity (hF2 : XiDerivZerosInStrip) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
      (hkc : HasCompactSupport k) :
      Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ) ∧
      (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k (((5/4:ℝ) : ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
          * logDeriv xiDeriv (((5/4:ℝ) : ℂ) + t * I))
        = ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ -/

/-! ## 5. (EF2) The archimedean part  [XF′ Thm 4.2 (a)]   FILE: ExplicitFormula/Archimedean.lean -/

/-! L := h′/h = Lfn s = logDeriv Γℝ s + 1/s + 1/(s−1) is DEFINED in Zeta23/XiPrime/Seam.lean,
together with logDeriv_xi_eq (ξ′/ξ = L + ζ′/ζ), xiDeriv_eq_xi_mul
(ξ′ = ξ·(L + ζ′/ζ)), Yfn := ξ′/Γℝ and its factorisation. -/

/-! STATEMENTS (Archimedean.lean):
  theorem archimedean_line {k} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
      (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
      (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
          * Lfn ((c : ℂ) + t * I))
        = Hfn k 0 + Hfn k 1 + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)
  (whence Zeta23.EF.pole_term / gamma_term give ∫ h_k (Π_X + μ) verbatim), and [XF′ Lemma 2.1]:
  theorem logDeriv_xiDeriv_eq_E {s : ℂ} (hs : 1 < s.re) (hne : xiDeriv s ≠ 0) :
      logDeriv xiDeriv s = (Lfn s + logDeriv riemannZeta s)
        + deriv (fun w => Lfn w + logDeriv riemannZeta w) s / (Lfn s + logDeriv riemannZeta s) -/

/-! ## 6. (EF3) Dirichlet series with general coefficients on the line  [XF′ Thm 4.2 (e)]
FILE: ExplicitFormula/DirichletLine.lean.  STATEMENTS:
  theorem dirichlet_line {k} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (c : ℝ)
      (a : ℕ → ℂ) (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
      Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I)) ∧
      (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I))
        = ∑' N : ℕ, a N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N)
  theorem dirichlet_line_mirror  — same with Hfn k (1 − c − tI) and k (−Real.log N). -/

/-! ## 7. (EF4) The explicit formula for ξ′ with frozen coefficients, entrywise  [XF′ Thm 4.2]
For a height-family Pf : ℝ → Params in the class FamilyHyps below (fixed λ ∈ (0,1); window
φ_T = (Pf T).phi T even, C³, supported in [−L/2, L/2], |φ| ≤ 1, ‖φ^{(j)}‖₁ ≤ C for j = 1,2,3 —
contains the taper family T ↦ P for P.Valid with P.lam < 1, and the profiled families
T ↦ P.atV v T):
  G^{(1)}_{kl} := Σ_{ρ₁} m_{ρ₁} φ̂(γ_{ρ₁} − τ_k) φ̂(γ_{ρ₁} − τ_l)  ( = Z.Gz (Pf T) T k l )
            = ∫ φ̂(τ−τ_k) φ̂(τ−τ_l) [μ + Π_X + P^{(1)}_X(τ; L⋆(τ⋆_{kl}))] dτ  ( = (Pf T).Gentry1 T k l )
              + 𝓔_{kl},      |𝓔_{kl}| ≤ C T^{−δ} · (1/max(1, (τ_k − τ_l)²) + 1/T),   some δ > 0.
STATEMENT (the Statement.XiEF shape):
  theorem xiEF (hF2 : XiDerivZerosInStrip) (Z : ZeroConfig) (hZ : Z.carrier = {ρ : ℂ | IsXiDerivZero ρ})
      (hm : ∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ) (Pf : ℝ → Params) (hPf : FamilyHyps Pf) :
      XiEF Z Pf
ROUTE (why the ζ machinery is reused wholesale): on Re s = 5/4 write ξ″/ξ′ = E + E′/E with
E := ξ′/ξ = Lfn + ζ′/ζ.  The E-part of the contour integral is literally the ζ explicit
formula (archimedean_line + WeilEF.prime_side_line twice + Zeta23.EF.literatureRHS_eq_integral_nu), so
   G^{(1)}_{kl} = G^{ζ}_{kl} + J_{kl},   J_{kl} := (1/2π)∫[H(s)+H(1−s)]·(E′/E)(s) dt,
and only E′/E = (L′+B)/(L−A) is expanded (|A/L| < 1 for |t| ≥ t₀) and frozen (L ↦ L⋆, L′ ↦ 0) into the
Dirichlet series Σ_N C_J(N; L⋆) N^{−s}, C_J := xiCoeff + Λ (the j-part of [XF′ Def 2.3];
xiCoeffJ), evaluated by dirichlet_line; G^{ζ} + ∫h_k·P_{C_J} = Gentry1 since
Defs.Pc is additive in the coefficients and Pc X (−Λ) = PX X. -/

/-- the Weil test function of the pair (k, l) at height T:  k_{kl} := f_k ⋆ f̃_l  with
f_k(u) = φ(u)e^{−iτ_k u} (Defs.Params.fk), so that h_{k_{kl}}(z) = φ̂(z−τ_k)·conj φ̂(z̄−τ_l) and
Hfn (kfun P T k l) ρ · m_ρ is the zero-side Gram summand (GramBridge).  This is the single definition
used by GramBridge.lean, TestWeight.lean and Main.lean. -/
def kfun (P : Params) (T : ℝ) (k l : ℤ) : ℝ → ℂ := Zeta23.EF.weilTest (P.fk T k) (P.fk T l)

/-- Hypotheses on a height-family of parameter sets used by the ξ′ explicit formula. -/
structure FamilyHyps (Pf : ℝ → Params) : Prop where
  lam_const : ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ ∀ T, (Pf T).lam = lam
  window : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ContDiff ℝ 3 ((Pf T).phi T) ∧
    tsupport ((Pf T).phi T) ⊆ Icc (-((Pf T).L T / 2)) ((Pf T).L T / 2) ∧
    (∀ u : ℝ, (Pf T).phi T (-u) = (Pf T).phi T u) ∧
    (∀ u : ℝ, |(Pf T).phi T u| ≤ 1) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      Integrable (iteratedDeriv j ((Pf T).phi T)) ∧
      ∫ u : ℝ, |iteratedDeriv j ((Pf T).phi T) u| ≤ C)

end XiPrime
end Zeta23
