/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses/GzGp.lean — the H-EF bridge between the two expressions of [eq:Gdef]:  Z.Gz P T (zero side, Σ_ρ m_ρ φ̂(γ_ρ−τ_k)φ̂(γ_ρ−τ_l))
                  = P.Gp T  (prime side, ∫ φ̂(τ−τ_k)φ̂(τ−τ_l)ν_X(τ)dτ),
"the two expressions agreeing by Proposition [prop:EF]" — here: by hypothesis H-EF applied to
f = f_k, g = f_l, using h_{f_k}(z) = φ̂(z − τ_k) and "since φ̂ is real on ℝ we have
conj φ̂(conj z) = φ̂(z)" ([subsec:family] after [eq:fk]).
What this does and does not test: it checks the paper's internal consistency between [eq:Wdef],
[eq:fk], [eq:Gdef] and the form of [eq:EF] (conjugations, shifts, realness, support, X = e^L);
it does not test the 2π/sign normalisation inside ν_X, because [eq:EF] enters as the hypothesis
H-EF in the paper's own form — that normalisation is tested in Zeta23/ExplicitFormula.lean
(literature form ⇒ ExplicitFormulaPaper).
Taper regularity (φ ∈ C², supp φ ⊆ [−L/2, L/2]; Zeta23/Taper.lean) enters as
hypotheses. Helper lemmas are namespaced Zeta23.GzGp to avoid clashing with Zeta23/Taper.lean's
Params.phiHat_conj / Params.phiHat_ofReal (same statements; proved here independently so
this file depends only on Zeta23.Hypotheses).
-/
import Zeta23.Hypotheses
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped ComplexConjugate
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

namespace GzGp

variable (P : Params) (T : ℝ)

lemma integral_comp_neg_real (g : ℝ → ℂ) : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, g x := by
  have h := Measure.integral_comp_mul_left g (-1)
  simp only [neg_mul, one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  exact h

/-- φ is even: φ(−u) = φ(u)  ([subsec:family]: "φ ∈ C_c³(ℝ) is even"). -/
lemma phi_neg (u : ℝ) : P.phi T (-u) = P.phi T u := by simp [Params.phi, abs_neg]

/-- h_{f_k}(z) = φ̂(z − τ_k)  ([subsec:family] after [eq:fk]). -/
lemma paperFT_fk (k : ℤ) (z : ℂ) : paperFT (P.fk T k) z = P.phiHat T (z - P.tau T k) := by
  unfold paperFT Params.phiHat Params.fk paperFT
  congr 1
  ext u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- "since φ̂ is real on ℝ we have conj φ̂(conj z) = φ̂(z)", in the form φ̂(conj z) = conj φ̂(z);
uses only that φ is real-valued and even. -/
lemma phiHat_conj (z : ℂ) : P.phiHat T (conj z) = conj (P.phiHat T z) := by
  show (∫ u : ℝ, (P.phi T u : ℂ) * cexp (I * conj z * (u : ℂ)))
      = conj (∫ u : ℝ, (P.phi T u : ℂ) * cexp (I * z * (u : ℂ)))
  calc (∫ u : ℝ, (P.phi T u : ℂ) * cexp (I * conj z * (u : ℂ)))
      = ∫ u : ℝ, (fun v : ℝ => conj ((P.phi T v : ℂ) * cexp (I * z * (v : ℂ)))) (-u) := by
        congr 1
        ext u
        simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
          phi_neg, Complex.ofReal_neg, map_neg]
        congr 2
        ring
    _ = ∫ v : ℝ, conj ((P.phi T v : ℂ) * cexp (I * z * (v : ℂ))) :=
        integral_comp_neg_real (fun v : ℝ => conj ((P.phi T v : ℂ) * cexp (I * z * (v : ℂ))))
    _ = conj (∫ v : ℝ, (P.phi T v : ℂ) * cexp (I * z * (v : ℂ))) := integral_conj

/-- φ̂ is real on the real axis: φ̂(r) = φ̂_ℝ(r). -/
lemma phiHat_ofReal (r : ℝ) : P.phiHat T r = (P.phiHatR T r : ℂ) := by
  have h := phiHat_conj P T (r : ℂ)
  rw [Complex.conj_ofReal] at h
  have him : (P.phiHat T r).im = 0 := Complex.conj_eq_iff_im.mp h.symm
  apply Complex.ext
  · simp [Params.phiHatR]
  · simp [Params.phiHatR, him]

/-- f_k ∈ C² given φ ∈ C² (as a ℂ-valued function). -/
lemma fk_contDiff (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ))) (k : ℤ) :
    ContDiff ℝ 2 (P.fk T k) := by
  unfold Params.fk
  apply hφC2.mul
  apply Complex.contDiff_exp.comp
  apply ContDiff.neg
  apply ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff

/-- supp f_k ⊆ supp φ ⊆ [−L/2, L/2]. -/
lemma fk_tsupport (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k : ℤ) :
    tsupport (P.fk T k) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) := by
  refine (tsupport_mul_subset_left).trans (subset_trans (le_of_eq ?_) hφsupp)
  show tsupport (Complex.ofReal ∘ P.phi T) = tsupport (P.phi T)
  simp only [tsupport, Function.support_comp_eq Complex.ofReal (by simp) (P.phi T)]

/-- Zero side: G_{kl} [eq:Gdef, 1st expr] is literally W(f_k, f_l) [eq:Wdef]. No hypotheses. -/
lemma Gz_eq_W (Z : ZeroConfig) (k l : Fin (P.d T)) :
    Z.Gz P T k l = Z.W (P.fk T k) (P.fk T l) := by
  unfold ZeroConfig.Gz ZeroConfig.W ZeroConfig.Gsummand ZeroConfig.Wsummand
  congr 1
  ext ρ
  rw [paperFT_fk, paperFT_fk, ← Complex.conj_ofReal (P.tau T l), ← map_sub,
    phiHat_conj, Complex.conj_conj, Complex.conj_ofReal]

/-- Prime side: the [eq:EF] right-hand side at (f_k, f_l) is literally G_{kl} [eq:Gdef, 2nd expr].
No hypotheses. -/
lemma EFrhs_eq_Gp (k l : Fin (P.d T)) :
    (∫ τ : ℝ, paperFT (P.fk T k) τ * conj (paperFT (P.fk T l) τ) *
      (nuX (Real.exp (P.L T)) τ : ℂ)) = P.Gp T k l := by
  unfold Params.Gp Params.Gentry Params.X
  rw [← integral_complex_ofReal]
  congr 1
  ext τ
  rw [paperFT_fk, paperFT_fk, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
    phiHat_ofReal, phiHat_ofReal, Complex.conj_ofReal]
  push_cast
  ring

end GzGp

/-- **The H-EF bridge** [eq:Gdef]: the zero-side and prime-side matrices agree, given H-EF, L > 0,
φ ∈ C² and supp φ ⊆ [−L/2, L/2] (the last two are taper facts, Zeta23/Taper.lean). -/
theorem ZeroConfig.Gz_eq_Gp (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hEF : ExplicitFormulaPaper Z) (hL : 0 < P.L T)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) :
    Z.Gz P T = P.Gp T := by
  ext k l
  obtain ⟨-, -, hW⟩ := hEF (P.L T) hL (P.fk T k) (P.fk T l) (GzGp.fk_contDiff P T hφC2 k)
    (GzGp.fk_contDiff P T hφC2 l) (GzGp.fk_tsupport P T hφsupp k) (GzGp.fk_tsupport P T hφsupp l)
  rw [GzGp.Gz_eq_W, hW, GzGp.EFrhs_eq_Gp]

/-- Also: under H-EF the zero-side entries are (absolutely) summable — needed to write E = G − A as
the sum over zeros with γ ∉ I' . -/
theorem ZeroConfig.summable_Gsummand (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hEF : ExplicitFormulaPaper Z) (hL : 0 < P.L T)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : Fin (P.d T)) :
    Summable (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) := by
  obtain ⟨hS, -, -⟩ := hEF (P.L T) hL (P.fk T k) (P.fk T l) (GzGp.fk_contDiff P T hφC2 k)
    (GzGp.fk_contDiff P T hφC2 l) (GzGp.fk_tsupport P T hφsupp k) (GzGp.fk_tsupport P T hφsupp l)
  refine hS.congr fun ρ => ?_
  unfold ZeroConfig.Gsummand ZeroConfig.Wsummand
  rw [GzGp.paperFT_fk, GzGp.paperFT_fk, ← Complex.conj_ofReal (P.tau T l), ← map_sub,
    GzGp.phiHat_conj, Complex.conj_conj, Complex.conj_ofReal]

end Zeta23
