/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/GramBridge.lean — Gram-matrix bridge lemmas for the xiEF assembly.

Bookkeeping between the Defs-level objects of the statement XiEF — Z.Gz (zero side), P.Gentry /
P.GentryC / P.Gentry1 (prime-side entries) — and the analytic objects the explicit formula produces:
tsums of H = WeilEF.Hfn over {ρ | ξ′ ρ = 0} and integrals ∫ ĥ(τ)·density(τ) dτ, for the Weil test function
of the pair (f_k, f_l),  kfun P T k l := weilTest (P.fk T k) (P.fk T l)  (the single definition, in
Zeta23/XiPrime/ExplicitFormula.lean; the family version is kfun (Pf T) T k l).
ζ model: Zeta23/Hypotheses/GzGp.lean (Gz_eq_W, EFrhs_eq_Gp, paperFT_fk, phiHat_conj, phiHat_ofReal).

  (S1) Gsummand_eq_mult_Hfn, Gz_eq_tsum_xi, summable_Gsummand_of
  (S2) literatureRHS_pairTest_eq_Gentry
  (S3) paperFT_pairTest, paperFT_pairTest_ofReal, GentryC_eq_of_nuc, Gentry1_eq
  (S4) tau_mem, tauStar_mem
Standing per-T hypotheses (as in GzGp): hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)),
hφsupp : tsupport (P.phi T) ⊆ Icc (−L/2) (L/2), hL : 0 < P.L T.
-/
import Zeta23.XiPrime.ExplicitFormula
import Zeta23.Hypotheses.GzGp
import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Complete
import Zeta23.WeilEF.VerticalLine

open scoped ComplexConjugate FourierTransform
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn)
open Zeta23.EF (weilTest)

section Pair

variable (P : Params) (T : ℝ)

/-! ### regularity of f_k and of the pair test function -/

theorem fk_continuous (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ))) (k : ℤ) :
    Continuous (P.fk T k) :=
  (GzGp.fk_contDiff P T hφC2 k).continuous

theorem fk_hasCompactSupport (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k : ℤ) :
    HasCompactSupport (P.fk T k) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (GzGp.fk_tsupport P T hφsupp k)

theorem pairTest_contDiff (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : ℤ) :
    ContDiff ℝ 2 (kfun P T k l) :=
  Zeta23.EF.weilTest_contDiff (GzGp.fk_contDiff P T hφC2 k) (fk_continuous P T hφC2 l)
    (fk_hasCompactSupport P T hφsupp k)

theorem pairTest_hasCompactSupport (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2))
    (k l : ℤ) : HasCompactSupport (kfun P T k l) :=
  Zeta23.EF.weilTest_hasCompactSupport (fk_hasCompactSupport P T hφsupp k)
    (fk_hasCompactSupport P T hφsupp l)

theorem tsupport_pairTest (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : ℤ) :
    tsupport (kfun P T k l) ⊆ Icc (-(P.L T)) (P.L T) :=
  Zeta23.EF.tsupport_weilTest_subset (GzGp.fk_tsupport P T hφsupp k) (GzGp.fk_tsupport P T hφsupp l)

/-! ### (S3a) ĥ of the pair test function -/

/-- ĥ_{f_k ⋆ f̃_l}(z) = φ̂(z − τ_k)·φ̂(z − τ_l). -/
theorem paperFT_pairTest (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : ℤ) (z : ℂ) :
    paperFT (kfun P T k l) z
      = P.phiHat T (z - P.tau T k) * P.phiHat T (z - P.tau T l) := by
  unfold kfun
  rw [Zeta23.EF.paperFT_weilTest (fk_continuous P T hφC2 k) (fk_continuous P T hφC2 l)
      (fk_hasCompactSupport P T hφsupp k) (fk_hasCompactSupport P T hφsupp l),
    GzGp.paperFT_fk, GzGp.paperFT_fk, ← GzGp.phiHat_conj]
  congr 2
  rw [map_sub, Complex.conj_conj, Complex.conj_ofReal]

/-- on the real line ĥ is the REAL number φ̂_ℝ(τ − τ_k)·φ̂_ℝ(τ − τ_l). -/
theorem paperFT_pairTest_ofReal (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : ℤ) (τ : ℝ) :
    paperFT (kfun P T k l) τ
      = ((P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) : ℝ) : ℂ) := by
  rw [paperFT_pairTest P T hφC2 hφsupp k l τ]
  have e1 : ((τ : ℂ) - (P.tau T k : ℂ)) = ((τ - P.tau T k : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((τ : ℂ) - (P.tau T l : ℂ)) = ((τ - P.tau T l : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, GzGp.phiHat_ofReal, GzGp.phiHat_ofReal]
  push_cast; ring

/-! ### (S1) zero side: Gsummand / Gz as m_ρ · H(ρ) -/

/-- Z.Gsummand P T k l ρ = m_ρ · H_{f_k ⋆ f̃_l}(ρ)   (H k s = paperFT k ((s − 1/2)/I) = ĥ(γ_ρ), rfl). -/
theorem Gsummand_eq_mult_Hfn (Z : ZeroConfig) (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : ℤ) (ρ : ℂ) :
    Z.Gsummand P T k l ρ = (Z.mult ρ : ℂ) * Hfn (kfun P T k l) ρ := by
  show Z.Gsummand P T k l ρ = (Z.mult ρ : ℂ) * paperFT (kfun P T k l) (gammaOf ρ)
  rw [paperFT_pairTest P T hφC2 hφsupp]
  unfold ZeroConfig.Gsummand
  ring

/-- the zero-side Gram entry as a tsum over the zeros of ξ′ weighted by xiDerivMult. -/
theorem Gz_eq_tsum_xi (Z : ZeroConfig) (hZ : Z.carrier = {ρ : ℂ | IsXiDerivZero ρ})
    (hm : ∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : Fin (P.d T)) :
    Z.Gz P T k l = ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ},
      (xiDerivMult (ρ : ℂ) : ℂ) * Hfn (kfun P T k l) ρ := by
  unfold ZeroConfig.Gz
  rw [← tsum_congr_set_coe
    (fun ρ => (xiDerivMult ρ : ℂ) * Hfn (kfun P T k l) ρ) hZ]
  refine tsum_congr fun ρ => ?_
  rw [Gsummand_eq_mult_Hfn P T Z hφC2 hφsupp, hm ρ ρ.2]

/-- absolute convergence of the zero-side entry, transported from the ξ′-indexed sum. -/
theorem summable_Gsummand_of (Z : ZeroConfig) (hZ : Z.carrier = {ρ : ℂ | IsXiDerivZero ρ})
    (hm : ∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k l : Fin (P.d T))
    (h : Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} =>
      (xiDerivMult (ρ : ℂ) : ℂ) * Hfn (kfun P T k l) ρ)) :
    Summable (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) := by
  rw [← hZ] at h
  refine h.congr fun ρ => ?_
  rw [Gsummand_eq_mult_Hfn P T Z hφC2 hφsupp, hm ρ ρ.2]

/-! ### (S2) prime side with ζ's coefficients: literatureRHS = Gentry -/

/-- ĥ·ν_X is integrable on ℝ for the pair test function (X = e^L = P.X T). -/
theorem integrable_paperFT_pairTest_mul_nuX (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (hL : 0 < P.L T) (k l : ℤ) :
    Integrable (fun τ : ℝ => paperFT (kfun P T k l) τ * (nuX (P.X T) τ : ℂ)) :=
  Zeta23.EF.integrable_paperFT_mul_nuX hL
    (Zeta23.EF.integrable_fourier_of_contDiff_two (pairTest_contDiff P T hφC2 hφsupp k l)
      (pairTest_hasCompactSupport P T hφsupp k l))
    (Zeta23.EF.integrable_paperFT_mul_mu (pairTest_contDiff P T hφC2 hφsupp k l)
      (pairTest_hasCompactSupport P T hφsupp k l) Zeta23.gammaFacts)

/-- **(S2)**  literatureRHS (f_k ⋆ f̃_l) = G_{kl} (= ∫ φ̂_ℝ(τ−τ_k) φ̂_ℝ(τ−τ_l) ν_X(τ) dτ, X = e^L). -/
theorem literatureRHS_pairTest_eq_Gentry (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (hL : 0 < P.L T)
    (k l : Fin (P.d T)) :
    Zeta23.EF.literatureRHS (kfun P T k l) = ((P.Gentry T k l : ℝ) : ℂ) := by
  have hkd := pairTest_contDiff P T hφC2 hφsupp (k : ℤ) (l : ℤ)
  have hkc := pairTest_hasCompactSupport P T hφsupp (k : ℤ) (l : ℤ)
  rw [Zeta23.EF.literatureRHS_eq_integral_nu hL hkd.continuous (tsupport_pairTest P T hφsupp k l)
    (Zeta23.EF.integrable_fourier_of_contDiff_two hkd hkc)
    (Zeta23.EF.integrable_paperFT_mul_mu hkd hkc Zeta23.gammaFacts)]
  rw [show ((P.Gentry T k l : ℝ) : ℂ) = P.Gp T k l from rfl, ← GzGp.EFrhs_eq_Gp]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  dsimp only [kfun]
  rw [Zeta23.EF.paperFT_weilTest (fk_continuous P T hφC2 k) (fk_continuous P T hφC2 l)
      (fk_hasCompactSupport P T hφsupp k) (fk_hasCompactSupport P T hφsupp l), Complex.conj_ofReal]

/-! ### (S3b) prime side with general coefficients: GentryC / Gentry1 versus Gentry -/

/-- If the density with coefficients c splits as ν_c(X) = ν_X + P_{cJ}(X) pointwise and ĥ·P_{cJ} is
integrable, then  M^c_{kl} = G_{kl} + ∫ ĥ(τ) P_{cJ}(X; τ) dτ  (as complex numbers). -/
theorem GentryC_eq_of_nuc (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (hL : 0 < P.L T) (k l : ℤ)
    (c cJ : ℕ → ℂ) (hnuc : ∀ τ : ℝ, nuc (P.X T) c τ = nuX (P.X T) τ + Pc (P.X T) cJ τ)
    (hint : Integrable (fun τ : ℝ =>
      paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ))) :
    ((P.GentryC T c k l : ℝ) : ℂ) = ((P.Gentry T k l : ℝ) : ℂ)
      + ∫ τ : ℝ, paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ) := by
  have hW : ∀ τ : ℝ, ((P.phiHatR T (τ - P.tau T k) : ℝ) : ℂ) * ((P.phiHatR T (τ - P.tau T l) : ℝ) : ℂ)
      = paperFT (kfun P T k l) τ := fun τ => by
    rw [← Complex.ofReal_mul, paperFT_pairTest_ofReal P T hφC2 hφsupp k l τ]
  have hnu := integrable_paperFT_pairTest_mul_nuX P T hφC2 hφsupp hL k l
  unfold Params.GentryC Params.GentryCW Params.Gentry
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have h1 : ∀ τ : ℝ,
      ((P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * nucW 1 (P.X T) c τ : ℝ) : ℂ)
        = paperFT (kfun P T k l) τ * (nuX (P.X T) τ : ℂ)
          + paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ) := by
    intro τ
    have e : nucW 1 (P.X T) c τ = nuX (P.X T) τ + Pc (P.X T) cJ τ := hnuc τ
    rw [e]; push_cast; rw [hW τ]; ring
  have h2 : ∀ τ : ℝ,
      ((P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * nuX (P.X T) τ : ℝ) : ℂ)
        = paperFT (kfun P T k l) τ * (nuX (P.X T) τ : ℂ) := by
    intro τ; push_cast; rw [hW τ]
  simp_rw [h1, h2]
  rw [integral_add hnu hint]

/-- **Gentry1 = Gentry + J-term**: the entry-dependent main term of [XF′ Thm 4.2] splits as the ζ entry
plus ∫ ĥ·P_{cJ}, given the density decomposition nuc X (xiCoeff L⋆) = nuX X + Pc X cJ. -/
theorem Gentry1_eq (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (hL : 0 < P.L T)
    (k l : Fin (P.d T)) (cJ : ℕ → ℂ)
    (hnuc : ∀ τ : ℝ, nuc (P.X T) (xiCoeff (Lstar (P.tauStar T k l))) τ
      = nuX (P.X T) τ + Pc (P.X T) cJ τ)
    (hint : Integrable (fun τ : ℝ =>
      paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ))) :
    ((P.Gentry1 T k l : ℝ) : ℂ) = ((P.Gentry T k l : ℝ) : ℂ)
      + ∫ τ : ℝ, paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ) :=
  GentryC_eq_of_nuc P T hφC2 hφsupp hL k l _ cJ hnuc hint

/-! ### (S4) the grid points lie in [T, 2T] -/

/-- T ≤ τ_k ≤ 2T for 0 ≤ k < d  (τ_k = T + k·2π/L, d = ⌊LT/2π⌋). -/
theorem tau_mem (hL : 0 < P.L T) (hT : 0 < T) (k : Fin (P.d T)) :
    T ≤ P.tau T k ∧ P.tau T k ≤ 2 * T := by
  have hh : 0 < P.hgrid T := by unfold Params.hgrid; positivity
  have hx0 : 0 ≤ P.L T * T / (2 * Real.pi) := by positivity
  have hk1 : ((k : ℕ) : ℝ) + 1 ≤ P.L T * T / (2 * Real.pi) := by
    have h : (k : ℕ) + 1 ≤ P.d T := k.2
    unfold Params.d at h
    have h' := (Nat.le_floor_iff hx0).mp h
    push_cast at h'
    exact h'
  have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  have ecast : (((k : ℕ) : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; rfl
  have hkh : ((k : ℕ) : ℝ) * P.hgrid T ≤ T := by
    have h1 : ((k : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := by linarith
    calc ((k : ℕ) : ℝ) * P.hgrid T ≤ (P.L T * T / (2 * Real.pi)) * P.hgrid T :=
          mul_le_mul_of_nonneg_right h1 hh.le
      _ = T := by
          unfold Params.hgrid
          rw [div_mul_div_comm, div_eq_iff (mul_pos (by positivity) hL).ne']
          ring
  unfold Params.tau
  rw [ecast]
  constructor
  · nlinarith [mul_nonneg hk0 hh.le]
  · linarith

/-- T ≤ τ⋆_{kl} ≤ 2T. -/
theorem tauStar_mem (hL : 0 < P.L T) (hT : 0 < T) (k l : Fin (P.d T)) :
    T ≤ P.tauStar T k l ∧ P.tauStar T k l ≤ 2 * T := by
  obtain ⟨h1, h2⟩ := tau_mem P T hL hT k
  obtain ⟨h3, h4⟩ := tau_mem P T hL hT l
  unfold Params.tauStar
  constructor <;> linarith

end Pair

end XiPrime
end Zeta23
