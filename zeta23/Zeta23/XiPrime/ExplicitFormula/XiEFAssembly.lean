/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/XiEFAssembly.lean — the (EF4) assembly [XF′ Thm 4.2].
Inputs that live in other files are taken here as explicit Prop-valued hypotheses
(GramBridgeFacts — GramBridge.lean; TestWeightFacts — TestWeight.lean; CoeffFacts —
Coeff/LSeries.lean), so that this file is complete independently of those files;
ExplicitFormula/Main.lean instantiates them.
Everything else is proved here: xiPrime_EF_lit_corr' (EF1+EF2+EF3, F2 from ZeroFree),
Jcorr_estimate (Expansion + EntryError + DirichletLine), prime_term_complex (PrimeTermJ),
FamilyHyps.perT / pow_log_absorb (FamilyFacts).
-/
import Zeta23.XiPrime.ExplicitFormula.ZeroFree
import Zeta23.XiPrime.ExplicitFormula.FullLine
import Zeta23.XiPrime.ExplicitFormula.JTerm
import Zeta23.XiPrime.ExplicitFormula.PrimeTermJ
import Zeta23.XiPrime.ExplicitFormula.FamilyFacts

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn)

/-! ## The ξ′ explicit formula, literature form with correction (hypothesis-free) -/

theorem fullLineIdentity_holds (hF2 : XiDerivZerosInStrip) : FullLineIdentity :=
  fun _ hk hkc => full_line_identity hF2 hk hkc

/-- Σ' m_{ρ₁} h_k(γ_{ρ₁}) = literatureRHS k + Jcorr k, with (F2) from ZeroFree, (EF1) and the rational
line from FullLine. -/
theorem xiPrime_EF_lit_corr' {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf ρ)
      = Zeta23.EF.literatureRHS k + Jcorr k :=
  xiPrime_EF_lit_corr xiDerivZerosInStrip_holds (fullLineIdentity_holds xiDerivZerosInStrip_holds)
    rationalLine_holds hk hkc

/-! ## The input Props -/

/-- The j-part of the coefficients: C_J(N;Λ⋆) := C(N;Λ⋆) + Λ(N) (= `xiCoeffJ`). -/
def xiCoeffJ' (Λs : ℂ) (N : ℕ) : ℂ := xiCoeff Λs N + ((Λ N : ℝ) : ℂ)

/-- The inputs (C1)+(C2) at Re s = 5/4 and (C3), in consumer shape. -/
def CoeffFacts : Prop :=
  (∃ R₀ : ℝ, 0 < R₀ ∧ ∀ Λs : ℂ, R₀ ≤ ‖Λs‖ →
      Summable (fun N : ℕ => ‖xiCoeffJ' Λs N‖ * (N : ℝ) ^ (-(5/4:ℝ))) ∧
      ∀ t : ℝ, LSeries (xiCoeffJ' Λs) (((5/4:ℝ):ℂ) + t * I) = Dfro Λs t) ∧
  (∀ (Λs : ℂ) (N : ℕ), xiCoeffJ' (conj Λs) N = conj (xiCoeffJ' Λs N))

/-- GramBridge inputs (S1, S2, S3', S4). -/
structure GramBridgeFacts : Prop where
  gz_tsum : ∀ (Z : ZeroConfig), Z.carrier = {ρ : ℂ | IsXiDerivZero ρ} →
    (∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ) →
    ∀ (P : Params) (T : ℝ), ContDiff ℝ 2 (fun u : ℝ => ((P.phi T u : ℝ) : ℂ)) →
      tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) →
      ∀ k l : Fin (P.d T),
        Z.Gz P T k l = ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * Hfn (kfun P T k l) ρ
  summable_of : ∀ (Z : ZeroConfig), Z.carrier = {ρ : ℂ | IsXiDerivZero ρ} →
    (∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ) →
    ∀ (P : Params) (T : ℝ), ContDiff ℝ 2 (fun u : ℝ => ((P.phi T u : ℝ) : ℂ)) →
      tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) →
      ∀ k l : Fin (P.d T),
        Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * Hfn (kfun P T k l) ρ) →
        Summable (fun ρ : Z.carrier => Z.Gsummand P T k l ρ)
  lit_eq_Gentry : ∀ (P : Params) (T : ℝ), ContDiff ℝ 2 (fun u : ℝ => ((P.phi T u : ℝ) : ℂ)) →
      tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) → 0 < P.L T →
      ∀ k l : Fin (P.d T), Zeta23.EF.literatureRHS (kfun P T k l) = ((P.Gentry T k l : ℝ) : ℂ)
  Gentry1_eq : ∀ (P : Params) (T : ℝ), ContDiff ℝ 2 (fun u : ℝ => ((P.phi T u : ℝ) : ℂ)) →
      tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) → 0 < P.L T →
      ∀ (k l : Fin (P.d T)) (cJ : ℕ → ℂ),
        (∀ τ : ℝ, nuc (P.X T) (xiCoeff (Lstar (P.tauStar T k l))) τ = nuX (P.X T) τ + Pc (P.X T) cJ τ) →
        Integrable (fun τ : ℝ => paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ)) →
        ((P.Gentry1 T k l : ℝ) : ℂ)
          = ((P.Gentry T k l : ℝ) : ℂ) + ∫ τ : ℝ, paperFT (kfun P T k l) τ * ((Pc (P.X T) cJ τ : ℝ) : ℂ)
  tau_mem : ∀ (P : Params) (T : ℝ), 0 < P.L T → 0 < T → ∀ k : Fin (P.d T), T ≤ P.tau T k ∧ P.tau T k ≤ 2 * T

/-- The TestWeight inputs W0–W3, in consumer (cauchyK) shape. -/
def TestWeightFacts (Pf : ℝ → Params) : Prop :=
  ∃ C T₁ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ k l : ℤ,
    ContDiff ℝ 2 (kfun (Pf T) T k l) ∧ HasCompactSupport (kfun (Pf T) T k l) ∧
    tsupport (kfun (Pf T) T k l) ⊆ Icc (-(Pf T).L T) ((Pf T).L T) ∧
    (∀ t : ℝ, ‖Hfn (kfun (Pf T) T k l) (((5/4:ℝ):ℂ) + t * I)‖
        ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2
          * (cauchyK ((Pf T).tau T k) t * cauchyK ((Pf T).tau T l) t)) ∧
    (∀ t : ℝ, (|t - (Pf T).tau T k| + |t - (Pf T).tau T l|) * ‖Hfn (kfun (Pf T) T k l) (((5/4:ℝ):ℂ) + t * I)‖
        ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T
          * (cauchyK ((Pf T).tau T k) t * cauchyK ((Pf T).tau T l) t)) ∧
    (∀ t : ℝ, ‖Hfn (kfun (Pf T) T k l) (1 - (5/4:ℝ) - t * I)‖
        ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2
          * (cauchyK (-(Pf T).tau T k) t * cauchyK (-(Pf T).tau T l) t)) ∧
    (∀ t : ℝ, (|t + (Pf T).tau T k| + |t + (Pf T).tau T l|) * ‖Hfn (kfun (Pf T) T k l) (1 - (5/4:ℝ) - t * I)‖
        ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T
          * (cauchyK (-(Pf T).tau T k) t * cauchyK (-(Pf T).tau T l) t))

/-! ## Small helpers -/

/-- a compactly supported k vanishes at ±log N for N > e^L. -/
theorem k_log_eq_zero {k : ℝ → ℂ} {L : ℝ} (hks : tsupport k ⊆ Icc (-L) L) {N : ℕ}
    (hN : Real.exp L < (N : ℝ)) : k (Real.log N) = 0 ∧ k (-Real.log N) = 0 := by
  have hN0 : (0:ℝ) < N := lt_trans (Real.exp_pos L) hN
  have hlog : L < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]; exact hN
  constructor
  · apply image_eq_zero_of_notMem_tsupport
    intro h; have := (hks h).2; linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro h; have := (hks h).1; linarith

theorem summable_coeff_mul_k {k : ℝ → ℂ} {L : ℝ} (hks : tsupport k ⊆ Icc (-L) L) (c : ℕ → ℂ) (sgn : Bool) :
    Summable (fun N : ℕ => c N / ((Real.sqrt N : ℝ) : ℂ) *
      k (if sgn then Real.log N else -Real.log N)) := by
  refine summable_of_hasFiniteSupport ((Set.finite_Iic ⌈Real.exp L⌉₊).subset ?_)
  intro N hN
  rw [Function.mem_support] at hN
  rw [Set.mem_Iic]
  by_contra h
  push Not at h
  have hN' : Real.exp L < (N : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast h)
  obtain ⟨h1, h2⟩ := k_log_eq_zero hks hN'
  apply hN
  cases sgn <;> simp [h1, h2]

theorem max_one_le_four_add (x : ℝ) : max 1 (x ^ 2) ≤ 4 + x ^ 2 := by
  rcases le_total 1 (x ^ 2) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; nlinarith

/-! ## The assembly -/

/-- **(EF4)** assembled from the preceding pieces and the three input Props. -/
theorem xiEF_of (hGB : GramBridgeFacts) (hCO : CoeffFacts)
    (Z : ZeroConfig) (hZ : Z.carrier = {ρ : ℂ | IsXiDerivZero ρ})
    (hm : ∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ)
    (Pf : ℝ → Params) (hPf : FamilyHyps Pf) (hTW : TestWeightFacts Pf) : XiEF Z Pf := by
  obtain ⟨lam, Cφ, T₁, hlam0, hlam1, hCφ0, hT₁0, hper⟩ := hPf.perT
  obtain ⟨Cw, Tw, hCw0, htw⟩ := hTW
  obtain ⟨⟨R₀, hR₀0, hco⟩, hconj⟩ := hCO
  obtain ⟨K, TJ, hK0, hTJ8, hJ⟩ := Jcorr_estimate xiDerivZerosInStrip_holds
  obtain ⟨Ca, Ta, hCa0, habs⟩ := pow_log_absorb lam hlam1 hlam0 (A := 1) zero_le_one
  set δ : ℝ := (1 - 3 * lam / 4) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; nlinarith
  set T₀ : ℝ := max (max (max T₁ Tw) (max TJ Ta)) (Real.exp (2 * (R₀ + 1))) with hT₀
  refine ⟨2 * K * Cw * Ca, δ, T₀, hδ0, fun T hT k l => ?_⟩
  -- thresholds
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTw : Tw ≤ T := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTJ : TJ ≤ T := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hT
  have hTa : Ta ≤ T := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hT
  have hTR : Real.exp (2 * (R₀ + 1)) ≤ T := le_trans (le_max_right _ _) hT
  have hT8 : 8 ≤ T := le_trans hTJ8 hTJ
  have hT0 : 0 < T := by linarith
  -- per-height facts
  obtain ⟨-, hL1, -, hX, hLlog, hX34, hφC2, hsupp, hL0, -, -, -⟩ := hper T hT₁
  obtain ⟨hkcd, hkc, hks, hw1, hw2, hw1', hw2'⟩ := htw T hTw (k : ℤ) (l : ℤ)
  set kf : ℝ → ℂ := kfun (Pf T) T k l with hkf
  set a : ℝ := (Pf T).tau T k with ha_def
  set b : ℝ := (Pf T).tau T l with hb_def
  have ha : T ≤ a := (hGB.tau_mem (Pf T) T hL0 hT0 k).1
  have hb : T ≤ b := (hGB.tau_mem (Pf T) T hL0 hT0 l).1
  have hτs : (Pf T).tauStar T k l = (a + b) / 2 := rfl
  set Λs : ℂ := Lstar ((a + b) / 2) with hΛs
  -- ‖Λ⋆‖ ≥ R₀
  have hΛR : R₀ ≤ ‖Λs‖ := by
    have h1 := norm_Lstar_ge' (τ := (a + b) / 2) (by linarith)
    have h2 : Real.log T ≤ Real.log ((a + b) / 2) := Real.log_le_log hT0 (by linarith)
    have h3 : 2 * (R₀ + 1) ≤ Real.log T := by
      have := Real.log_le_log (Real.exp_pos _) hTR
      rwa [Real.log_exp] at this
    rw [hΛs]; linarith
  have hΛR' : R₀ ≤ ‖conj Λs‖ := by rwa [Complex.norm_conj]
  -- coefficients
  set cJ : ℕ → ℂ := xiCoeffJ' Λs with hcJ
  obtain ⟨hcs, hC1⟩ := hco Λs hΛR
  obtain ⟨-, hC1c⟩ := hco (conj Λs) hΛR'
  have hcJconj : (fun N => conj (cJ N)) = xiCoeffJ' (conj Λs) := by
    funext N; rw [hcJ, hconj]
  have hC1' : ∀ t : ℝ, LSeries (fun N => conj (cJ N)) (((5/4:ℝ):ℂ) + t * I) = Dfro (conj Λs) t := by
    intro t; rw [hcJconj]; exact hC1c t
  -- weights
  set W : ℝ := Cw * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 with hW
  set W' : ℝ := Cw * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T with hW'
  have hXpos : 0 ≤ (Pf T).X T ^ (3/4 : ℝ) := Real.rpow_nonneg (by rw [hX]; exact (Real.exp_pos _).le) _
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hW'0 : 0 ≤ W' := by rw [hW']; positivity
  -- the J estimate
  have hJk := hJ hkcd hkc (T := T) (a := a) (b := b) (W := W) (W' := W') hTJ ha hb hW0 hW'0
    hw1 hw2 hw1' hw2' hcs hC1 hC1'
  -- the explicit formula in literature form with correction
  obtain ⟨hsumρ, hlit⟩ := xiPrime_EF_lit_corr' hkcd hkc
  have hgam : ∀ ρ : ℂ, paperFT kf (gammaOf ρ) = Hfn kf ρ := fun _ => rfl
  simp_rw [hgam] at hsumρ hlit
  -- zero side
  have hGz : Z.Gz (Pf T) T k l = Zeta23.EF.literatureRHS kf + Jcorr kf := by
    rw [hGB.gz_tsum Z hZ hm (Pf T) T hφC2 hsupp k l]; exact hlit
  have hlitG : Zeta23.EF.literatureRHS kf = (((Pf T).Gentry T k l : ℝ) : ℂ) := hGB.lit_eq_Gentry (Pf T) T hφC2 hsupp hL0 k l
  -- the frozen main term as a prime-side density
  have hFk := Zeta23.EF.integrable_fourier_of_contDiff_two hkcd hkc
  have hS : (∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * kf (Real.log N))
      + (∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * kf (-Real.log N))
      = ∫ τ : ℝ, paperFT kf τ * ((Pc ((Pf T).X T) cJ τ : ℝ) : ℂ) := by
    have h1 := summable_coeff_mul_k hks cJ true
    have h2 := summable_coeff_mul_k hks (fun N => conj (cJ N)) false
    simp only [ite_true] at h1
    simp only [Bool.false_eq_true, ite_false] at h2
    rw [← Summable.tsum_add h1 h2, hX, ← prime_term_complex hkcd.continuous hks hFk cJ]
    refine tsum_congr fun N => ?_
    ring
  have hnuc : ∀ τ : ℝ, nuc ((Pf T).X T) (xiCoeff (Lstar ((Pf T).tauStar T k l))) τ = nuX ((Pf T).X T) τ + Pc ((Pf T).X T) cJ τ := by
    intro τ; rw [hτs, nuc_xiCoeff_eq']; rfl
  have hintPc : Integrable (fun τ : ℝ => paperFT kf τ * ((Pc ((Pf T).X T) cJ τ : ℝ) : ℂ)) := by
    rw [hX]; exact integrable_paperFT_mul_Pc ((Pf T).L T) hFk cJ
  have hG1 := hGB.Gentry1_eq (Pf T) T hφC2 hsupp hL0 k l cJ hnuc hintPc
  -- the entry error equals the J error
  have hdiff : Z.Gz (Pf T) T k l - (((Pf T).Gentry1 T k l : ℝ) : ℂ)
      = Jcorr kf - ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * kf (Real.log N))
          + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * kf (-Real.log N)) := by
    rw [hGz, hlitG, hG1, hS]; ring
  refine ⟨hGB.summable_of Z hZ hm (Pf T) T hφC2 hsupp k l hsumρ, ?_⟩
  rw [hdiff]
  refine hJk.trans ?_
  -- the numeric absorption
  obtain ⟨hab1, hab2⟩ := habs T hTa
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hXL : (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 ≤ T ^ (3 * lam / 4) * Real.log T ^ 2 := by
    refine mul_le_mul hX34 ?_ (by positivity) (Real.rpow_nonneg hT0.le _)
    exact pow_le_pow_left₀ hL0.le hLlog 2
  have hWW : W + W' ≤ 2 * Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2) := by
    have hLL : (Pf T).L T ≤ (Pf T).L T ^ 2 := by nlinarith [hL1]
    have e : W + W' = Cw * (Pf T).X T ^ (3/4 : ℝ) * ((Pf T).L T ^ 2 + (Pf T).L T) := by
      rw [hW, hW']; ring
    rw [e]
    calc Cw * (Pf T).X T ^ (3/4 : ℝ) * ((Pf T).L T ^ 2 + (Pf T).L T)
        ≤ Cw * (Pf T).X T ^ (3/4 : ℝ) * (2 * (Pf T).L T ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCw0 hXpos)
      _ = 2 * Cw * ((Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2) := by ring
      _ ≤ 2 * Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2) :=
          mul_le_mul_of_nonneg_left hXL (by positivity)
  have hΔ : 0 < 4 + (a - b) ^ 2 := by positivity
  have hmax : 0 < max 1 ((a - b) ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : (W + W') / (T * Real.log T) / (4 + (a - b) ^ 2)
      ≤ 2 * Cw * Ca * T ^ (-δ) * (1 / max 1 ((a - b) ^ 2)) := by
    have e1 : (W + W') / (T * Real.log T) ≤ 2 * Cw * Ca * T ^ (-δ) := by
      calc (W + W') / (T * Real.log T)
          ≤ 2 * Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2) / (T * Real.log T) :=
            div_le_div_of_nonneg_right hWW (by positivity)
        _ = 2 * Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2 * 1 / (T * Real.log T)) := by ring
        _ ≤ 2 * Cw * (Ca * T ^ (-((1 - 3 * lam / 4) / 2))) := mul_le_mul_of_nonneg_left hab1 (by positivity)
        _ = 2 * Cw * Ca * T ^ (-δ) := by rw [hδ]; ring
    have e2 : 1 / (4 + (a - b) ^ 2) ≤ 1 / max 1 ((a - b) ^ 2) :=
      div_le_div_of_nonneg_left zero_le_one hmax (max_one_le_four_add _)
    calc (W + W') / (T * Real.log T) / (4 + (a - b) ^ 2)
        = (W + W') / (T * Real.log T) * (1 / (4 + (a - b) ^ 2)) := by ring
      _ ≤ 2 * Cw * Ca * T ^ (-δ) * (1 / max 1 ((a - b) ^ 2)) :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
  have h2 : W / T ^ 2 ≤ Cw * Ca * T ^ (-δ) * (1 / T) := by
    have hWle : W ≤ Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2) := by
      rw [hW, show Cw * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2
        = Cw * ((Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hXL hCw0
    calc W / T ^ 2 ≤ Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2) / T ^ 2 :=
          div_le_div_of_nonneg_right hWle (by positivity)
      _ = Cw * (T ^ (3 * lam / 4) * Real.log T ^ 2 * 1 / T ^ 2) := by ring
      _ ≤ Cw * (Ca * T ^ (-((1 - 3 * lam / 4) / 2)) / T) := mul_le_mul_of_nonneg_left hab2 hCw0
      _ = Cw * Ca * T ^ (-δ) * (1 / T) := by rw [hδ]; ring
  have hTδ : 0 ≤ T ^ (-δ) := Real.rpow_nonneg hT0.le _
  calc K * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2)
      ≤ K * (2 * Cw * Ca * T ^ (-δ) * (1 / max 1 ((a - b) ^ 2)) + Cw * Ca * T ^ (-δ) * (1 / T)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK0
    _ ≤ 2 * K * Cw * Ca * T ^ (-δ) * (1 / max 1 ((a - b) ^ 2) + 1 / T) := by
        have hnn : 0 ≤ K * Cw * Ca * T ^ (-δ) * (1 / T) := by positivity
        have e : 2 * K * Cw * Ca * T ^ (-δ) * (1 / max 1 ((a - b) ^ 2) + 1 / T)
            = K * (2 * Cw * Ca * T ^ (-δ) * (1 / max 1 ((a - b) ^ 2)) + Cw * Ca * T ^ (-δ) * (1 / T))
              + K * Cw * Ca * T ^ (-δ) * (1 / T) := by ring
        rw [e]; linarith

end XiPrime
end Zeta23
