/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (§5, §5.3 of the paper), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

TARGET (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)))

PAPER (§5.3, verbatim): "For T ≥ T₀,  tr G̃² = 𝓜 + O(L l log l (l² + X)),
  𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'."

ROUTE (paper's, §5.3, with two simplifications that only change absolute constants):
* [eq:trG2int]  L² tr G̃² = Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν(τ)ν(τ') dτdτ',
  K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k)φ̂(τ'−τ_k) [eq:Kdef]  — here a product of two integrals and a
  FINITE sum, so no Fubini beyond ∫(f)·∫(g) = ∬ f⊗g.
* K_∞ := Σ_{k∈ℤ} φ̂(τ−τ_k)φ̂(τ'−τ_k) = L Φ(τ−τ') by [lem:poisson] (LocalHyps.poisson), so
  ∬_{I×I} K_∞² νν' = L² 𝓜, and  L²(tr G̃² − 𝓜)·L² … precisely:
  Σ G² − L²𝓜·… = 𝓔₁ + 𝓔₂,  𝓔₁ := ∬_{I×I}(K² − K_∞²)νν',  𝓔₂ := ∬_{ℝ²∖I×I} K²νν'.
* [eq:Kbounds]  |K|, |K_∞| ≤ L² (paper: aL²; a ≤ 1);  |K_out| = |K_∞ − K| handled by the
  weighted AM–GM  |Σ_{k∉[0,d)} a_k b_k| ≤ ½(s ρ(τ) + ρ(τ')/s), ρ(τ) := Σ_{k∉[0,d)} φ̂(τ−τ_k)²
  = aL² − Σ_{k<d} φ̂(τ−τ_k)² (Poisson diagonal — a FINITE expression), with s := g(τ')/g(τ),
  g := (1 + dist(·,∂I))⁻².  This replaces the paper's (∫_I ψ_k)²-sum (§5.3) and gives
  |𝓔₁| ≤ 2L²B²(∫_I ρ/g)(∫_I g) ≪ L²B²·L·l ≤ L³B² l log l  — within the lemma's error (the paper
  gets L³B² log L here; the slack l is free since 𝓔₂ is the dominant term anyway).
* 𝓔₂ exactly as the paper (§5.3): |𝓔₂| ≤ 2L² Σ_{k<d}(∫_{I^c}ψ_k|ν|)(∫_ℝ ψ_k|ν|),
  second factor ≤ 3Ψ₀B, Σ_k first factor = ∫_{I^c}|ν|σ ≪ BLl via the grid bound
  σ(τ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ψ, σ ≤ d ψ(Δ); for the far range we use log⁺x ≤ 2√x instead of
  integrating logarithms (constants only).
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X: Zeta23/PiFacts.lean
  (from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

FILE LAYOUT:
  EndsCore.lean (this file) — defs, continuity/integrability, [eq:trG2int],
     decomposition, ψ toolkit, [eq:Kbounds] pointwise;
  EndsE1.lean — calE1_bound;   EndsE2.lean (1-D estimates N1/N2 in EndsNu.lean,
     weights in EndsWeighted.lean) — calE2_bound;
  Ends.lean — assembly lem_ends' / lem_ends (proved from the two bounds).
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PiFacts

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-! The ψ majorant `psiA cϱ p r = min(L, 2/|r|, c_ϱ/(w r²))` [eq:psidef] and the [eq:psiints]
facts (psi_integrable, psi_sq_integrable, integral_psi_Ioi_le, integral_psi_sq_le, phiHat_le_psi,
Phi_le_psi) are in Zeta23/PrimeSideA (`LocalHyps`). -/

/-- [eq:Bdef] pointwise bound on ν_X (Zeta23/PiFacts.lean `nuX_abs_le`):
"`|ν_X(τ)| ≤ B + log⁺(|τ|/4T)` (τ ∈ ℝ), `|ν_X(τ)| ≤ B` (|τ| ≤ 4T), `B := l + 4√X`" for T ≥ T₀. -/
def NuBound (p : Setting) (B : ℝ) (ν : ℝ → ℝ) : Prop :=
  ∀ τ : ℝ, |ν τ| ≤ B + max (Real.log (|τ| / (4 * p.T))) 0

/-- `B := l + 4√X` [eq:Bdef]. -/
def Bconst (p : Setting) : ℝ := p.l + 4 * Real.sqrt p.X

variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)

/-! ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for a free
`B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p` (bridges by `rfl`). -/

/-- `G_{kl}` for an abstract density ν (`GentryA p F k l = GentryNu (Zeta23.nuX p.X) p F k l`, rfl). -/
def GentryNu (ν : ℝ → ℝ) (p : Setting) (F : LocalFun) (k l : ℤ) : ℝ :=
  ∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * ν τ

/-- `𝓜` for an abstract density (`MtotalA p F = MtotalNu (Zeta23.nuX p.X) p F`, rfl). -/
def MtotalNu (ν : ℝ → ℝ) (p : Setting) (F : LocalFun) : ℝ := Mform F.Phi p.T ν ν

theorem GentryA_eq_GentryNu (p : Setting) (F : LocalFun) (k l : ℤ) :
    GentryA p F k l = GentryNu (Zeta23.nuX p.X) p F k l := rfl

theorem MtotalA_eq_MtotalNu (p : Setting) (F : LocalFun) :
    MtotalA p F = MtotalNu (Zeta23.nuX p.X) p F := rfl

/-! ## [eq:Kdef] -/

/-- `K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k) φ̂(τ'−τ_k)` [eq:Kdef]. -/
def Kfun (τ τ' : ℝ) : ℝ := ∑ k : Fin p.d, F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k)

/-- `K_∞(τ,τ') = L Φ(τ−τ')` (the value of `Σ_{k∈ℤ}`, [lem:poisson]). -/
def Kinf (τ τ' : ℝ) : ℝ := p.L * F.Phi (τ - τ')

/-- `ρ(τ) := aL² − Σ_{k<d} φ̂(τ−τ_k)²`  (`= Σ_{k∉[0,d)} φ̂(τ−τ_k)²` by the Poisson diagonal). -/
def rho (τ : ℝ) : ℝ := F.a * p.L ^ 2 - ∑ k : Fin p.d, F.phiHat (τ - p.tau k) ^ 2

/-! All double integrals below are integrals over `ℝ × ℝ` w.r.t. `volume` (= `volume.prod
volume`), restricted to `I ×ˢ I` or its complement where indicated — the same spelling as
`Mform` in Zeta23/PrimeSideA/Defs.lean. -/

/-- the square `I × I`, `I = [T,2T]`. -/
def sqI : Set (ℝ × ℝ) := p.I ×ˢ p.I

/-- the integrand of [eq:trG2int]: `K(τ,τ')² ν(τ) ν(τ')`. -/
def trG2integrand (q : ℝ × ℝ) : ℝ := Kfun p F q.1 q.2 ^ 2 * ν q.1 * ν q.2

/-- the integrand `K_∞(τ,τ')² ν(τ) ν(τ')` (`= L² Φ(τ−τ')² νν'`). -/
def KinfIntegrand (q : ℝ × ℝ) : ℝ := Kinf p F q.1 q.2 ^ 2 * ν q.1 * ν q.2

/-- `𝓔₁ := ∬_{I×I} (K² − K_∞²) ν ν'` (§5.3). -/
def calE1 : ℝ := ∫ q in sqI p, (trG2integrand p F ν q - KinfIntegrand p F ν q)

/-- `𝓔₂ := ∬_{(I×I)ᶜ} K² ν ν'` (§5.3). -/
def calE2 : ℝ := ∫ q in (sqI p)ᶜ, trG2integrand p F ν q

variable {p F ν}

section Structure
variable {B : ℝ}
/-! ## [eq:trG2int] and the decomposition -/

/-- ν_X is continuous (μ smooth by H-Γ, Π_X by hypothesis, P_X a trigonometric polynomial). -/
theorem nuX_continuous (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCoreW cϱ p F) :
    Continuous (Zeta23.nuX p.X) := by
  have h1 : Continuous Zeta23.mu := hΓ.smooth.continuous
  have h2 := hF.PiX_cont
  have h3 := PX_continuous p.X
  unfold Zeta23.nuX
  fun_prop

theorem Kfun_continuous (hF : LocalHypsCoreW cϱ p F) :
    Continuous (fun q : ℝ × ℝ => Kfun p F q.1 q.2) := by
  have := hF.phiHat_cont
  unfold Kfun
  fun_prop

theorem trG2integrand_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) :
    Continuous (trG2integrand p F ν) := by
  have h1 := hνc
  have h2 := Kfun_continuous hF
  unfold trG2integrand
  fun_prop

theorem KinfIntegrand_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) :
    Continuous (KinfIntegrand p F ν) := by
  have h1 := hνc
  have h2 : Continuous F.Phi := hF.Phi_contDiff.continuous
  unfold KinfIntegrand Kinf
  fun_prop

theorem isCompact_sqI : IsCompact (sqI p) := isCompact_Icc.prod isCompact_Icc

theorem measurableSet_sqI : MeasurableSet (sqI p) := measurableSet_Icc.prod measurableSet_Icc

/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/

/-- `|φ̂(r)|(1 + r²) ≤ L + c_ϱ/w` (from [eq:psidef]). -/
theorem abs_phiHat_mul_one_add_sq_le (hF : LocalHypsCoreW cϱ p F) (r : ℝ) :
    |F.phiHat r| * (1 + r ^ 2) ≤ p.L + cϱ / p.w := by
  have h1 := hF.phiHat_le_L r
  have h2 := hF.phiHat_le_sq r
  nlinarith [abs_nonneg (F.phiHat r)]

theorem abs_phiHat_le_div (hF : LocalHypsCoreW cϱ p F) (r : ℝ) :
    |F.phiHat r| ≤ (p.L + cϱ / p.w) / (1 + r ^ 2) := by
  rw [le_div_iff₀ (by positivity)]; exact abs_phiHat_mul_one_add_sq_le hF r

/-- shift inequality `1 + τ² ≤ 2(1 + a²)(1 + (τ − a)²)`. -/
theorem one_add_sq_le_shift (τ a : ℝ) : 1 + τ ^ 2 ≤ 2 * (1 + a ^ 2) * (1 + (τ - a) ^ 2) := by
  nlinarith [sq_nonneg (τ - 2 * a), sq_nonneg (a * (τ - a)), sq_nonneg a, sq_nonneg (τ - a)]

/-- `|φ̂(τ − a)| ≤ 2(L + c/w)(1 + a²)/(1 + τ²)`. -/
theorem abs_phiHat_shift_le (hF : LocalHypsCoreW cϱ p F) (τ a : ℝ) :
    |F.phiHat (τ - a)| ≤ 2 * (p.L + cϱ / p.w) * (1 + a ^ 2) / (1 + τ ^ 2) := by
  have hM : 0 ≤ p.L + cϱ / p.w := by
    have := abs_phiHat_mul_one_add_sq_le hF 0; nlinarith [abs_nonneg (F.phiHat 0)]
  have h1 := abs_phiHat_le_div hF (τ - a)
  have h2 := one_add_sq_le_shift τ a
  calc |F.phiHat (τ - a)| ≤ (p.L + cϱ / p.w) / (1 + (τ - a) ^ 2) := h1
    _ = (p.L + cϱ / p.w) * (1 / (1 + (τ - a) ^ 2)) := by ring
    _ ≤ (p.L + cϱ / p.w) * (2 * (1 + a ^ 2) / (1 + τ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
    _ = _ := by ring

/-- `log⁺ x ≤ x` for `x ≥ 0`. -/
theorem max_log_zero_le {x : ℝ} (hx : 0 ≤ x) : max (Real.log x) 0 ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; simp
  · exact max_le (by linarith [Real.log_le_sub_one_of_pos h]) hx

theorem Bconst_nonneg (hl : 0 ≤ p.l) : 0 ≤ Bconst p := by unfold Bconst; positivity

/-- crude global form of [eq:Bdef]: `|ν_X(τ)| ≤ B + |τ|` (for `T ≥ 1/4`). -/
theorem abs_nuX_le_linear (hν : NuBound p B ν) (hT : 1 ≤ p.T) (τ : ℝ) :
    |ν τ| ≤ B + |τ| := by
  have h := hν τ
  have h2 : max (Real.log (|τ| / (4 * p.T))) 0 ≤ |τ| / (4 * p.T) := max_log_zero_le (by positivity)
  have h3 : |τ| / (4 * p.T) ≤ |τ| := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg τ]
  linarith

/-- the one-variable pieces `g_{kl}(τ) := φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ)` of `G_{kl} = ∫ g_{kl}`. -/
def gkl (p : Setting) (F : LocalFun) (ν : ℝ → ℝ) (k l : ℤ) (τ : ℝ) : ℝ :=
  F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * ν τ

theorem gkl_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (k l : ℤ) :
    Continuous (gkl p F ν k l) := by
  have h1 := hνc
  have h2 := hF.phiHat_cont
  unfold gkl
  fun_prop

/-- domination `|g_{kl}(τ)| ≤ C_{kl} (1 + τ²)⁻¹`. -/
theorem abs_gkl_le (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 1 ≤ p.T) (hB : 0 ≤ B)
    (k l : ℤ) (τ : ℝ) :
    |gkl p F ν k l τ| ≤ (4 * (p.L + cϱ / p.w) ^ 2 * (1 + p.tau k ^ 2) * (1 + p.tau l ^ 2)
      * (B + 1)) * (1 + τ ^ 2)⁻¹ := by
  have hM : 0 ≤ p.L + cϱ / p.w := by
    have := abs_phiHat_mul_one_add_sq_le hF 0; nlinarith [abs_nonneg (F.phiHat 0)]
  have ha := abs_phiHat_shift_le hF τ (p.tau k)
  have hb := abs_phiHat_shift_le hF τ (p.tau l)
  have hn := abs_nuX_le_linear hν hT τ
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  -- (B + |τ|) ≤ (B + 1)(1 + τ²)
  have hlin : B + |τ| ≤ (B + 1) * (1 + τ ^ 2) := by
    have : |τ| ≤ 1 + τ ^ 2 := by
      rcases le_or_gt |τ| 1 with h | h
      · nlinarith [sq_nonneg τ]
      · have : |τ| ≤ |τ| ^ 2 := by nlinarith
        rw [sq_abs] at this; linarith
    nlinarith
  unfold gkl
  rw [abs_mul, abs_mul]
  have hn' : |ν τ| ≤ (B + 1) * (1 + τ ^ 2) := le_trans hn hlin
  calc |F.phiHat (τ - p.tau k)| * |F.phiHat (τ - p.tau l)| * |ν τ|
      ≤ (2 * (p.L + cϱ / p.w) * (1 + p.tau k ^ 2) / (1 + τ ^ 2))
        * (2 * (p.L + cϱ / p.w) * (1 + p.tau l ^ 2) / (1 + τ ^ 2))
        * ((B + 1) * (1 + τ ^ 2)) := by
        apply mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by positivity)) hn' (abs_nonneg _)
          (by positivity)
    _ = _ := by field_simp; ring

theorem gkl_integrable (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hT : 1 ≤ p.T) (hB : 0 ≤ B) (k l : ℤ) : Integrable (gkl p F ν k l) := by
  set C : ℝ := 4 * (p.L + cϱ / p.w) ^ 2 * (1 + p.tau k ^ 2) * (1 + p.tau l ^ 2) * (B + 1)
  refine Integrable.mono' (g := fun τ : ℝ => C * (1 + τ ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul C)
    (gkl_continuous hνc hF k l).aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_gkl_le hF hν hT hB k l τ

/-- `G_{kl} = ∫ g_{kl}`. -/
theorem GentryNu_eq (k l : ℤ) : GentryNu ν p F k l = ∫ τ, gkl p F ν k l τ := rfl

/-- pointwise: `Σ_{k,l<d} g_{kl}(τ) g_{kl}(τ') = K(τ,τ')² ν(τ)ν(τ')`. -/
theorem sum_gkl_mul_gkl (q : ℝ × ℝ) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, gkl p F ν k l q.1 * gkl p F ν k l q.2 = trG2integrand p F ν q := by
  unfold trG2integrand Kfun gkl
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The heart of "the interchange being justified by absolute convergence" (§5.3):
`K(τ,τ')² ν(τ)ν(τ')` is integrable on `ℝ²`. -/
theorem trG2integrand_integrable (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    Integrable (trG2integrand p F ν) := by
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have h : Integrable (fun q : ℝ × ℝ => ∑ k : Fin p.d, ∑ l : Fin p.d,
      gkl p F ν k l q.1 * gkl p F ν k l q.2) := by
    refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
    exact (gkl_integrable hνc hF hν hT1 hB k l).mul_prod (gkl_integrable hνc hF hν hT1 hB k l)
  exact h.congr (Filter.Eventually.of_forall fun q => sum_gkl_mul_gkl q)

/-- **[eq:trG2int]** (§5.3): `Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν_X(τ)ν_X(τ') dτdτ'`
("the interchange being justified by absolute convergence"). -/
theorem eq_trG2int (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 = ∫ q, trG2integrand p F ν q := by
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hsq : ∀ k l : Fin p.d, GentryNu ν p F k l ^ 2
      = ∫ q : ℝ × ℝ, gkl p F ν k l q.1 * gkl p F ν k l q.2 := by
    intro k l
    rw [sq, GentryNu_eq, ← integral_prod_mul]
    rfl
  have hI : ∀ k l : Fin p.d, Integrable (fun q : ℝ × ℝ => gkl p F ν k l q.1 * gkl p F ν k l q.2) :=
    fun k l => (gkl_integrable hνc hF hν hT1 hB k l).mul_prod (gkl_integrable hνc hF hν hT1 hB k l)
  have hinner : ∀ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2
      = ∫ q : ℝ × ℝ, ∑ l : Fin p.d, gkl p F ν k l q.1 * gkl p F ν k l q.2 := by
    intro k
    rw [integral_finsetSum _ (fun l _ => hI k l)]
    exact Finset.sum_congr rfl fun l _ => hsq k l
  rw [Finset.sum_congr rfl fun k _ => hinner k,
    ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hI k l)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q => sum_gkl_mul_gkl q)

/-- `∬_{I×I} K_∞² νν' = L² 𝓜` (§5.3 "note …"). -/
theorem integral_Kinf_sq : ∫ q in sqI p, KinfIntegrand p F ν q = p.L ^ 2 * MtotalNu ν p F := by
  unfold MtotalNu Mform KinfIntegrand Kinf sqI
  rw [← integral_const_mul]
  congr 1 with q
  ring

/-- The decomposition  `Σ_{k,l<d} G_{kl}² − L²𝓜 = 𝓔₁ + 𝓔₂`. -/
theorem decomp (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - p.L ^ 2 * MtotalNu ν p F
      = calE1 p F ν + calE2 p F ν := by
  have hint := trG2integrand_integrable hνc hF hν hB hT
  have h1 : IntegrableOn (trG2integrand p F ν) (sqI p) := hint.integrableOn
  have h2 : IntegrableOn (KinfIntegrand p F ν) (sqI p) :=
    (KinfIntegrand_continuous hνc hF).continuousOn.integrableOn_compact (isCompact_sqI (p := p))
  rw [eq_trG2int hνc hF hν hB hT, ← integral_Kinf_sq, calE1, calE2, integral_sub h1 h2,
    ← integral_add_compl (measurableSet_sqI (p := p)) hint]
  ring

end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem psiA_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    psiA cϱ p r = min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2))) := by
  simp [psiA, hr]

theorem psiA_zero : psiA cϱ p 0 = p.L := by simp [psiA]

theorem psiA_le_L (r : ℝ) : psiA cϱ p r ≤ p.L := by
  by_cases hr : r = 0
  · simp [psiA, hr]
  · rw [psiA_of_ne_zero hr]; exact min_le_left _ _

theorem psiA_le_div_sq {r : ℝ} (hr : r ≠ 0) : psiA cϱ p r ≤ cϱ / (p.w * r ^ 2) := by
  rw [psiA_of_ne_zero hr]; exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem psiA_le_div_abs {r : ℝ} (hr : r ≠ 0) : psiA cϱ p r ≤ 2 / |r| := by
  rw [psiA_of_ne_zero hr]; exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem psiA_even (r : ℝ) : psiA cϱ p (-r) = psiA cϱ p r := by
  simp [psiA]

theorem psiA_nonneg (hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w) (r : ℝ) : 0 ≤ psiA cϱ p r := by
  by_cases hr : r = 0
  · simp [psiA, hr, hL]
  · rw [psiA_of_ne_zero hr]
    refine le_min hL (le_min (by positivity) (by positivity))


theorem psiA_abs (r : ℝ) : psiA cϱ p |r| = psiA cϱ p r := by
  rcases le_or_gt 0 r with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, psiA_even]

/-- ψ is antitone on [0, ∞). -/
theorem psiA_antitoneOn (_hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w) :
    AntitoneOn (psiA cϱ p) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rcases eq_or_lt_of_le ha with rfl | ha'
  · rw [psiA_zero]; exact psiA_le_L b
  · have hb' : 0 < b := lt_of_lt_of_le ha' hab
    rw [psiA_of_ne_zero ha'.ne', psiA_of_ne_zero hb'.ne', abs_of_pos ha', abs_of_pos hb']
    refine min_le_min le_rfl (min_le_min ?_ ?_)
    · exact div_le_div_of_nonneg_left (by norm_num) ha' hab
    · exact div_le_div_of_nonneg_left hc (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) hw.le)

/-- ∫_ℝ ψ = 2 ∫_{(0,∞)} ψ (ψ even). -/
theorem integral_psiA_eq_two_mul (_hF : LocalHypsCoreW cϱ p F) :
    ∫ r, psiA cϱ p r = 2 * ∫ r in Set.Ioi 0, psiA cϱ p r := by
  have h := integral_comp_abs (f := psiA cϱ p)
  simp only [psiA_abs] at h
  exact h

theorem psiA_nonneg_of (hF : LocalHypsCoreW cϱ p F) (r : ℝ) : 0 ≤ psiA cϱ p r :=
  psiA_nonneg hF.L_pos.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w]) r

/-- tail: ∫_{(Δ,∞)} ψ ≤ c_ϱ/(w Δ) for Δ > 0 (from ψ(r) ≤ c/(w r²)). -/
theorem setIntegral_psiA_Ioi_le_div (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ≤ cϱ / (p.w * Δ) := by
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hg : IntegrableOn (fun x : ℝ => cϱ / p.w * x ^ (-2:ℝ)) (Set.Ioi Δ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hΔ).const_mul _
  calc ∫ r in Set.Ioi Δ, psiA cϱ p r ≤ ∫ r in Set.Ioi Δ, cϱ / p.w * r ^ (-2:ℝ) := by
        refine setIntegral_mono_on hF.psi_integrable.integrableOn hg measurableSet_Ioi
          fun r hr => ?_
        have hr0 : 0 < r := hΔ.trans hr
        calc psiA cϱ p r ≤ cϱ / (p.w * r ^ 2) := psiA_le_div_sq hr0.ne'
          _ = cϱ / p.w * r ^ (-2:ℝ) := by
              rw [Real.rpow_neg hr0.le, Real.rpow_two]; field_simp
    _ = cϱ / (p.w * Δ) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hΔ]
        norm_num
        rw [Real.rpow_neg_one]
        field_simp

/-- tail monotonicity: ∫_{(Δ,∞)} ψ ≤ ∫_{(0,∞)} ψ for Δ ≥ 0. -/
theorem setIntegral_psiA_Ioi_mono (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ≤ ∫ r in Set.Ioi 0, psiA cϱ p r :=
  setIntegral_mono_set hF.psi_integrable.integrableOn
    (Filter.Eventually.of_forall fun r => psiA_nonneg_of hF r)
    (Set.Ioi_subset_Ioi hΔ).eventuallyLE

/-- Generic: for f ≥ 0 antitone on [0,∞) and integrable on (Δ,∞), Δ ≥ 0, h > 0:
Σ_{j<n} f(Δ + j h) ≤ f(Δ) + h⁻¹ ∫_{(Δ,∞)} f  (j = 0 term + antitone comparison on each cell
[Δ+jh, Δ+(j+1)h], cells summed by intervalIntegral.sum_integral_adjacent_intervals). -/
theorem sum_grid_le_of_antitoneOn {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Ici 0))
    (h0 : ∀ x, 0 ≤ x → 0 ≤ f x) {Δ h : ℝ} (hΔ : 0 ≤ Δ) (hh : 0 < h)
    (hint : IntegrableOn f (Set.Ioi Δ)) (n : ℕ) :
    ∑ j ∈ Finset.range n, f (Δ + j * h) ≤ f Δ + h⁻¹ * ∫ r in Set.Ioi Δ, f r := by
  have hI0 : 0 ≤ ∫ r in Set.Ioi Δ, f r :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => h0 x (hΔ.trans (le_of_lt hx))
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact add_nonneg (h0 Δ hΔ) (mul_nonneg (inv_nonneg.mpr hh.le) hI0)
  | succ m =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    rw [add_comm]
    gcongr
    -- cells a j := Δ + j h
    set a : ℕ → ℝ := fun j => Δ + j * h with ha
    have ha_mono : ∀ j : ℕ, a j ≤ a (j + 1) := fun j => by
      simp only [ha, Nat.cast_add, Nat.cast_one]; nlinarith
    have hΔa : ∀ j : ℕ, Δ ≤ a j := fun j => by simp only [ha]; nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have hcellInt : ∀ j : ℕ, IntervalIntegrable f volume (a j) (a (j + 1)) := fun j => by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (ha_mono j)]
      exact hint.mono_set fun x hx => lt_of_le_of_lt (hΔa j) hx.1
    -- per cell: h · f(a (j+1)) ≤ ∫_{a j}^{a (j+1)} f
    have hcell : ∀ j : ℕ, f (Δ + (j + 1) * h) ≤ h⁻¹ * ∫ x in (a j)..(a (j + 1)), f x := by
      intro j
      rw [le_inv_mul_iff₀ hh]
      have hconst : ∫ x in (a j)..(a (j + 1)), f (a (j + 1)) = h * f (Δ + (j + 1) * h) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        simp only [ha, Nat.cast_add, Nat.cast_one]; ring
      rw [← hconst]
      refine intervalIntegral.integral_mono_on (ha_mono j) intervalIntegrable_const (hcellInt j)
        fun x hx => ?_
      have hx0 : 0 ≤ x := hΔ.trans ((hΔa j).trans hx.1)
      have hx1 : x ≤ a (j + 1) := hx.2
      have key := hf (show x ∈ Set.Ici (0:ℝ) from hx0) (show a (j + 1) ∈ Set.Ici (0:ℝ) from hx0.trans hx1) hx1
      simpa [ha, Nat.cast_add, Nat.cast_one] using key
    calc ∑ j ∈ Finset.range m, f (Δ + (↑j + 1) * h)
        ≤ ∑ j ∈ Finset.range m, h⁻¹ * ∫ x in (a j)..(a (j + 1)), f x :=
          Finset.sum_le_sum fun j _ => hcell j
      _ = h⁻¹ * ∫ x in (a 0)..(a m), f x := by
          rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals fun j _ => hcellInt j]
      _ ≤ h⁻¹ * ∫ r in Set.Ioi Δ, f r := by
          gcongr
          have h0m : a 0 ≤ a m := by
            simp only [ha, Nat.cast_zero, zero_mul, add_zero]; nlinarith [Nat.cast_nonneg (α := ℝ) m]
          rw [intervalIntegral.integral_of_le h0m]
          exact setIntegral_mono_set hint
            (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => h0 x (hΔ.trans (le_of_lt hx)))
            (LE.le.eventuallyLE fun x hx => lt_of_le_of_lt (hΔa 0) hx.1)

/-- grid sum vs integral (ψ antitone): Σ_{j<n} ψ(Δ + j h) ≤ ψ(Δ) + h⁻¹ ∫_{(Δ,∞)} ψ. -/
theorem sum_psiA_grid_le (hF : LocalHypsCoreW cϱ p F) {Δ h : ℝ} (hΔ : 0 ≤ Δ) (hh : 0 < h) (n : ℕ) :
    ∑ j ∈ Finset.range n, psiA cϱ p (Δ + j * h)
      ≤ psiA cϱ p Δ + h⁻¹ * ∫ r in Set.Ioi Δ, psiA cϱ p r :=
  sum_grid_le_of_antitoneOn
    (psiA_antitoneOn hF.L_pos.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w]))
    (fun x _ => psiA_nonneg_of hF x) hΔ hh hF.psi_integrable.integrableOn n

/-- ψ² is antitone on [0,∞) (ψ ≥ 0 antitone). -/
theorem psiA_sq_antitoneOn (hF : LocalHypsCoreW cϱ p F) :
    AntitoneOn (fun r => psiA cϱ p r ^ 2) (Set.Ici 0) := by
  have hc : 0 ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  intro a ha b hb hab
  have h := psiA_antitoneOn hF.L_pos.le hc hw ha hb hab
  show psiA cϱ p b ^ 2 ≤ psiA cϱ p a ^ 2
  exact pow_le_pow_left₀ (psiA_nonneg_of hF b) h 2

/-- same for ψ²: Σ_{j<n} ψ(Δ + j h)² ≤ ψ(Δ)² + h⁻¹ ∫_{(Δ,∞)} ψ². -/
theorem sum_psiA_sq_grid_le (hF : LocalHypsCoreW cϱ p F) {Δ h : ℝ} (hΔ : 0 ≤ Δ) (hh : 0 < h) (n : ℕ) :
    ∑ j ∈ Finset.range n, psiA cϱ p (Δ + j * h) ^ 2
      ≤ psiA cϱ p Δ ^ 2 + h⁻¹ * ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 :=
  sum_grid_le_of_antitoneOn (f := fun r => psiA cϱ p r ^ 2) (psiA_sq_antitoneOn hF)
    (fun _ _ => sq_nonneg _) hΔ hh hF.psi_sq_integrable.integrableOn n

/-- tail for ψ²: ∫_{(Δ,∞)} ψ² ≤ (c_ϱ/w)²/(3Δ³) for Δ > 0. -/
theorem setIntegral_psiA_sq_Ioi_le_div (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 ≤ (cϱ / p.w) ^ 2 / (3 * Δ ^ 3) := by
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : 0 ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hg : IntegrableOn (fun x : ℝ => (cϱ / p.w) ^ 2 * x ^ (-4:ℝ)) (Set.Ioi Δ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hΔ).const_mul _
  calc ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 ≤ ∫ r in Set.Ioi Δ, (cϱ / p.w) ^ 2 * r ^ (-4:ℝ) := by
        refine setIntegral_mono_on hF.psi_sq_integrable.integrableOn hg measurableSet_Ioi
          fun r hr => ?_
        have hr0 : 0 < r := hΔ.trans hr
        have h1 : psiA cϱ p r ≤ cϱ / (p.w * r ^ 2) := psiA_le_div_sq hr0.ne'
        calc psiA cϱ p r ^ 2 ≤ (cϱ / (p.w * r ^ 2)) ^ 2 := pow_le_pow_left₀ (psiA_nonneg_of hF r) h1 2
          _ = (cϱ / p.w) ^ 2 * r ^ (-4:ℝ) := by
              rw [show (-4:ℝ) = -((4:ℕ):ℝ) by norm_num, Real.rpow_neg hr0.le, Real.rpow_natCast]
              field_simp
    _ = (cϱ / p.w) ^ 2 / (3 * Δ ^ 3) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hΔ]
        norm_num
        field_simp

/-- ∫_{(Δ,∞)} ψ² ≤ ∫_ℝ ψ² ≤ 8L. -/
theorem setIntegral_psiA_sq_Ioi_le (hF : LocalHypsCoreW cϱ p F) (Δ : ℝ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 ≤ 8 * p.L :=
  le_trans (setIntegral_le_integral hF.psi_sq_integrable
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)) hF.integral_psi_sq_le

/-- `|φ̂(r)| ≤ ψ(r)` [eq:psidef] (LocalHyps field). -/
theorem abs_phiHat_le_psiA (hF : LocalHypsCoreW cϱ p F) (r : ℝ) : |F.phiHat r| ≤ psiA cϱ p r :=
  hF.phiHat_le_psi r

/-- `2Ψ₀ := ∫_ℝ ψ ≤ 2(4 + 2 log(c_ϱ L/4w))` [eq:psiints]. -/
theorem integral_psiA_le (hF : LocalHypsCoreW cϱ p F) :
    ∫ r, psiA cϱ p r ≤ 2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) := by
  rw [integral_psiA_eq_two_mul hF]; linarith [hF.integral_psi_Ioi_le]

end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


lemma sum_Ico_int_eq (p : Setting) (F : LocalFun) (τ : ℝ) :
    ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = ∑ k : Fin p.d, F.phiHat (τ - p.tau (k : ℕ)) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => F.phiHat (τ - p.tau (n : ℕ)) ^ 2) p.d]
  rw [show Finset.Ico (0:ℤ) (p.d : ℤ) = (Finset.range p.d).image (fun n : ℕ => (n : ℤ)) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hd⟩
      exact ⟨k.toNat, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega]
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]

lemma hasSum_total (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (F.a * p.L ^ 2) := by
  have h := hF.poisson τ τ
  rw [sub_self, hF.Phi_zero] at h
  have h2 : HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (p.L * (F.a * p.L)) := by
    refine HasSum.congr_fun h fun k => ?_
    rw [sq]
  rwa [show p.L * (F.a * p.L) = F.a * p.L ^ 2 by ring] at h2

/-- Poisson diagonal, finite part: `Σ_{k<d} φ̂(τ−τ_k)² ≤ aL²`, i.e. `ρ(τ) ≥ 0`. -/
theorem rho_nonneg (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) : 0 ≤ rho p F τ := by
  unfold rho
  have htot := hasSum_total hF τ
  have hle : ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2 ≤ F.a * p.L ^ 2 :=
    sum_le_hasSum _ (fun i _ => sq_nonneg _) htot
  rw [sum_Ico_int_eq] at hle
  linarith

/-- `ρ(τ) = Σ_{k∉[0,d)} φ̂(τ−τ_k)²` as a `HasSum` over the complement of `range d` in ℤ
(from LocalHyps.poisson τ τ and Phi_zero). -/
theorem hasSum_rho (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} => F.phiHat (τ - p.tau k) ^ 2)
      (rho p F τ) := by
  have htot := hasSum_total hF τ
  refine (Finset.hasSum_compl_iff (f := fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2)
    (Finset.Ico (0:ℤ) (p.d : ℤ))).2 ?_
  have he : rho p F τ + ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = F.a * p.L ^ 2 := by
    unfold rho
    rw [sum_Ico_int_eq]
    ring
  rw [he]
  exact htot

/-- **[eq:Kbounds]** first part: `|K(τ,τ')| ≤ aL² ≤ L²` (Cauchy–Schwarz + Poisson diagonal). -/
theorem abs_Kfun_le (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) : |Kfun p F τ τ'| ≤ p.L ^ 2 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin p.d => F.phiHat (τ - p.tau k)) (fun k : Fin p.d => F.phiHat (τ' - p.tau k))
  have hbound : ∀ σ : ℝ, ∑ k : Fin p.d, F.phiHat (σ - p.tau k) ^ 2 ≤ F.a * p.L ^ 2 := by
    intro σ
    have h0 := rho_nonneg hF σ
    unfold rho at h0
    linarith
  have hs1 : 0 ≤ ∑ k : Fin p.d, F.phiHat (τ' - p.tau k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have haL : F.a * p.L ^ 2 ≤ p.L ^ 2 := by
    nlinarith [hF.a_le_one, hF.a_pos.le, sq_nonneg p.L]
  have hK2 : Kfun p F τ τ' ^ 2 ≤ (p.L ^ 2) ^ 2 := by
    unfold Kfun
    calc (∑ k : Fin p.d, F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k)) ^ 2
        ≤ (∑ k : Fin p.d, F.phiHat (τ - p.tau k) ^ 2)
          * (∑ k : Fin p.d, F.phiHat (τ' - p.tau k) ^ 2) := hCS
      _ ≤ (p.L ^ 2) * (p.L ^ 2) :=
          mul_le_mul ((hbound τ).trans haL) ((hbound τ').trans haL) hs1 (sq_nonneg _)
      _ = (p.L ^ 2) ^ 2 := (sq _).symm
  nlinarith [abs_nonneg (Kfun p F τ τ'), sq_abs (Kfun p F τ τ'), sq_nonneg p.L]

/-- `|K_∞(τ,τ')| = L|Φ(τ−τ')| ≤ L² ` (LocalHyps.Phi_le_L). -/
theorem abs_Kinf_le (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) : |Kinf p F τ τ'| ≤ p.L ^ 2 := by
  have hL := hF.L_pos
  unfold Kinf
  rw [abs_mul, abs_of_pos hL, sq]
  exact mul_le_mul_of_nonneg_left (hF.Phi_le_L _) hL.le

/-- **[eq:Kbounds]** via ψ: `|K(τ,τ')| ≤ Σ_{k<d} ψ(τ−τ_k) ψ(τ'−τ_k)`. -/
theorem abs_Kfun_le_sum_psiA (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) :
    |Kfun p F τ τ'| ≤ ∑ k : Fin p.d, psiA cϱ p (τ - p.tau k) * psiA cϱ p (τ' - p.tau k) := by
  unfold Kfun
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have hL := hF.L_pos
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : 0 ≤ cϱ := by linarith [hF.four_le_cϱ]
  exact mul_le_mul (hF.phiHat_le_psi _) (hF.phiHat_le_psi _) (abs_nonneg _)
    (psiA_nonneg hL.le hc hw _)

/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/

/-- general reindexing `Σ_{k ∈ Ico 0 d} f k = Σ_{k : Fin d} f k` for `f : ℤ → ℝ`. -/
lemma sum_Ico_int_eq_sum_fin (f : ℤ → ℝ) (d : ℕ) :
    ∑ k ∈ Finset.Ico (0:ℤ) (d : ℤ), f k = ∑ k : Fin d, f ((k : ℕ) : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d]
  rw [show Finset.Ico (0:ℤ) (d : ℤ) = (Finset.range d).image (fun n : ℕ => (n : ℤ)) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hd⟩
      exact ⟨k.toNat, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega]
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]

/-- `K_out = K_∞ − K` as a HasSum over `k ∉ [0,d)` (from LocalHyps.poisson). -/
theorem hasSum_Kout (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) :
    HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} =>
      F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
      (Kinf p F τ τ' - Kfun p F τ τ') := by
  have htot : HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
      (Kinf p F τ τ') := hF.poisson τ τ'
  refine (Finset.hasSum_compl_iff (f := fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (Finset.Ico (0:ℤ) (p.d : ℤ))).2 ?_
  have he : Kinf p F τ τ' - Kfun p F τ τ'
      + ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k)
      = Kinf p F τ τ' := by
    rw [sum_Ico_int_eq_sum_fin (fun k => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k)), Kfun]
    ring
  rw [he]
  exact htot

/-- termwise weighted AM–GM: `|a b| ≤ (s a² + b²/s)/2` for `s > 0`. -/
lemma abs_mul_le_weighted (a b : ℝ) {s : ℝ} (hs : 0 < s) :
    |a * b| ≤ (s * a ^ 2 + b ^ 2 / s) / 2 := by
  rw [abs_mul]
  have h : 0 ≤ (s * |a| - |b|) ^ 2 / s := by positivity
  have e : (s * |a| - |b|) ^ 2 / s = s * a ^ 2 + b ^ 2 / s - 2 * (|a| * |b|) := by
    have ha := sq_abs a
    have hb := sq_abs b
    field_simp
    nlinarith [ha, hb]
  linarith [e ▸ h]

/-- **Pointwise bound for K_out** (weighted AM–GM): for every `s > 0`,
`|K_∞(τ,τ') − K(τ,τ')| ≤ (s ρ(τ) + ρ(τ')/s)/2`. -/
theorem abs_Kinf_sub_Kfun_le (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) {s : ℝ} (hs : 0 < s) :
    |Kinf p F τ τ' - Kfun p F τ τ'| ≤ (s * rho p F τ + rho p F τ' / s) / 2 := by
  set f : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} → ℝ :=
    fun k => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k) with hf
  have hK := hasSum_Kout hF τ τ'
  have hρ := hasSum_rho hF τ
  have hρ' := hasSum_rho hF τ'
  -- majorant
  have hmaj : HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} =>
      (s * F.phiHat (τ - p.tau k) ^ 2 + F.phiHat (τ' - p.tau k) ^ 2 / s) / 2)
      ((s * rho p F τ + rho p F τ' / s) / 2) :=
    ((hρ.mul_left s).add (hρ'.div_const s)).div_const 2
  have hle : ∀ k, |f k| ≤ (s * F.phiHat (τ - p.tau k) ^ 2 + F.phiHat (τ' - p.tau k) ^ 2 / s) / 2 :=
    fun k => abs_mul_le_weighted _ _ hs
  have habs : Summable (fun k => |f k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hmaj.summable
  rw [← hK.tsum_eq]
  calc |∑' k, f k| ≤ ∑' k, |f k| := by
        have := norm_tsum_le_tsum_norm (f := f) (by simpa [Real.norm_eq_abs] using habs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ (s * rho p F τ + rho p F τ' / s) / 2 :=
        hasSum_le hle habs.hasSum hmaj

end Kbounds


end PrimeSide
end Zeta23
