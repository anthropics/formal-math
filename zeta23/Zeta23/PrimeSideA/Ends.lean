/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (the paper, §5, §5.3), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

MAIN RESULT (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
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
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X (Zeta23/PiFacts.lean,
  from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

The proof is assembled from the 𝓔₁ and 𝓔₂ bounds (Zeta23.PrimeSideA.EndsE1/EndsE2) in the
theorems below.
-/
import Zeta23.PrimeSideA.EndsE1
import Zeta23.PrimeSideA.EndsE2

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-- `B² ≪ l² + X` [eq:Bdef]: `(l + 4√X)² ≤ 32 (l² + X)` (for `l ≥ 0`, `X ≥ 0`). -/
theorem Bconst_sq_le (p : Setting) (_hl : 0 ≤ p.l) : Bconst p ^ 2 ≤ 32 * (p.l ^ 2 + p.X) := by
  unfold Bconst
  have hX := p.X_pos.le
  have hs : Real.sqrt p.X ^ 2 = p.X := Real.sq_sqrt hX
  nlinarith [Real.sqrt_nonneg p.X, sq_nonneg (p.l - 4 * Real.sqrt p.X)]

section Main
variable (cϱ lam : ℝ)

/-- **[lem:ends], ν-generic, window-generic core**: LocalHypsCoreW + the cap L ≤ 2l (used downstream with λ ∈ (1,2]). -/
theorem lem_ends_nu_W :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      |(p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F|
        ≤ C * (p.L * p.l * Real.log p.l * B ^ 2) := by
  obtain ⟨C₁, T₁, h1⟩ := calE1_bound cϱ lam
  obtain ⟨C₂, T₂, h2⟩ := calE2_bound cϱ lam
  -- T ≥ 2π e^e gives l ≥ e ≥ 1 hence log l ≥ 1
  refine ⟨(|C₁| + |C₂|), max (max T₁ T₂) (2 * π * Real.exp (Real.exp 1)),
    fun p F B ν hplam hT hF hL2l hνc hν hBl => ?_⟩
  have hT1 : T₁ ≤ p.T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ p.T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTe : 2 * π * Real.exp (Real.exp 1) ≤ p.T := le_trans (le_max_right _ _) hT
  have hl : Real.exp 1 ≤ p.l := Setting.le_l_of_T hTe
  have hl1 : 1 ≤ p.l := le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) hl
  have hlog : 1 ≤ Real.log p.l := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hl
  have hT' : 2 * π ≤ p.T := Setting.twopi_le_T (Real.exp_pos 1).le hTe
  have hL := hF.L_pos
  have hB0 : 0 ≤ B := le_trans (by linarith) hBl
  have e1 := h1 p F B ν hplam hT1 hF hL2l hνc hν
  have e2 := h2 p F B ν hplam hT2 hF hL2l hνc hν hBl
  have hdec := decomp hνc hF hν hB0 hT'
  have hkey : (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F
      = (p.L)⁻¹ ^ 2 * (calE1 p F ν + calE2 p F ν) := by
    rw [← hdec]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (by positivity)]
  have hsum : |calE1 p F ν + calE2 p F ν|
      ≤ (|C₁| + |C₂|) * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
    calc |calE1 p F ν + calE2 p F ν| ≤ |calE1 p F ν| + |calE2 p F ν| := abs_add_le _ _
      _ ≤ C₁ * (p.L ^ 3 * B ^ 2 * p.l) + C₂ * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) :=
          add_le_add e1 e2
      _ ≤ |C₁| * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l)
          + |C₂| * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
          gcongr ?_ + ?_
          · calc C₁ * (p.L ^ 3 * B ^ 2 * p.l) ≤ |C₁| * (p.L ^ 3 * B ^ 2 * p.l) := by
                  gcongr; exact le_abs_self _
              _ = |C₁| * (p.L ^ 3 * B ^ 2 * p.l) * 1 := (mul_one _).symm
              _ ≤ |C₁| * (p.L ^ 3 * B ^ 2 * p.l) * Real.log p.l := by gcongr
              _ = _ := by ring
          · exact mul_le_mul_of_nonneg_right (le_abs_self C₂) (by positivity)
      _ = _ := by ring
  calc (p.L)⁻¹ ^ 2 * |calE1 p F ν + calE2 p F ν|
      ≤ (p.L)⁻¹ ^ 2 * ((|C₁| + |C₂|) * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l)) := by gcongr
    _ = (|C₁| + |C₂|) * (p.L * p.l * Real.log p.l * B ^ 2) := by field_simp

/-- **[lem:ends], ν-GENERIC FORM** under the paper's window hypotheses (LocalHypsCore, λ ≤ 1):
`|L⁻² Σ_{k,l<d} G_{kl}(ν)² − 𝓜(ν)| ≤ C · L · l · log l · B²` for `T ≥ T₀` (C, T₀ depend on c_ϱ only),
for any continuous density with `|ν(τ)| ≤ B + log⁺(|τ|/4T)`, `l ≤ B`. -/
theorem lem_ends_nu :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → Continuous ν → NuBound p B ν → p.l ≤ B →
      |(p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F|
        ≤ C * (p.L * p.l * Real.log p.l * B ^ 2) := by
  obtain ⟨C, T₀, h⟩ := lem_ends_nu_W cϱ lam
  refine ⟨C, T₀, fun p F B ν hplam hT hF hνc hν hBl => h p F B ν hplam hT hF.toCoreW ?_ hνc hν hBl⟩
  -- L = λ l ≤ l ≤ 2l
  have h1 := hF.lam_le_one
  have h2 := hF.lam_pos
  have h3 : p.L = p.lam * p.l := rfl
  have hl : 0 ≤ p.l := by linarith [hF.one_le_l]
  rw [h3]; nlinarith

/-- [eq:Bdef] in the present packaging: `Zeta23.nuX_abs_le` gives
`NuBound p (Bconst p) (Zeta23.nuX p.X)` for `T ≥ T₀(λ)`. -/
theorem nuBound_eventually (hΓ : Zeta23.GammaFacts) (hlam : 0 < lam) :
    ∃ T₀ : ℝ, ∀ p : Setting, p.lam = lam → T₀ ≤ p.T → NuBound p (Bconst p) (Zeta23.nuX p.X) := by
  obtain ⟨T₀, _, h⟩ := Zeta23.nuX_abs_le hΓ hlam
  refine ⟨T₀, fun p hplam hT τ => ?_⟩
  have := h p.T hT τ
  rw [← hplam] at this
  exact this

/-- **[lem:ends] (End effects)** (§5.3, verbatim): for `T ≥ T₀`,
`tr G̃² = 𝓜 + O(L · l · log l · (l² + X))`,  `𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ)ν_X(τ') dτdτ'`.
ζ-instantiation of `lem_ends_nu` with
`ν := ν_X`, `B := l + 4√X` ([eq:Bdef] via `Zeta23.nuX_abs_le`, continuity of μ from H-Γ);
`hcheb` is carried for interface uniformity. -/
theorem lem_ends (hΓ : Zeta23.GammaFacts) (_hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X))) := by
  obtain ⟨C, T₁, h1⟩ := lem_ends_nu cϱ lam
  obtain ⟨T₂, h2⟩ := nuBound_eventually lam hΓ hlam.1
  refine ⟨32 * |C|, max (max T₁ T₂) 1, fun p F hplam hT hF => ?_⟩
  have hT1 : T₁ ≤ p.T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ p.T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hν := h2 p hplam hT2
  have hl0 : 0 ≤ p.l := by linarith [hF.one_le_l]
  have hBl : p.l ≤ Bconst p := by unfold Bconst; have := Real.sqrt_nonneg p.X; linarith
  have h := h1 p F (Bconst p) (Zeta23.nuX p.X) hplam hT1 hF (nuX_continuous hΓ hF.toCoreW) hν hBl
  have hB := Bconst_sq_le p hl0
  have e : trGt2A p F - MtotalA p F
      = (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Zeta23.nuX p.X) p F k l ^ 2
        - MtotalNu (Zeta23.nuX p.X) p F := rfl
  show |trGt2A p F - MtotalA p F| ≤ _
  rw [e]
  refine h.trans ?_
  have hnn : 0 ≤ p.L * p.l * Real.log p.l := by
    have := hF.L_pos
    have : 0 ≤ Real.log p.l := Real.log_nonneg hF.one_le_l
    positivity
  calc C * (p.L * p.l * Real.log p.l * Bconst p ^ 2)
      ≤ |C| * (p.L * p.l * Real.log p.l * Bconst p ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (p.L * p.l * Real.log p.l * (32 * (p.l ^ 2 + p.X))) := by gcongr
    _ = 32 * |C| * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)) := by ring

end Main

end PrimeSide
end Zeta23
