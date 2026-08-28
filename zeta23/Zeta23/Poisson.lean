/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
[lem:poisson] "Poisson summation for the Gabor system", the paper §2.2:

  "For all τ, τ' ∈ ℝ,
     K_∞(τ,τ') := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L·Φ(τ−τ'),   in particular   Σ_{k∈ℤ} φ̂(τ−τ_k)² = aL²."

Here τ_k := T + k h, h := 2π/L [eq:fk], Φ := (φ²)^ [eq:PhigA], a := L⁻¹∫φ² [eq:abdef], and
φ̂(s) = ∫ φ(u) e^{isu} du is the paper's Fourier convention (`Zeta23.paperFT`).  Only the
real-argument identity is proved (that is all [prop:block](ii) uses; the complex continuation
mentioned in [rem:pairblock] is not used by the proof).

Proof route (the paper's, rearranged so that Fourier inversion is not needed): with
  G(ξ) := L · ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du      (= L e^{−iTLξ}(φ_τ ∗ φ_{τ'})(Lξ)),
G is continuous with support in [−1,1] and G(k) = 0 for k ∈ ℤ∖{0} (because φ(u) = 0 for
|u| ≥ L/2), G(0) = L ∫ φ(u)φ(−u)e^{i(τ−τ')u} du = L Φ(τ−τ') (φ even), and a Fubini computation
gives 𝓕G(w) = φ̂(τ−τ_w) φ̂(τ'−τ_w) for Mathlib's 𝓕 and every real w (τ_w := T + w·2π/L).
Mathlib's Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
(Σ_k G(k) = Σ_n 𝓕G(n)) then gives the claim; summability of n ↦ φ̂(τ−τ_n)φ̂(τ'−τ_n) comes from
the decay |φ̂(r)| ≪ (1+r²)⁻¹, i.e. [eq:hfbound]/[eq:psidef].
-/
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Zeta23.Defs
import Zeta23.Poisson.PaperFT
import Zeta23.Taper.Strip
import Zeta23.Taper.Fourier

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23

namespace Poisson

/-! #### A decay-to-`IsBigO` lemma -/

/-- If `‖g w‖ · (1 + (c − w h)²) ≤ C` for all real `w` (`h ≠ 0`) then `g = O(|w|⁻²)` on
`cocompact ℝ`. -/
theorem isBigO_of_decay {g : ℝ → ℂ} {c h C : ℝ} (hh : h ≠ 0)
    (hg : ∀ w, ‖g w‖ * (1 + (c - w * h) ^ 2) ≤ C) :
    g =O[cocompact ℝ] fun w : ℝ => |w| ^ (-2 : ℝ) := by
  have hC : 0 ≤ C := le_trans (by positivity) (hg 0)
  refine IsBigO.of_bound (4 * C / h ^ 2) ?_
  have hev : ∀ᶠ w : ℝ in cocompact ℝ, max 1 (2 * |c| / |h|) ≤ ‖w‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hev] with w hw
  rw [Real.norm_eq_abs] at hw
  have hw1 : 1 ≤ |w| := le_trans (le_max_left _ _) hw
  have hw2 : 2 * |c| / |h| ≤ |w| := le_trans (le_max_right _ _) hw
  have hhpos : 0 < |h| := abs_pos.mpr hh
  have h1 : |w| * |h| / 2 ≤ |c - w * h| := by
    have h3 : |w * h| - |c| ≤ |c - w * h| := by
      have := abs_sub_abs_le_abs_sub (w * h) c
      rw [abs_sub_comm] at this
      exact this
    rw [abs_mul] at h3
    rw [div_le_iff₀ hhpos] at hw2
    linarith
  have h2 : (|w| * |h| / 2) ^ 2 ≤ 1 + (c - w * h) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rw [sq_abs] at this
    linarith
  have hnorm : ‖(|w| ^ (-2 : ℝ) : ℝ)‖ = (w ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _),
      Real.rpow_two, sq_abs]
  rw [hnorm]
  have hden : 0 < 1 + (c - w * h) ^ 2 := by positivity
  have hq : 0 < (|w| * |h| / 2) ^ 2 := by positivity
  have hw0 : w ≠ 0 := by intro h0; rw [h0, abs_zero] at hw1; linarith
  calc ‖g w‖ ≤ C / (1 + (c - w * h) ^ 2) := by rw [le_div_iff₀ hden]; exact hg w
    _ ≤ C / ((|w| * |h| / 2) ^ 2) := by gcongr
    _ = 4 * C / h ^ 2 * (w ^ 2)⁻¹ := by
      rw [div_pow, mul_pow, sq_abs, sq_abs]
      field_simp
      ring

/-! #### The auxiliary function `G` -/

variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)

/-- Integrand of `G`: `(ξ,u) ↦ L φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)}`. -/
noncomputable def gInt (ξ u : ℝ) : ℂ :=
  (L : ℂ) * ((φ u : ℂ) * (φ (L * ξ - u) : ℂ) *
    cexp (I * (τ * u + τ' * (L * ξ - u) - T * L * ξ)))

/-- `G(ξ) := L ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du` (see module docstring). -/
noncomputable def Gaux (ξ : ℝ) : ℂ := ∫ u, gInt φ L T τ τ' ξ u

variable {φ L T τ τ'}

theorem gInt_eq_zero_of_not_mem (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    {ξ u : ℝ} (h : ¬ (|ξ| < 1 ∧ |u| < L / 2)) : gInt φ L T τ τ' ξ u = 0 := by
  unfold gInt
  by_cases hu : |u| < L / 2
  · have hξ : 1 ≤ |ξ| := by
      by_contra h'
      exact h ⟨not_le.mp h', hu⟩
    have : L / 2 ≤ |L * ξ - u| := by
      have h4 : |L * ξ| - |u| ≤ |L * ξ - u| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h4
      nlinarith
    rw [hsupp _ this]
    simp
  · rw [hsupp u (not_lt.mp hu)]
    simp

theorem gInt_continuous (hφc : Continuous φ) :
    Continuous (Function.uncurry (gInt φ L T τ τ')) := by
  unfold gInt Function.uncurry
  fun_prop

theorem gInt_hasCompactSupport (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    HasCompactSupport (Function.uncurry (gInt φ L T τ τ')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod (isCompact_Icc (a := -(L / 2)) (b := L / 2))) ?_
  rintro ⟨ξ, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne (gInt_eq_zero_of_not_mem hL hsupp _)
  rintro ⟨h1, h2⟩
  apply hmem
  rw [mem_prod, mem_Icc, mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩,
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩

theorem gInt_integrable_prod (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    Integrable (Function.uncurry (gInt φ L T τ τ')) (volume.prod volume) :=
  (gInt_continuous hφc).integrable_of_hasCompactSupport (gInt_hasCompactSupport hL hsupp)

/-- `G` is continuous. -/
theorem Gaux_continuous (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) : Continuous (Gaux φ L T τ τ') := by
  have : Gaux φ L T τ τ' = fun ξ => ∫ u in Icc (-(L / 2)) (L / 2), gInt φ L T τ τ' ξ u := by
    funext ξ
    unfold Gaux
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    apply gInt_eq_zero_of_not_mem hL hsupp
    rintro ⟨-, h2⟩
    apply hu
    rw [mem_Icc]
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [this]
  exact continuous_parametric_integral_of_continuous (gInt_continuous hφc) isCompact_Icc

/-- `G(ξ) = 0` for `|ξ| ≥ 1`. -/
theorem Gaux_eq_zero (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {ξ : ℝ}
    (hξ : 1 ≤ |ξ|) : Gaux φ L T τ τ' ξ = 0 := by
  unfold Gaux
  rw [← integral_zero]
  congr 1 with u
  apply gInt_eq_zero_of_not_mem hL hsupp
  rintro ⟨h1, -⟩
  linarith

/-- `G(0) = L · (φ²)^(τ − τ')` (uses φ even). -/
theorem Gaux_zero (heven : ∀ u, φ (-u) = φ u) :
    Gaux φ L T τ τ' 0 = L * paperFT (fun u => ((φ u ^ 2 : ℝ) : ℂ)) ((τ - τ' : ℝ) : ℂ) := by
  unfold Gaux gInt
  rw [paperFT_def, integral_const_mul_C]
  congr 1
  congr 1 with u
  simp only [mul_zero, zero_sub, heven]
  push_cast
  ring_nf

/-- The exponent bookkeeping: for `L ≠ 0`,
`e^{i(τu + τ'(Lξ−u) − TLξ)} · e^{−2πiξw} = e^{iαu} · e^{iβ(Lξ−u)}` with
`α = τ − (T + w·2π/L)`, `β = τ' − (T + w·2π/L)`. -/
theorem cexp_bookkeeping (hL : L ≠ 0) (ξ u w : ℝ) :
    cexp (I * (τ * u + τ' * (L * ξ - u) - T * L * ξ)) * cexp (↑(-2 * π * ξ * w) * I)
      = cexp (I * ↑(τ - (T + w * (2 * π / L))) * u)
        * cexp (I * ↑(τ' - (T + w * (2 * π / L))) * ↑(L * ξ - u)) := by
  have hL' : (L : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Fubini computation: `𝓕G(w) = φ̂(τ − τ_w) φ̂(τ' − τ_w)`, `τ_w = T + w·2π/L`. -/
theorem fourier_Gaux (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (w : ℝ) :
    𝓕 (Gaux φ L T τ τ') w
      = paperFT (fun u => (φ u : ℂ)) ((τ - (T + w * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + w * (2 * π / L)) : ℝ) : ℂ) := by
  set α : ℝ := τ - (T + w * (2 * π / L)) with hα
  set β : ℝ := τ' - (T + w * (2 * π / L)) with hβ
  -- the integrand after multiplying in the character
  set J : ℝ → ℝ → ℂ := fun ξ u => cexp (↑(-2 * π * ξ * w) * I) * gInt φ L T τ τ' ξ u with hJ
  have hJint : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry J) := by
      have := gInt_continuous (L := L) (T := T) (τ := τ) (τ' := τ') hφc
      simp only [hJ]
      apply Continuous.mul _ this
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply (gInt_hasCompactSupport (T := T) (τ := τ) (τ' := τ') hL hsupp).mono
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro h0
    apply hp
    simp only [hJ, Function.uncurry] at h0 ⊢
    rw [show p = (p.1, p.2) from rfl] at h0
    simp only at h0
    rw [h0, mul_zero]
  -- Step 1: unfold 𝓕 and move the character inside
  rw [Real.fourier_real_eq_integral_exp_smul]
  have step1 : (fun ξ : ℝ => cexp (↑(-2 * π * ξ * w) * I) • Gaux φ L T τ τ' ξ)
      = fun ξ => ∫ u, J ξ u := by
    funext ξ
    rw [smul_eq_mul, Gaux, hJ]
    beta_reduce
    rw [integral_const_mul_C]
  rw [step1]
  -- Step 2: swap the integrals
  rw [integral_integral_swap hJint]
  -- Step 3: compute the inner integral
  have step3 : ∀ u : ℝ, ∫ ξ, J ξ u
      = (φ u : ℂ) * cexp (I * α * u) * paperFT (fun v => (φ v : ℂ)) β := by
    intro u
    -- F0 v := φ(v) e^{iβv};  the ξ-integrand is φ(u)e^{iαu} · L · F0(Lξ − u)
    set F0 : ℝ → ℂ := fun v => (φ v : ℂ) * cexp (I * β * (v : ℂ)) with hF0
    have hpt : ∀ ξ : ℝ, J ξ u = (φ u : ℂ) * cexp (I * α * u)
        * ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      intro ξ
      simp only [hJ, gInt, hF0]
      have := cexp_bookkeeping (T := T) (τ := τ) (τ' := τ') hL.ne' ξ u w
      rw [← hα, ← hβ] at this
      calc cexp (↑(-2 * π * ξ * w) * I) * (↑L * (↑(φ u) * ↑(φ (L * ξ - u))
              * cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑ξ - ↑u) - ↑T * ↑L * ↑ξ))))
          = ↑L * ↑(φ u) * ↑(φ (L * ξ - u)) * (cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑ξ - ↑u)
              - ↑T * ↑L * ↑ξ)) * cexp (↑(-2 * π * ξ * w) * I)) := by ring
        _ = ↑L * ↑(φ u) * ↑(φ (L * ξ - u)) * (cexp (I * ↑α * ↑u) * cexp (I * ↑β * ↑(L * ξ - u))) := by
              rw [this]
        _ = _ := by push_cast; ring
    have hint : ∫ ξ, J ξ u = ∫ ξ, (φ u : ℂ) * cexp (I * α * u)
        * ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      congr 1 with ξ; exact hpt ξ
    rw [hint, integral_const_mul_C, integral_const_mul_C,
      Measure.integral_comp_mul_left (fun y : ℝ => F0 (y - u)) L,
      integral_sub_right_eq_self F0 u, paperFT_def, abs_of_pos (inv_pos.mpr hL)]
    congr 1
    rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ofReal_inv,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hL.ne'), one_mul]
  simp_rw [step3]
  -- Step 4: pull the constant out of the outer integral
  rw [integral_mul_const_C, paperFT_def, paperFT_def]

/-! #### The abstract identity -/

/-- Core identity [lem:poisson], complex form, for an abstract window: `φ : ℝ → ℝ` continuous,
even, vanishing for `|u| ≥ L/2` (`L > 0`), with `|φ̂(s)|(1+s²)` bounded on ℝ.
For all real `T, τ, τ'`:  `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L · (φ²)^(τ−τ')`, `τ_k = T + k·2π/L`,
as a `HasSum`. -/
theorem hasSum_paperFT_mul_paperFT {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (heven : ∀ u, φ (-u) = φ u)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
                        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      (L * paperFT (fun u => ((φ u ^ 2 : ℝ) : ℂ)) ((τ - τ' : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hdecay
  set G := Gaux φ L T τ τ' with hG
  have hGc : Continuous G := Gaux_continuous hL hφc hsupp
  -- G has compact support, hence is O(|x|^{-2})
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, (1 : ℝ) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hG, Gaux_eq_zero hL hsupp (by simpa using hx)]
    simp
  -- decay of 𝓕 G
  have hφhat_bdd : ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ ≤ C := by
    intro s
    have := hC s
    have h1 : ‖paperFT (fun u => (φ u : ℂ)) s‖ * 1 ≤ ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) := by
      gcongr; nlinarith
    linarith
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hφhat_bdd 0)
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply isBigO_of_decay (c := τ - T) (h := 2 * π / L) (C := C * C) (by positivity)
    intro w
    rw [hG, fourier_Gaux hL hφc hsupp w, norm_mul]
    have e1 : τ - T - w * (2 * π / L) = τ - (T + w * (2 * π / L)) := by ring
    rw [e1]
    calc ‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
          * ‖paperFT (fun u => (φ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖
          * (1 + (τ - (T + w * (2 * π / L))) ^ 2)
        = (‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
            * (1 + (τ - (T + w * (2 * π / L))) ^ 2))
          * ‖paperFT (fun u => (φ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖ := by ring
      _ ≤ C * C := by
        apply mul_le_mul (hC _) (hφhat_bdd _) (norm_nonneg _) hC0
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  -- Poisson summation at x = 0
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hGc one_lt_two hGO hsum 0
  have lhs : ∑' n : ℤ, G (0 + n) = G 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zero_add, hG, Gaux_eq_zero hL hsupp]
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
  have rhs : ∑' n : ℤ, 𝓕 G n * fourier n ((0 : ℝ) : UnitAddCircle) = ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [lhs, rhs] at key
  -- conclude
  have hs : HasSum (fun n : ℤ => 𝓕 G n) (G 0) := by
    rw [key]; exact hsum.hasSum
  rw [hG, Gaux_zero heven] at hs
  convert hs using 1
  funext k
  rw [fourier_Gaux hL hφc hsupp]

end Poisson

namespace Taper

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- Decay input for Poisson: `|φ̂(s)|(1 + s²) ≤ L + C₁` on ℝ (from [eq:hfbound] at `y = 0`). -/
theorem phiHat_decay (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (phi ϱ L w u : ℂ)) s‖ * (1 + s ^ 2) ≤ C := by
  refine ⟨L + C1 ϱ L w, fun s => ?_⟩
  have h0 := norm_phiHat_le hϱ hw hwL s
  have h2 := norm_phiHat_mul_sq_le hϱ hw hwL s
  simp only [ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, norm_real,
    Real.norm_eq_abs, sq_abs] at h0 h2
  unfold phiHat at h0 h2
  linarith

/-- [lem:poisson], general form, real-valued:
`Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` with `τ_k = T + k·(2π/L)`. -/
theorem hasSum_phiHatR_mul (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => phiHatR ϱ L w (τ - (T + k * (2 * π / L)))
                          * phiHatR ϱ L w (τ' - (T + k * (2 * π / L))))
      (L * PhiR ϱ L w (τ - τ')) := by
  have hL : 0 < L := by linarith
  have h := Poisson.hasSum_paperFT_mul_paperFT hL (phi_continuous hϱ hw hwL)
    (fun u hu => phi_eq_zero hϱ hw hu) (fun u => phi_even u) (phiHat_decay hϱ hw hwL) T τ τ'
  -- transport along re : ℂ → ℝ
  have h2 := (Complex.reCLM.hasSum h)
  convert h2 using 1
  · funext k
    simp only [Complex.reCLM_apply]
    rw [show paperFT (fun u => (phi ϱ L w u : ℂ)) = phiHat ϱ L w from rfl,
      phiHat_ofReal, phiHat_ofReal]
    norm_cast
  · simp only [Complex.reCLM_apply]
    rw [show paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) = Phi ϱ L w from rfl, Phi_ofReal]
    norm_cast

/-- [lem:poisson], "in particular": `Σ_{k∈ℤ} φ̂(γ−τ_k)² = a L²` for every real `γ`. -/
theorem hasSum_phiHatR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (T γ : ℝ) :
    HasSum (fun k : ℤ => phiHatR ϱ L w (γ - (T + k * (2 * π / L))) ^ 2)
      (aConst ϱ L w * L ^ 2) := by
  have h := hasSum_phiHatR_mul hϱ hw hwL T γ γ
  simp only [sub_self, PhiR_zero hϱ hw hwL, ← pow_two] at h
  convert h using 1
  ring

end Taper

namespace Params

variable {P : Params} {T : ℝ}

private theorem w_pos' (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w

variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-- [lem:poisson] for the paper's data: for all real τ, τ',
`HasSum (k ↦ φ̂(τ − τ_k) φ̂(τ' − τ_k)) (L Φ(τ − τ'))`, `τ_k = P.tau T k = T + k·(2π/L)`. -/
theorem hasSum_phiHatR_mul (τ τ' : ℝ) :
    HasSum (fun k : ℤ => P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ' - P.tau T k))
      (P.L T * P.PhiR T (τ - τ')) :=
  Taper.hasSum_phiHatR_mul hP.taper (w_pos' hP) (by linarith [hP.one_le_w]) T τ τ'

/-- [lem:poisson] "in particular": `HasSum (k ↦ φ̂(γ − τ_k)²) (a L²)` for every real γ. -/
theorem hasSum_phiHatR_sq (γ : ℝ) :
    HasSum (fun k : ℤ => P.phiHatR T (γ - P.tau T k) ^ 2) (P.a T * P.L T ^ 2) :=
  Taper.hasSum_phiHatR_sq hP.taper (w_pos' hP) (by linarith [hP.one_le_w]) T γ

theorem tsum_phiHatR_sq (γ : ℝ) :
    ∑' k : ℤ, P.phiHatR T (γ - P.tau T k) ^ 2 = P.a T * P.L T ^ 2 :=
  (hasSum_phiHatR_sq hP hwL γ).tsum_eq

end Params

end Zeta23
