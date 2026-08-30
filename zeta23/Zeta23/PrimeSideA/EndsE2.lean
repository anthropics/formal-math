/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₂ (§5.3).  Statement consumed by
Zeta23/PrimeSideA/Ends.lean.
Substrate: Zeta23/PrimeSideA/EndsWeighted.lean; 1-D estimates N1/N2 from
Zeta23/PrimeSideA/EndsNu.lean.
-/
import Zeta23.PrimeSideA.EndsNu

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

section Assembly

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- Pointwise: |trG2integrand(τ,τ')| ≤ L² Σ_{k<d} ψ(τ−τ_k)ψ(τ'−τ_k) · |ν(τ)| |ν(τ')|
([eq:Kbounds]). -/
theorem abs_trG2integrand_le (hF : LocalHypsCoreW cϱ p F) (q : ℝ × ℝ) :
    |trG2integrand p F ν q| ≤ p.L ^ 2 *
      (∑ k ∈ Finset.range p.d, psiA cϱ p (q.1 - p.tau k) * psiA cϱ p (q.2 - p.tau k))
      * (|ν q.1| * |ν q.2|) := by
  have hK2 : Kfun p F q.1 q.2 ^ 2 ≤ p.L ^ 2 *
      ∑ k ∈ Finset.range p.d, psiA cϱ p (q.1 - p.tau k) * psiA cϱ p (q.2 - p.tau k) := by
    have h1 := abs_Kfun_le hF q.1 q.2
    have h2 := abs_Kfun_le_sum_psiA hF q.1 q.2
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => psiA cϱ p (q.1 - p.tau i) * psiA cϱ p (q.2 - p.tau i)) p.d] at h2
    calc Kfun p F q.1 q.2 ^ 2 = |Kfun p F q.1 q.2| * |Kfun p F q.1 q.2| := by
          rw [← sq_abs]; ring
      _ ≤ p.L ^ 2 * ∑ k ∈ Finset.range p.d,
            psiA cϱ p (q.1 - p.tau k) * psiA cϱ p (q.2 - p.tau k) := by
          exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  calc |trG2integrand p F ν q|
      = Kfun p F q.1 q.2 ^ 2 * (|ν q.1| * |ν q.2|) := by
        unfold trG2integrand
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
    _ ≤ _ := by
        gcongr

/-- the 𝓔₂ majorant kernel with its ν-weights: `L²·(Σ_{k<d} ψ(τ−τ_k)ψ(τ'−τ_k))·|ν(τ)||ν(τ')|`. -/
def majK2 (cϱ : ℝ) (p : Setting) (ν : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  p.L ^ 2 * (∑ k ∈ Finset.range p.d, psiA cϱ p (q.1 - p.tau k) * psiA cϱ p (q.2 - p.tau k))
    * (|ν q.1| * |ν q.2|)

theorem abs_trG2integrand_le_majK2 (hF : LocalHypsCoreW cϱ p F) (q : ℝ × ℝ) :
    |trG2integrand p F ν q| ≤ majK2 cϱ p ν q := abs_trG2integrand_le hF q

/-- the majorant kernel is integrable on ℝ² (finite sum of products of integrable 1-D weights). -/
theorem majK2_integrable (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (_hB0 : 0 ≤ B) (hT : 2 * π ≤ p.T) : Integrable (majK2 cϱ p ν) := by
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hT0 : 0 < p.T := by linarith
  have hB1 : 1 ≤ max B 1 := le_max_right _ _
  have hν' : NuBound p (max B 1) ν := fun τ => (hν τ).trans (by linarith [le_max_left B 1])
  have htau : ∀ k ∈ Finset.range p.d, (p.tau k : ℝ) ∈ Icc p.T (2 * p.T) := by
    intro k hk
    have := Setting.tau_mem p hF.L_pos hT0.le hk
    exact ⟨this.1, this.2⟩
  have hwk : ∀ k ∈ Finset.range p.d,
      Integrable (fun τ : ℝ => psiA cϱ p (τ - p.tau k) * |ν τ|) :=
    fun k hk => integrable_psiA_shift_mul_nu hνc hF hν' hB1 hT1 (htau k hk)
  have h : Integrable (fun q : ℝ × ℝ => ∑ k ∈ Finset.range p.d,
      (p.L ^ 2 * (psiA cϱ p (q.1 - p.tau k) * |ν q.1|)) * (psiA cϱ p (q.2 - p.tau k) * |ν q.2|)) := by
    refine integrable_finsetSum _ fun k hk => ?_
    exact ((hwk k hk).const_mul (p.L ^ 2)).mul_prod (hwk k hk)
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [majK2]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `|𝓔₂(ν)| ≤ ∬_{(I×I)ᶜ} majK2(ν)`. -/
theorem abs_calE2_le_maj (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB0 : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    |calE2 p F ν| ≤ ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q := by
  have hfi : Integrable (trG2integrand p F ν) := trG2integrand_integrable hνc hF hν hB0 hT
  unfold calE2
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
    (majK2_integrable hνc hF hν hB0 hT).integrableOn
    (Filter.Eventually.of_forall fun q => ?_)
  show ‖trG2integrand p F ν q‖ ≤ _
  rw [Real.norm_eq_abs]
  exact abs_trG2integrand_le_majK2 hF q

/-- **The Fubini core of the 𝓔₂ majorant bound** (§5.3), with the two 1-D estimates abstracted:
if  ∫ ψ(τ−a)|ν(τ)| dτ ≤ M₁  for every a ∈ [T,2T]  and  ∫_{Iᶜ} (Σ_k ψ(τ−τ_k))|ν(τ)| dτ ≤ M₂,  then
∬_{(I×I)ᶜ} majK2(ν) ≤ 2·L²·M₁·M₂  ((I×I)ᶜ ⊆ (Iᶜ×ℝ) ∪ (ℝ×Iᶜ) and two iterated integrals). -/
theorem setIntegral_compl_sqI_majK2_le (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB1 : 1 ≤ B) (hT1 : 1 ≤ p.T) {M1 M2 : ℝ} (hM1nn : 0 ≤ M1)
    (hN1 : ∀ a ∈ Icc p.T (2 * p.T), ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ| ≤ M1)
    (hN2 : ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ| ≤ M2) :
    ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ 2 * (p.L ^ 2 * M1 * M2) := by
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hL0 : (0 : ℝ) < p.L := hF.L_pos
  have hw1 : (1 : ℝ) ≤ p.w := hF.one_le_w
  have hc4 : (4 : ℝ) ≤ cϱ := hF.four_le_cϱ
  -- grid points lie in [T, 2T]
  have htau : ∀ k ∈ Finset.range p.d, (p.tau k : ℝ) ∈ Icc p.T (2 * p.T) := by
    intro k hk
    have := Setting.tau_mem p hL0 hT0.le hk
    exact ⟨this.1, this.2⟩
  -- per-k integrability of the 1-D weights
  have hwk : ∀ k ∈ Finset.range p.d,
      Integrable (fun τ : ℝ => psiA cϱ p (τ - p.tau k) * |ν τ|) :=
    fun k hk => integrable_psiA_shift_mul_nu hνc hF hν hB1 hT1 (htau k hk)
  have hsum_int : Integrable (fun τ : ℝ =>
      (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|) := by
    have := integrable_finsetSum (Finset.range p.d) hwk
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [Finset.sum_mul]
  have hψnn : ∀ (τ : ℝ) (k : ℕ), 0 ≤ psiA cϱ p (τ - p.tau k) :=
    fun τ k => psiA_nonneg hL0.le (by linarith) (by linarith) _
  -- global integrability of the majorant (finite sum of products of 1-D integrable weights)
  have hMnn : ∀ q : ℝ × ℝ, 0 ≤ majK2 cϱ p ν q := fun q =>
    mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hψnn q.1 k) (hψnn q.2 k))) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have habs : Integrable (fun q : ℝ × ℝ => majK2 cϱ p ν q) := by
    have h : Integrable (fun q : ℝ × ℝ => ∑ k ∈ Finset.range p.d,
        (p.L ^ 2 * (psiA cϱ p (q.1 - p.tau k) * |ν q.1|)) * (psiA cϱ p (q.2 - p.tau k) * |ν q.2|)) := by
      refine integrable_finsetSum _ fun k hk => ?_
      exact ((hwk k hk).const_mul (p.L ^ 2)).mul_prod (hwk k hk)
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [majK2]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- Step B: complement of the square inside the union of two strips
  set S₁ : Set (ℝ × ℝ) := ((p.I)ᶜ) ×ˢ (univ : Set ℝ) with hS₁
  set S₂ : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ ((p.I)ᶜ) with hS₂
  have hmI : MeasurableSet ((p.I)ᶜ) := measurableSet_Icc.compl
  have hmS₁ : MeasurableSet S₁ := hmI.prod MeasurableSet.univ
  have hmS₂ : MeasurableSet S₂ := MeasurableSet.univ.prod hmI
  have hsub : (sqI p)ᶜ ⊆ S₁ ∪ S₂ := by
    rintro ⟨τ, τ'⟩ hq
    rw [Set.mem_compl_iff] at hq
    unfold sqI at hq
    rw [Set.mem_prod] at hq
    push Not at hq
    by_cases h1 : τ ∈ p.I
    · exact Or.inr ⟨trivial, hq h1⟩
    · exact Or.inl ⟨h1, trivial⟩
  have hB : ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q
      ≤ (∫ q in S₁, majK2 cϱ p ν q) + ∫ q in S₂, majK2 cϱ p ν q := by
    have h1 : ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ ∫ q in S₁ ∪ S₂, majK2 cϱ p ν q :=
      setIntegral_mono_set habs.integrableOn
        (Filter.Eventually.of_forall fun q => hMnn q)
        hsub.eventuallyLE
    refine h1.trans ?_
    rw [← Set.union_sdiff_self]
    rw [setIntegral_union disjoint_sdiff_self_right (hmS₂.diff hmS₁)
      habs.integrableOn habs.integrableOn]
    have hmono : ∫ q in S₂ \ S₁, majK2 cϱ p ν q ≤ ∫ q in S₂, majK2 cϱ p ν q :=
      setIntegral_mono_set habs.integrableOn
        (Filter.Eventually.of_forall fun q => hMnn q)
        ((Set.sdiff_subset : S₂ \ S₁ ⊆ S₂).eventuallyLE)
    linarith
  -- Step C: iterated-integral bound over S₁ (constrained first coordinate)
  have hrestrict1 : (volume : Measure (ℝ × ℝ)).restrict S₁
      = (volume.restrict ((p.I)ᶜ)).prod volume := by
    rw [hS₁, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hint1 : Integrable (fun q : ℝ × ℝ => majK2 cϱ p ν q)
      ((volume.restrict ((p.I)ᶜ)).prod volume) := by
    rw [← hrestrict1]; exact habs.integrableOn
  have hiter1 : ∫ q in S₁, majK2 cϱ p ν q
      = ∫ τ in (p.I)ᶜ, ∫ τ', majK2 cϱ p ν (τ, τ') := by
    rw [show (∫ q in S₁, majK2 cϱ p ν q)
        = ∫ q, majK2 cϱ p ν q ∂((volume : Measure (ℝ × ℝ)).restrict S₁) from rfl,
      hrestrict1, integral_prod _ hint1]
  have hprod_bound : ∀ τ τ' : ℝ, majK2 cϱ p ν (τ, τ')
      ≤ ∑ k ∈ Finset.range p.d, (p.L ^ 2 * psiA cϱ p (τ - p.tau k) * |ν τ|)
          * (psiA cϱ p (τ' - p.tau k) * |ν τ'|) := by
    intro τ τ'
    refine le_of_eq ?_
    simp only [majK2]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hterm_nn : ∀ (τ : ℝ) (k : ℕ), 0 ≤ p.L ^ 2 * psiA cϱ p (τ - p.tau k) * |ν τ| :=
    fun τ k => mul_nonneg (mul_nonneg (by positivity) (hψnn τ k)) (abs_nonneg _)
  have hmaj_int : ∀ τ : ℝ, Integrable (fun τ' : ℝ =>
      ∑ k ∈ Finset.range p.d, (p.L ^ 2 * psiA cϱ p (τ - p.tau k) * |ν τ|)
        * (psiA cϱ p (τ' - p.tau k) * |ν τ'|)) :=
    fun τ => integrable_finsetSum _ (fun k hk => (hwk k hk).const_mul _)
  have hinner1 : ∀ τ : ℝ, (∫ τ', majK2 cϱ p ν (τ, τ'))
      ≤ p.L ^ 2 * M1 * ((∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|) := by
    intro τ
    have h1 : (∫ τ', majK2 cϱ p ν (τ, τ')) ≤ ∫ τ', ∑ k ∈ Finset.range p.d,
        (p.L ^ 2 * psiA cϱ p (τ - p.tau k) * |ν τ|)
          * (psiA cϱ p (τ' - p.tau k) * |ν τ'|) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ' => hMnn (τ, τ'))
        (hmaj_int τ) (Filter.Eventually.of_forall fun τ' => hprod_bound τ τ')
    refine h1.trans ?_
    rw [integral_finsetSum _ (fun k hk => (hwk k hk).const_mul _)]
    have h2 : ∀ k ∈ Finset.range p.d,
        (∫ τ', (p.L ^ 2 * psiA cϱ p (τ - p.tau k) * |ν τ|)
          * (psiA cϱ p (τ' - p.tau k) * |ν τ'|))
        ≤ (p.L ^ 2 * psiA cϱ p (τ - p.tau k) * |ν τ|) * M1 := by
      intro k hk
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hN1 _ (htau k hk)) (hterm_nn τ k)
    refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have houter1 : ∫ q in S₁, majK2 cϱ p ν q
      ≤ p.L ^ 2 * M1 * M2 := by
    rw [hiter1]
    have h1 : ∫ τ in (p.I)ᶜ, (∫ τ', majK2 cϱ p ν (τ, τ'))
        ≤ ∫ τ in (p.I)ᶜ, p.L ^ 2 * M1
            * ((∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun τ => integral_nonneg fun τ' => hMnn (τ, τ'))
        (hsum_int.integrableOn.const_mul _)
        (Filter.Eventually.of_forall fun τ => hinner1 τ)
    refine h1.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hN2 (mul_nonneg (by positivity : (0:ℝ) ≤ p.L ^ 2) hM1nn)
  -- Step D: S₂ is the swap image of S₁ and the majorant is swap-symmetric
  have houter2 : ∫ q in S₂, majK2 cϱ p ν q ≤ p.L ^ 2 * M1 * M2 := by
    have hsymm : ∀ q : ℝ × ℝ, majK2 cϱ p ν (Prod.swap q) = majK2 cϱ p ν q := by
      intro q
      simp only [majK2, Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm |ν q.2|]
      congr 2
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hpre : Prod.swap ⁻¹' S₁ = S₂ := by
      ext ⟨a, b⟩; simp [hS₁, hS₂]
    have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
      have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
      rwa [← Measure.volume_eq_prod] at h
    have hme : MeasurableEmbedding (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
      (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding
    have key := hmp.setIntegral_preimage_emb hme (majK2 cϱ p ν) S₁
    rw [hpre] at key
    simp only [hsymm] at key
    rw [key]
    exact houter1
  -- combine and fold constants
  have htotal : ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ 2 * (p.L ^ 2 * M1
      * M2) := by
    have := hB.trans (add_le_add houter1 houter2)
    linarith
  exact htotal

end Assembly

section Bounds
variable (cϱ lam : ℝ)


/-- **Majorant bound behind 𝓔₂** (§5.3): ∬_{(I×I)ᶜ} L²(Σ_k ψψ')·|ν||ν'| ≤ C·L³B²·l·log l
for T ≥ T₀ — the ν-dependence sits in a nonnegative bilinear kernel (Cauchy–Schwarz
in χ is pushed inside this). -/
theorem calE2_maj_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ C * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
  refine ⟨2 * (12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * CN2 cϱ,
    2 * π * Real.exp 8, fun p F B ν _ hT hF hL2l hνc hν hBl => ?_⟩
  -- regime
  have hπ3 := Real.pi_gt_three
  have he8 : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hT8 : 2 * π * Real.exp 8 ≤ p.T := hT
  have hT1 : (1 : ℝ) ≤ p.T := by nlinarith
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hT2π : 2 * π ≤ p.T := by nlinarith
  have hl8 : (8 : ℝ) ≤ p.l := Setting.le_l_of_T hT8
  have hl1 : (1 : ℝ) ≤ p.l := by linarith
  have hlogl2 : (2 : ℝ) ≤ Real.log p.l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 8 := by norm_num
      _ ≤ p.l := hl8
  have hL8 : (8 : ℝ) ≤ p.L := hF.eight_le_L
  have hL0 : (0 : ℝ) < p.L := by linarith
  have hLl : p.L ≤ 2 * p.l := hL2l
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlogL : Real.log p.L ≤ Real.log p.l + 1 := by
    calc Real.log p.L ≤ Real.log (2 * p.l) := Real.log_le_log hL0 hLl
      _ = Real.log 2 + Real.log p.l := Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log p.l + 1 := by linarith
  have hB1 : (1 : ℝ) ≤ B := le_trans hl1 hBl
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hw1 : (1 : ℝ) ≤ p.w := hF.one_le_w
  have hc4 : (4 : ℝ) ≤ cϱ := hF.four_le_cϱ
  have hm0 : (0 : ℝ) ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hlogl0 : (0 : ℝ) < Real.log p.l := by linarith
  -- fold the N1 constant into log l
  have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.l + 1 := by
    calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
          apply Real.log_le_log (by positivity)
          apply div_le_self (by positivity)
          linarith
      _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
      _ ≤ max 0 (Real.log cϱ) + Real.log p.l + 1 := by
          have := le_max_right (0 : ℝ) (Real.log cϱ)
          linarith
  set M1 : ℝ := (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B with hM1
  have hM1nn : 0 ≤ M1 := by
    rw [hM1]
    have hwle := hF.w_le
    have hlog4w : (0:ℝ) ≤ Real.log (cϱ * p.L / (4 * p.w)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    positivity
  have hM1fold : M1 ≤ ((12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l) * B := by
    rw [hM1]
    have key : 2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ
        ≤ (12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l := by
      have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.l + 1 := hlogbound
      nlinarith [mul_nonneg hm0 (by linarith : (0:ℝ) ≤ Real.log p.l - 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ cϱ) (by linarith : (0:ℝ) ≤ Real.log p.l - 2)]
    exact mul_le_mul_of_nonneg_right key hB0
  -- the 1-D estimates
  have hN1 : ∀ a ∈ Icc p.T (2 * p.T),
      ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ| ≤ M1 :=
    fun a ha => nu_weight_bound hνc hF hν hBl hL2l hT1 ha
  have hN2 := nu_grid_bound hνc hF hν hBl hL2l hT8
  have htotal := setIntegral_compl_sqI_majK2_le hνc hF hν hB1 hT1 hM1nn hN1 hN2
  refine htotal.trans ?_
  have hc60 : (0:ℝ) ≤ CN2 cϱ := CN2_nonneg cϱ
  have hstep : M1 * (CN2 cϱ * (B * (p.L * p.l)))
      ≤ (((12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l) * B)
        * (CN2 cϱ * (B * (p.L * p.l))) := by
    exact mul_le_mul_of_nonneg_right hM1fold (mul_nonneg hc60 (by positivity))
  calc 2 * (p.L ^ 2 * M1 * (CN2 cϱ * (B * (p.L * p.l))))
      = 2 * p.L ^ 2 * (M1 * (CN2 cϱ * (B * (p.L * p.l)))) := by
        ring
    _ ≤ 2 * p.L ^ 2 * ((((12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l) * B)
        * (CN2 cϱ * (B * (p.L * p.l)))) := by
        refine mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 2 * (12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * CN2 cϱ
        * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
        ring

/-- **Majorant bound behind 𝓔₂, L-intrinsic form** (no bandwidth cap; absorbing hypothesis
`L ≤ B`): ∬_{(I×I)ᶜ} majK2(ν) ≤ C·L³B²·(1 + log L)·(L + l) for T ≥ T₀. -/
theorem calE2_maj_bound_L :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → Continuous ν → NuBound p B ν → p.L ≤ B →
      ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q
        ≤ C * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
  refine ⟨2 * (8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * CN2 cϱ,
    2 * π * Real.exp 8, fun p F B ν hT hF hνc hν hBL => ?_⟩
  -- regime
  have hπ3 := Real.pi_gt_three
  have he8 : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hT8 : 2 * π * Real.exp 8 ≤ p.T := hT
  have hT1 : (1 : ℝ) ≤ p.T := by nlinarith
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hT2π : 2 * π ≤ p.T := by nlinarith
  have hl8 : (8 : ℝ) ≤ p.l := Setting.le_l_of_T hT8
  have hl1 : (1 : ℝ) ≤ p.l := by linarith
  have hlogl2 : (2 : ℝ) ≤ Real.log p.l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 8 := by norm_num
      _ ≤ p.l := hl8
  have hL8 : (8 : ℝ) ≤ p.L := hF.eight_le_L
  have hL0 : (0 : ℝ) < p.L := by linarith
  have hlogL0 : (0 : ℝ) ≤ Real.log p.L := Real.log_nonneg (by linarith)
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hw1 : (1 : ℝ) ≤ p.w := hF.one_le_w
  have hc4 : (4 : ℝ) ≤ cϱ := hF.four_le_cϱ
  have hm0 : (0 : ℝ) ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hlogl0 : (0 : ℝ) < Real.log p.l := by linarith
  -- fold the N1 constant into log L
  have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := by
    calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
          apply Real.log_le_log (by positivity)
          apply div_le_self (by positivity)
          linarith
      _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
      _ ≤ max 0 (Real.log cϱ) + Real.log p.L := by
          have := le_max_right (0 : ℝ) (Real.log cϱ)
          linarith
  set M1 : ℝ := (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B with hM1
  have hM1nn : 0 ≤ M1 := by
    rw [hM1]
    have hwle := hF.w_le
    have hlog4w : (0:ℝ) ≤ Real.log (cϱ * p.L / (4 * p.w)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    positivity
  have hM1fold : M1 ≤ ((8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L)) * B := by
    rw [hM1]
    have key : 2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ
        ≤ (8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L) := by
      have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := hlogbound
      nlinarith [mul_nonneg hm0 hlogL0, mul_nonneg (by linarith : (0:ℝ) ≤ cϱ) hlogL0]
    exact mul_le_mul_of_nonneg_right key hB0
  -- the 1-D estimates
  have hN1 : ∀ a ∈ Icc p.T (2 * p.T),
      ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ| ≤ M1 :=
    fun a ha => nu_weight_bound_L hνc hF hν hBL hT1 ha
  have hN2 := nu_grid_bound_L hνc hF hν hBL hT8
  have htotal := setIntegral_compl_sqI_majK2_le hνc hF hν hB1 hT1 hM1nn hN1 hN2
  refine htotal.trans ?_
  have hc60 : (0:ℝ) ≤ CN2 cϱ := CN2_nonneg cϱ
  have hLl0 : 0 ≤ p.L + p.l := by linarith
  have hstep : M1 * (CN2 cϱ * (B * (p.L * (p.L + p.l))))
      ≤ (((8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L)) * B)
        * (CN2 cϱ * (B * (p.L * (p.L + p.l)))) := by
    exact mul_le_mul_of_nonneg_right hM1fold (mul_nonneg hc60 (by positivity))
  calc 2 * (p.L ^ 2 * M1 * (CN2 cϱ * (B * (p.L * (p.L + p.l)))))
      = 2 * p.L ^ 2 * (M1 * (CN2 cϱ * (B * (p.L * (p.L + p.l))))) := by
        ring
    _ ≤ 2 * p.L ^ 2 * ((((8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L)) * B)
        * (CN2 cϱ * (B * (p.L * (p.L + p.l))))) := by
        refine mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 2 * (8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * CN2 cϱ
        * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
        ring


/-- **Bound for E2** (§5.3): |𝓔₂| ≤ C·L³B²·l·log l for T ≥ T₀ (corollary of the
majorant bound via |K²νν'| ≤ majK2). -/
theorem calE2_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      |calE2 p F ν| ≤ C * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
  obtain ⟨C, T₀, h⟩ := calE2_maj_bound cϱ lam
  refine ⟨C, max T₀ (2 * π), fun p F B ν hplam hT hF hL2l hνc hν hBl => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hT2π : 2 * π ≤ p.T := (le_max_right _ _).trans hT
  have hB0 : 0 ≤ B := le_trans (by linarith [hF.one_le_l]) hBl
  refine le_trans ?_ (h p F B ν hplam hT0 hF hL2l hνc hν hBl)
  exact abs_calE2_le_maj hνc hF hν hB0 hT2π

end Bounds

end PrimeSide
end Zeta23
