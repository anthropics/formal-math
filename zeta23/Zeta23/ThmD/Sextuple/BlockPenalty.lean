/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Energy
import Zeta23.LinAlg.SextuplePenaltyConvex

/-!
# Spectral penalty of a six-point Gram block

This file proves the corrected local spectral leaf.  For a positive-semidefinite
six-by-six matrix of trace at most six, the sextuple spectral penalty controls
the smaller of its off-diagonal energy and `6 / 5`.  It does not assert the
false untruncated global energy domination.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23.ThmD.Sextuple

/-- Off-diagonal Hilbert--Schmidt energy, counted once in each orientation. -/
def offDiagEnergy (M : Matrix (Fin 6) (Fin 6) ℂ) : ℝ :=
  2 * ∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·), ‖M i j‖ ^ 2

/-- The spectral penalty of a Hermitian six-by-six block. -/
def blockSpectralPenalty {M : Matrix (Fin 6) (Fin 6) ℂ}
    (hM : M.IsHermitian) : ℝ :=
  ∑ i, RHLinalg.sextuplePenalty (hM.eigenvalues i)

private lemma frobSq_eq_sum_norm_sq (A : Matrix (Fin 6) (Fin 6) ℂ) :
    RHLinalg.frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold RHLinalg.frobSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

private lemma norm_sq_transpose_eq (M : Matrix (Fin 6) (Fin 6) ℂ)
    (hM : M.IsHermitian) (i j : Fin 6) :
    ‖M j i‖ ^ 2 = ‖M i j‖ ^ 2 := by
  have hij := hM.apply i j
  rw [← hij, norm_star]

/-- The off-diagonal energy is bounded by the centered Frobenius norm. -/
lemma offDiagEnergy_le_frobSq_sub_one
    {M : Matrix (Fin 6) (Fin 6) ℂ} (hM : M.IsHermitian) :
    offDiagEnergy M ≤ RHLinalg.frobSq (M - 1) := by
  let f : Fin 6 → Fin 6 → ℝ := fun i j => ‖M i j‖ ^ 2
  have hswap :
      (∑ i : Fin 6, ∑ j : Fin 6, if j < i then f i j else 0) =
        ∑ i : Fin 6, ∑ j : Fin 6, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · simp [hij, f, norm_sq_transpose_eq M hM]
    · simp [hij]
  have henergy : offDiagEnergy M =
      ∑ i : Fin 6, ∑ j : Fin 6,
        ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
    unfold offDiagEnergy
    simp_rw [Finset.sum_filter]
    rw [show (2 : ℝ) * (∑ i : Fin 6, ∑ j : Fin 6,
        if i < j then f i j else 0) =
        (∑ i : Fin 6, ∑ j : Fin 6, if i < j then f i j else 0) +
        ∑ i : Fin 6, ∑ j : Fin 6, if i < j then f i j else 0 by ring]
    nth_rewrite 2 [← hswap]
    simp only [sum_add_distrib]
  rw [henergy, frobSq_eq_sum_norm_sq]
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [hij, not_lt_of_ge hij.le, f, hij.ne]
  · subst j
    simp [f]
  · simp [hij, not_lt_of_ge hij.le, f, hij.ne']

private lemma frobSq_sub_one_eq_sum_sq_eigenvalues_sub_one
    {M : Matrix (Fin 6) (Fin 6) ℂ} (hM : M.IsHermitian) :
    RHLinalg.frobSq (M - 1) = ∑ i, (hM.eigenvalues i - 1) ^ 2 := by
  have hcross : RCLike.re ((M * (-1 : Matrix (Fin 6) (Fin 6) ℂ)).trace) =
      -RHLinalg.rtrace M := by
    simp [RHLinalg.rtrace]
  have hone : RHLinalg.frobSq (-1 : Matrix (Fin 6) (Fin 6) ℂ) = 6 := by
    rw [frobSq_eq_sum_norm_sq]
    calc
      (∑ i : Fin 6, ∑ j : Fin 6,
          ‖(-1 : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ^ 2) =
          ∑ _i : Fin 6, (1 : ℝ) := by
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji.symm]
        · simp
      _ = 6 := by norm_num [Fintype.card_fin]
  have hcenter : RHLinalg.frobSq (M - 1) =
      RHLinalg.frobSq M - 2 * RHLinalg.rtrace M + 6 := by
    rw [sub_eq_add_neg, RHLinalg.frobSq_add_hermitian hM
      Matrix.isHermitian_one.neg, hcross, hone]
    ring
  have hexpand : (∑ i, (hM.eigenvalues i - 1) ^ 2) =
      (∑ i, hM.eigenvalues i ^ 2) - 2 * (∑ i, hM.eigenvalues i) + 6 := by
    calc
      (∑ i, (hM.eigenvalues i - 1) ^ 2) =
          ∑ i, (hM.eigenvalues i ^ 2 - 2 * hM.eigenvalues i + 1) := by
        exact sum_congr rfl fun i _ => by ring
      _ = (∑ i, hM.eigenvalues i ^ 2) - 2 * (∑ i, hM.eigenvalues i) + 6 := by
        rw [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum]
        norm_num [Fintype.card_fin]
  rw [hcenter, RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hM,
    RHLinalg.rtrace_eq_sum_eigenvalues hM]
  exact hexpand.symm

private lemma blockSpectralPenalty_eq_frobSq_sub_one_of_eigenvalues_le_two
    {M : Matrix (Fin 6) (Fin 6) ℂ} (hM : M.IsHermitian)
    (hle : ∀ i, hM.eigenvalues i ≤ 2) :
    blockSpectralPenalty hM = RHLinalg.frobSq (M - 1) := by
  rw [blockSpectralPenalty, frobSq_sub_one_eq_sum_sq_eigenvalues_sub_one hM]
  exact sum_congr rfl fun i _ => RHLinalg.sextuplePenalty_of_le_two (hle i)



private lemma card_strictUpperPairs_fin_six :
    (∑ i : Fin 6, (Finset.univ.filter (i < ·)).card) = 15 := by
  decide

private lemma one_twentyfifth_le_sextuplePenalty_of_mem_interval
    {x : ℝ} (_hx0 : 0 ≤ x) (hx4 : x ≤ 4 / 5) :
    (1 / 25 : ℝ) ≤ RHLinalg.sextuplePenalty x := by
  rw [RHLinalg.sextuplePenalty_of_le_two (by linarith)]
  have h₁ : 0 ≤ 4 / 5 - x := by linarith
  have h₂ : 0 ≤ 6 / 5 - x := by linarith
  nlinarith [mul_nonneg h₁ h₂]

private lemma six_fifths_le_blockSpectralPenalty_of_eigenvalue_gt_two
    {M : Matrix (Fin 6) (Fin 6) ℂ} (hM : M.PosSemidef)
    (htrace : RHLinalg.rtrace M ≤ 6) (k : Fin 6)
    (hk : 2 < hM.isHermitian.eigenvalues k) :
    (6 / 5 : ℝ) ≤ blockSpectralPenalty hM.isHermitian := by
  let hH := hM.isHermitian
  let μ : Fin 6 → ℝ := hH.eigenvalues
  let s : Finset (Fin 6) := Finset.univ.erase k
  let other : ℝ := ∑ i ∈ s, μ i
  let avg : ℝ := (1 / 5 : ℝ) * other
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => hM.eigenvalues_nonneg i
  have hother0 : 0 ≤ other := by
    exact sum_nonneg fun i _ => hμ0 i
  have hsum : other + μ k = ∑ i, μ i := by
    dsimp [other, s]
    exact Finset.sum_erase_add Finset.univ μ (Finset.mem_univ k)
  have htrace_eigs : (∑ i, μ i) ≤ 6 := by
    rw [← RHLinalg.rtrace_eq_sum_eigenvalues hH]
    exact htrace
  have hother4 : other ≤ 4 := by
    change 2 < μ k at hk
    linarith
  have havg0 : 0 ≤ avg := by
    dsimp [avg]
    positivity
  have havg4 : avg ≤ 4 / 5 := by
    dsimp [avg]
    nlinarith
  have hcard : s.card = 5 := by
    simp [s, Fintype.card_fin]
  have hweights : (∑ i ∈ s, (1 / 5 : ℝ)) = 1 := by
    rw [sum_const, nsmul_eq_mul, hcard]
    norm_num
  have hJ₀ := RHLinalg.sextuplePenalty_sum_le s
    (fun _ : Fin 6 => (1 / 5 : ℝ)) μ
    (fun _ _ => by norm_num) hweights
  have hJ : RHLinalg.sextuplePenalty avg ≤
      (1 / 5 : ℝ) * ∑ i ∈ s, RHLinalg.sextuplePenalty (μ i) := by
    simpa [avg, other, Finset.mul_sum] using hJ₀
  have havgPenalty : (1 / 25 : ℝ) ≤ RHLinalg.sextuplePenalty avg :=
    one_twentyfifth_le_sextuplePenalty_of_mem_interval havg0 havg4
  have hotherPenalty : (1 / 5 : ℝ) ≤
      ∑ i ∈ s, RHLinalg.sextuplePenalty (μ i) := by
    nlinarith
  have hkPenalty : (1 : ℝ) ≤ RHLinalg.sextuplePenalty (μ k) := by
    rw [RHLinalg.sextuplePenalty_of_two_lt hk]
    linarith
  have hsplitPenalty :
      (∑ i ∈ s, RHLinalg.sextuplePenalty (μ i)) +
          RHLinalg.sextuplePenalty (μ k) = blockSpectralPenalty hH := by
    change (∑ i ∈ s, RHLinalg.sextuplePenalty (μ i)) +
      RHLinalg.sextuplePenalty (μ k) =
        ∑ i, RHLinalg.sextuplePenalty (μ i)
    simpa only [s] using
      (Finset.sum_erase_add Finset.univ
        (fun i => RHLinalg.sextuplePenalty (μ i)) (Finset.mem_univ k))
  linarith

/-- Corrected spectral leaf for a positive-semidefinite six-by-six block.
The truncation by `6 / 5` is essential. -/
theorem min_offDiagEnergy_six_fifths_le_blockSpectralPenalty
    {M : Matrix (Fin 6) (Fin 6) ℂ} (hM : M.PosSemidef)
    (htrace : RHLinalg.rtrace M ≤ 6) :
    min (offDiagEnergy M) (6 / 5 : ℝ) ≤
      blockSpectralPenalty hM.isHermitian := by
  by_cases hle : ∀ i, hM.isHermitian.eigenvalues i ≤ 2
  · calc
      min (offDiagEnergy M) (6 / 5 : ℝ) ≤ offDiagEnergy M := min_le_left _ _
      _ ≤ RHLinalg.frobSq (M - 1) :=
        offDiagEnergy_le_frobSq_sub_one hM.isHermitian
      _ = blockSpectralPenalty hM.isHermitian :=
        (blockSpectralPenalty_eq_frobSq_sub_one_of_eigenvalues_le_two
          hM.isHermitian hle).symm
  · simp only [not_forall, not_le] at hle
    obtain ⟨k, hk⟩ := hle
    exact (min_le_right _ _).trans
      (six_fifths_le_blockSpectralPenalty_of_eigenvalue_gt_two hM htrace k hk)




/-- Entrywise stability of the off-diagonal energy.  There are fifteen
unordered pairs, each square changes by at most `2 * ε`, and the energy counts
both orientations. -/
lemma sextupleEnergy_le_offDiagEnergy_add_error
    (M : Matrix (Fin 6) (Fin 6) ℂ) (g : Fin 5 → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hclose : ∀ i j, i < j →
      ‖M i j - (sextupleGram g i j : ℂ)‖ ≤ ε)
    (hactual : ∀ i j, i < j → ‖M i j‖ ≤ 1)
    (hideal : ∀ i j, i < j → |sextupleGram g i j| ≤ 1) :
    sextupleEnergy g ≤ offDiagEnergy M + 60 * ε := by
  have hpoint : ∀ i j, i < j →
      (sextupleGram g i j) ^ 2 ≤ ‖M i j‖ ^ 2 + 2 * ε := by
    intro i j hij
    let a : ℝ := |sextupleGram g i j|
    let b : ℝ := ‖M i j‖
    have ha0 : 0 ≤ a := abs_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have ha1 : a ≤ 1 := hideal i j hij
    have hb1 : b ≤ 1 := hactual i j hij
    have habs : |b - a| ≤ ε := by
      calc
        |b - a| = |‖M i j‖ - ‖(sextupleGram g i j : ℂ)‖| := by
          simp [a, b, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖M i j - (sextupleGram g i j : ℂ)‖ :=
          abs_norm_sub_norm_le _ _
        _ ≤ ε := hclose i j hij
    have hdiff : a - b ≤ ε := by
      calc
        a - b ≤ |a - b| := le_abs_self _
        _ = |b - a| := abs_sub_comm _ _
        _ ≤ ε := habs
    have hsum0 : 0 ≤ a + b := add_nonneg ha0 hb0
    have hmul₁ : (a - b) * (a + b) ≤ ε * (a + b) :=
      mul_le_mul_of_nonneg_right hdiff hsum0
    have hsum1 : a + b ≤ 2 := by linarith
    have hmul₂ : ε * (a + b) ≤ ε * 2 :=
      mul_le_mul_of_nonneg_left hsum1 hε
    rw [← sq_abs (sextupleGram g i j)]
    change a ^ 2 ≤ b ^ 2 + 2 * ε
    nlinarith
  unfold sextupleEnergy offDiagEnergy
  have hsum :
      (∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·),
          (sextupleGram g i j) ^ 2) ≤
        ∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·),
          (‖M i j‖ ^ 2 + 2 * ε) := by
    exact sum_le_sum fun i _ => sum_le_sum fun j hj =>
      hpoint i j (by simpa using hj)
  have hcount :
      (∑ i : Fin 6, ∑ _j ∈ Finset.univ.filter (i < ·), (2 * ε : ℝ)) =
        30 * ε := by
    simp only [sum_const, nsmul_eq_mul]
    have hcardR :
        (∑ i : Fin 6, ((Finset.univ.filter (i < ·)).card : ℝ)) = 15 := by
      exact_mod_cast card_strictUpperPairs_fin_six
    rw [← Finset.sum_mul, hcardR]
    ring
  calc
    2 * (∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·),
        (sextupleGram g i j) ^ 2) ≤
        2 * (∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·),
          (‖M i j‖ ^ 2 + 2 * ε)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * (∑ i : Fin 6, ∑ j ∈ Finset.univ.filter (i < ·),
          ‖M i j‖ ^ 2) + 60 * ε := by
      simp only [sum_add_distrib]
      rw [hcount]
      ring


/-- Error-stable affine block bound.  The low-energy branch transfers the
ideal kernel certificate entrywise; the high-energy branch uses the corrected
`6 / 5` spectral floor. -/
theorem blockAffine_of_entrywise_close
    {M : Matrix (Fin 6) (Fin 6) ℂ} (hM : M.PosSemidef)
    (htrace : RHLinalg.rtrace M ≤ 6) (g : Fin 5 → ℝ)
    {A B ε : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hg : ∀ i, 0 ≤ g i) (hA : A ≤ 6 / 5)
    (hcert : A ≤ sextupleEnergy g + B * sextupleSpan g)
    (hclose : ∀ i j, i < j →
      ‖M i j - (sextupleGram g i j : ℂ)‖ ≤ ε)
    (hactual : ∀ i j, i < j → ‖M i j‖ ≤ 1)
    (hideal : ∀ i j, i < j → |sextupleGram g i j| ≤ 1) :
    A ≤ blockSpectralPenalty hM.isHermitian + B * sextupleSpan g + 60 * ε := by
  have hspan : 0 ≤ sextupleSpan g := by
    exact Finset.sum_nonneg fun i _ => hg i
  have hBspan : 0 ≤ B * sextupleSpan g := mul_nonneg hB hspan
  have htransfer := sextupleEnergy_le_offDiagEnergy_add_error
    M g ε hε hclose hactual hideal
  have hmin := min_offDiagEnergy_six_fifths_le_blockSpectralPenalty hM htrace
  rcases le_total (offDiagEnergy M) (6 / 5 : ℝ) with hlow | hhigh
  · rw [min_eq_left hlow] at hmin
    linarith
  · rw [min_eq_right hhigh] at hmin
    linarith


end Zeta23.ThmD.Sextuple

end
