/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.LinAlg.RankTrace

/-!
# The sextuple spectral penalty

This file strengthens the rank--trace inequality at `c = 2`.  The scalar
remainder is

`sextuplePenalty x = if x ≤ 2 then (x - 1)² else 2 * x - 3`.

For `p, n ≥ 0`, its defining minimization is

`min_{n ≥ 0} ((p - n)² + 4n) = 2p - 1 + sextuplePenalty p`.

The value `sextuplePenalty 0 = 1` makes the spectral remainder invariant
under padding the nonzero spectrum with zero eigenvalues.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The convex spectral penalty retained by the sextuple rank--trace argument. -/
def sextuplePenalty (x : ℝ) : ℝ :=
  if x ≤ 2 then (x - 1) ^ 2 else 2 * x - 3

@[simp] lemma sextuplePenalty_of_le_two {x : ℝ} (hx : x ≤ 2) :
    sextuplePenalty x = (x - 1) ^ 2 := by
  simp [sextuplePenalty, hx]

lemma sextuplePenalty_of_two_lt {x : ℝ} (hx : 2 < x) :
    sextuplePenalty x = 2 * x - 3 := by
  rw [sextuplePenalty, if_neg (not_le.mpr hx)]

@[simp] lemma sextuplePenalty_zero : sextuplePenalty 0 = 1 := by
  norm_num [sextuplePenalty]

@[simp] lemma sextuplePenalty_one : sextuplePenalty 1 = 0 := by
  norm_num [sextuplePenalty]

@[simp] lemma sextuplePenalty_two : sextuplePenalty 2 = 1 := by
  norm_num [sextuplePenalty]

/-- Expanded identity `sextuplePenalty x = gc 2 x + 1`, kept independent
of the downstream `ZeroSide.RankTraceMult.gc` definition. -/
lemma sextuplePenalty_eq_gc_two (x : ℝ) :
    sextuplePenalty x = x ^ 2 - 2 * x - (max (x - 2) 0) ^ 2 + 1 := by
  by_cases hx : x ≤ 2
  · rw [sextuplePenalty_of_le_two hx, max_eq_right (by linarith)]
    ring
  · rw [sextuplePenalty_of_two_lt (lt_of_not_ge hx), max_eq_left (by linarith)]
    ring

lemma sextuplePenalty_nonneg (x : ℝ) : 0 ≤ sextuplePenalty x := by
  by_cases hx : x ≤ 2
  · rw [sextuplePenalty_of_le_two hx]
    positivity
  · rw [sextuplePenalty_of_two_lt (lt_of_not_ge hx)]
    linarith

/-- The point at which `n ↦ (p - n)² + 4n` attains its minimum on `n ≥ 0`. -/
def sextupleMinimizer (p : ℝ) : ℝ :=
  if p ≤ 2 then 0 else p - 2

lemma sextupleMinimizer_nonneg (p : ℝ) :
    0 ≤ sextupleMinimizer p := by
  by_cases h : p ≤ 2
  · simp [sextupleMinimizer, h]
  · simp [sextupleMinimizer, h]
    linarith

/-- Scalar lower bound behind the refined rank--trace inequality. -/
lemma sextuplePenalty_scalar_lower {p m : ℝ} (hm : 0 ≤ m) :
    2 * p - 1 + sextuplePenalty p ≤ (p - m) ^ 2 + 4 * m := by
  by_cases h : p ≤ 2
  · rw [sextuplePenalty_of_le_two h]
    nlinarith
  · rw [sextuplePenalty_of_two_lt (lt_of_not_ge h)]
    nlinarith [sq_nonneg (m - (p - 2))]

/-- The scalar lower bound is sharp at `sextupleMinimizer p`. -/
lemma sextuplePenalty_scalar_eq_minimizer (p : ℝ) :
    (p - sextupleMinimizer p) ^ 2 + 4 * sextupleMinimizer p
      = 2 * p - 1 + sextuplePenalty p := by
  by_cases h : p ≤ 2
  · rw [sextupleMinimizer, if_pos h, sextuplePenalty_of_le_two h]
    ring
  · rw [sextupleMinimizer, if_neg h,
      sextuplePenalty_of_two_lt (lt_of_not_ge h)]
    ring

/-- Exact scalar minimization, including attainment on the nonnegative half-line. -/
theorem sextuplePenalty_scalar_minimum (p : ℝ) :
    (∀ m : ℝ, 0 ≤ m →
      2 * p - 1 + sextuplePenalty p ≤ (p - m) ^ 2 + 4 * m) ∧
    ∃ m : ℝ, 0 ≤ m ∧
      (p - m) ^ 2 + 4 * m = 2 * p - 1 + sextuplePenalty p := by
  refine ⟨fun m hm => sextuplePenalty_scalar_lower hm,
    sextupleMinimizer p, sextupleMinimizer_nonneg p, ?_⟩
  exact sextuplePenalty_scalar_eq_minimizer p

/-! ### Finite scalar sums -/

section FiniteSums

variable {ι : Type*} [Fintype ι]

/-- Sum of the sharp scalar bounds, in the form used for the negative part of `Q`. -/
lemma sum_sq_diff_sextuplePenalty_lower {p m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) :
    2 * (∑ i, p i) - Fintype.card ι + (∑ i, sextuplePenalty (p i))
        - 4 * (∑ i, m i)
      ≤ ∑ i, (p i - m i) ^ 2 := by
  have hsum : ∑ i, (2 * p i - 1 + sextuplePenalty (p i))
      ≤ ∑ i, ((p i - m i) ^ 2 + 4 * m i) := by
    exact sum_le_sum fun i _ => sextuplePenalty_scalar_lower (hm i)
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
    ← mul_sum] at hsum
  rw [card_univ] at hsum
  linarith

end FiniteSums

/-! ### Spectral remainder and zero padding -/

/-- The dimension-free spectral remainder.  Each zero eigenvalue contributes
`sextuplePenalty 0 - 1 = 0`. -/
def sextupleSpectralRemainder {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℝ :=
  ∑ i, (sextuplePenalty (hA.eigenvalues i) - 1)

/-- The sum of `sextuplePenalty` over the nonzero spectrum, padded with zeros
to a list of length `r`.  The rank hypothesis in applications guarantees that
such a padding exists. -/
def paddedSextuplePenalty {A : Matrix n n 𝕜} (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  r + sextupleSpectralRemainder hA

/-- Adding one zero to a padded spectrum adds `sextuplePenalty 0 = 1`. -/
lemma paddedSextuplePenalty_succ {A : Matrix n n 𝕜} (hA : A.IsHermitian) (r : ℕ) :
    paddedSextuplePenalty hA (r + 1) = paddedSextuplePenalty hA r + sextuplePenalty 0 := by
  simp [paddedSextuplePenalty]
  ring_nf

lemma paddedSextuplePenalty_add {A : Matrix n n 𝕜} (hA : A.IsHermitian) (r k : ℕ) :
    paddedSextuplePenalty hA (r + k) = paddedSextuplePenalty hA r + k := by
  simp [paddedSextuplePenalty]
  ring

/-- Padding to the ambient dimension is the ordinary spectral sum. -/
lemma paddedSextuplePenalty_card {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    paddedSextuplePenalty hA (Fintype.card n)
      = ∑ i, sextuplePenalty (hA.eigenvalues i) := by
  simp only [paddedSextuplePenalty, sextupleSpectralRemainder,
    sum_sub_distrib, sum_const, nsmul_eq_mul]
  rw [card_univ]
  ring

/-- Matrix-functional form of the dimension-free spectral remainder. -/
lemma sextupleSpectralRemainder_eq_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    sextupleSpectralRemainder hA
      = rtrace (specMap hA sextuplePenalty) - Fintype.card n := by
  rw [rtrace_specMap]
  simp only [sextupleSpectralRemainder, sum_sub_distrib, sum_const, nsmul_eq_mul]
  rw [card_univ]
  ring


/-- The contribution from the nonzero eigenvalues only. -/
def nonzeroSextuplePenalty {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℝ :=
  ∑ i with hA.eigenvalues i ≠ 0, sextuplePenalty (hA.eigenvalues i)

/-- Removing zero eigenvalues changes the raw penalty sum by exactly the rank.
This is the formal zero-padding identity behind `paddedSextuplePenalty`. -/
lemma sextupleSpectralRemainder_eq_nonzero_sub_rank {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    sextupleSpectralRemainder hA = nonzeroSextuplePenalty hA - A.rank := by
  classical
  let s : Finset n := {i | hA.eigenvalues i ≠ 0}
  have hsum : ∑ i, (sextuplePenalty (hA.eigenvalues i) - 1)
      = ∑ i ∈ s, (sextuplePenalty (hA.eigenvalues i) - 1) := by
    symm
    refine sum_subset (subset_univ s) ?_
    intro i _ hi
    have hz : hA.eigenvalues i = 0 := by
      by_contra hne
      exact hi (by simp [s, hne])
    simp [hz]
  rw [sextupleSpectralRemainder, hsum, nonzeroSextuplePenalty,
    sum_sub_distrib, sum_const, nsmul_eq_mul]
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  simp [s]

/-- The canonical padded sum is the nonzero spectral sum plus one for each
of the `r - rank A` padding zeros.  Only `rank A ≤ r` is required. -/
lemma paddedSextuplePenalty_eq_nonzero_add {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {r : ℕ} (hr : A.rank ≤ r) :
    paddedSextuplePenalty hA r
      = nonzeroSextuplePenalty hA + (r - A.rank : ℕ) := by
  rw [paddedSextuplePenalty, sextupleSpectralRemainder_eq_nonzero_sub_rank]
  rw [Nat.cast_sub hr]
  ring

/-- A genuine zero-padded penalty sum is nonnegative. -/
lemma paddedSextuplePenalty_nonneg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {r : ℕ} (hr : A.rank ≤ r) :
    0 ≤ paddedSextuplePenalty hA r := by
  rw [paddedSextuplePenalty_eq_nonzero_add hA hr]
  exact add_nonneg
    (sum_nonneg fun i _ => sextuplePenalty_nonneg _)
    (Nat.cast_nonneg _)

/-! ### Refined rank--trace inequality -/

/-- The strongest dimension-free form of the refined rank--trace inequality.
It retains the complete scalar remainder and needs no rank bound on `P`. -/
theorem rank_trace_ineq_sextuple_remainder {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ)
        + sextupleSpectralRemainder hP.isHermitian
      ≤ frobSq (P + Q) := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  have hpenaltyP : sextupleSpectralRemainder hP.isHermitian
      = (∑ k, sextuplePenalty (p k)) - d := by
    unfold sextupleSpectralRemainder
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ,
      sum_eigenvalues_reindex hP.isHermitian sextuplePenalty]
    simp [p, d]
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq
      rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]
      simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef hP hQp_psd
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstepVN : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k) ^ 2 - 2 * ∑ k, p k * m k + ∑ k, (m k) ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]
    linarith
  have hstepPenalty :
      2 * rtrace P + sextupleSpectralRemainder hP.isHermitian - 4 * rtrace Qm
        ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm, hpenaltyP]
    have hs := sum_sq_diff_sextuplePenalty_lower (p := p) (m := m) hm_nn
    simp [d] at hs
    linarith
  have hstepQp : 4 * rtrace Qp - 4 * (b : ℝ) ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    have hcard : #{i | (hQ.eigenvalues i)⁺ ≠ 0} ≤ b := by
      calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
          = #{i | 0 < hQ.eigenvalues i} := by
            congr 1
            ext i
            simp [posPart_eq_zero, not_le]
        _ ≤ b := hb
    have h := sum_sq_lower_of_card_pos_le hcard (2 : ℝ)
    norm_num at h ⊢
    exact h
  have htraceQ : 4 * rtrace Q = 4 * rtrace Qp - 4 * rtrace Qm := by
    rw [hQdec, rtrace_sub]
    ring
  linarith [hstepVN, hstepPenalty, hstepQp, hPQp, hexpand, htraceQ]

/-- Ambient-dimension spectral-sum form of the refined inequality. -/
theorem rank_trace_ineq_two_sextuplePenalty_spectrum {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P - Fintype.card n + 4 * rtrace Q - 4 * (b : ℝ)
        + (∑ i, sextuplePenalty (hP.isHermitian.eigenvalues i))
      ≤ frobSq (P + Q) := by
  have h := rank_trace_ineq_sextuple_remainder hP hQ hb
  rw [← paddedSextuplePenalty_card hP.isHermitian]
  unfold paddedSextuplePenalty at *
  linarith

/-- Matrix-functional form, with the penalty applied by spectral calculus. -/
theorem rank_trace_ineq_two_sextuplePenalty_specMap {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P - Fintype.card n + 4 * rtrace Q - 4 * (b : ℝ)
        + rtrace (specMap hP.isHermitian sextuplePenalty)
      ≤ frobSq (P + Q) := by
  have h := rank_trace_ineq_sextuple_remainder hP hQ hb
  rw [sextupleSpectralRemainder_eq_specMap] at h
  linarith

/-- Refined `c = 2` rank--trace inequality in the same `P/Q/r/b` interface as
`rank_trace_ineq_two`.  The last term is the spectrum of `P`, padded by zeros
to length `r`. -/
theorem rank_trace_ineq_two_sextuplePenalty {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (_hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P - r + 4 * rtrace Q - 4 * (b : ℝ)
        + paddedSextuplePenalty hP.isHermitian r
      ≤ frobSq (P + Q) := by
  have h := rank_trace_ineq_sextuple_remainder hP hQ hb
  unfold paddedSextuplePenalty
  linarith

/-- Rearranged form, directly extending `rank_trace_ineq_two`. -/
theorem rank_trace_ineq_two_sextuplePenalty_rearranged {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (P + Q)
        + paddedSextuplePenalty hP.isHermitian r
      ≤ r := by
  have h := rank_trace_ineq_two_sextuplePenalty hP hQ hr hb
  linarith

end RHLinalg
