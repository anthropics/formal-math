/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.LinAlg.SextuplePenalty
import Zeta23.LinAlg.Sylvester
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Convexity and pinching for the sextuple spectral penalty

The sextuple penalty is convex.  On the nonnegative half-line it is
`2`-Lipschitz.  The final section gives the doubly-stochastic and unitary
eigenbasis forms of trace pinching used by finite block decompositions.
-/

noncomputable section

open Matrix Finset Set
open scoped ComplexOrder

namespace RHLinalg

/-- A subgradient of `sextuplePenalty`. -/
def sextuplePenaltySlope (x : ℝ) : ℝ :=
  if x ≤ 2 then 2 * (x - 1) else 2

lemma sextuplePenaltySlope_of_le_two {x : ℝ} (hx : x ≤ 2) :
    sextuplePenaltySlope x = 2 * (x - 1) := by
  simp [sextuplePenaltySlope, hx]

lemma sextuplePenaltySlope_of_two_lt {x : ℝ} (hx : 2 < x) :
    sextuplePenaltySlope x = 2 := by
  rw [sextuplePenaltySlope, if_neg (not_le.mpr hx)]

/-- The selected slope supports the graph globally. -/
lemma sextuplePenalty_support (x y : ℝ) :
    sextuplePenalty x + sextuplePenaltySlope x * (y - x) ≤ sextuplePenalty y := by
  by_cases hx : x ≤ 2
  · rw [sextuplePenaltySlope_of_le_two hx, sextuplePenalty_of_le_two hx]
    by_cases hy : y ≤ 2
    · rw [sextuplePenalty_of_le_two hy]
      nlinarith [sq_nonneg (y - x)]
    · have hy' : 2 < y := lt_of_not_ge hy
      rw [sextuplePenalty_of_two_lt hy']
      have hprod : 0 ≤ (2 - x) * (y - 2) :=
        mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy'.le)
      nlinarith [sq_nonneg (2 - x)]
  · have hx' : 2 < x := lt_of_not_ge hx
    rw [sextuplePenaltySlope_of_two_lt hx', sextuplePenalty_of_two_lt hx']
    by_cases hy : y ≤ 2
    · rw [sextuplePenalty_of_le_two hy]
      nlinarith [sq_nonneg (y - 2)]
    · rw [sextuplePenalty_of_two_lt (lt_of_not_ge hy)]
      ring_nf
      exact le_refl (-3 + y * 2 : ℝ)

/-- `sextuplePenalty` is convex (in fact, the proof gives global convexity). -/
theorem convexOn_sextuplePenalty : ConvexOn ℝ (Ici (0 : ℝ)) sextuplePenalty := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a * x + b * y
  have hx := sextuplePenalty_support z x
  have hy := sextuplePenalty_support z y
  have hax := mul_le_mul_of_nonneg_left hx ha
  have hby := mul_le_mul_of_nonneg_left hy hb
  have hcombine := add_le_add hax hby
  have hz : sextuplePenalty z =
      a * (sextuplePenalty z + sextuplePenaltySlope z * (x - z))
        + b * (sextuplePenalty z + sextuplePenaltySlope z * (y - z)) := by
    have hb' : b = 1 - a := by linarith
    dsimp [z]
    rw [hb']
    ring
  rw [← hz] at hcombine
  simpa [smul_eq_mul, z] using hcombine

lemma sextuplePenaltySlope_mem_Icc {x : ℝ} (hx : 0 ≤ x) :
    sextuplePenaltySlope x ∈ Icc (-2 : ℝ) 2 := by
  by_cases h : x ≤ 2
  · rw [sextuplePenaltySlope_of_le_two h]
    constructor <;> linarith
  · rw [sextuplePenaltySlope_of_two_lt (lt_of_not_ge h)]
    exact ⟨by norm_num, le_rfl⟩

private lemma abs_sextuplePenalty_sub_le_of_le {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    |sextuplePenalty x - sextuplePenalty y| ≤ 2 * |x - y| := by
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  have hsx := sextuplePenaltySlope_mem_Icc hx
  have hsy := sextuplePenaltySlope_mem_Icc hy
  have hsupport_xy := sextuplePenalty_support x y
  have hsupport_yx := sextuplePenalty_support y x
  have hmulx := mul_le_mul_of_nonneg_right hsx.1 (sub_nonneg.mpr hxy)
  have hmuly := mul_le_mul_of_nonneg_right hsy.2 (sub_nonneg.mpr hxy)
  rw [abs_le]
  constructor <;> nlinarith

/-- The pointwise `2`-Lipschitz estimate on the nonnegative half-line. -/
theorem abs_sextuplePenalty_sub_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |sextuplePenalty x - sextuplePenalty y| ≤ 2 * |x - y| := by
  rcases le_total x y with hxy | hyx
  · exact abs_sextuplePenalty_sub_le_of_le hx hy hxy
  · calc
      |sextuplePenalty x - sextuplePenalty y|
          = |sextuplePenalty y - sextuplePenalty x| := abs_sub_comm _ _
      _ ≤ 2 * |y - x| := abs_sextuplePenalty_sub_le_of_le hy hx hyx
      _ = 2 * |x - y| := by rw [abs_sub_comm]


/-- Standard metric-space form of the Lipschitz estimate. -/
theorem lipschitzOnWith_sextuplePenalty :
    LipschitzOnWith 2 sextuplePenalty (Ici (0 : ℝ)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  simp only [Set.mem_Ici] at hx hy
  simpa [Real.dist_eq] using abs_sextuplePenalty_sub_le x y hx hy

/-! ### Jensen and doubly-stochastic majorization -/

/-- Finite Jensen inequality in the exact weighted form used for spectral pinching. -/
theorem sextuplePenalty_sum_le {ι : Type*} (s : Finset ι) (w μ : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) :
    sextuplePenalty (∑ i ∈ s, w i * μ i)
      ≤ ∑ i ∈ s, w i * sextuplePenalty (μ i) := by
  set xbar := ∑ i ∈ s, w i * μ i with hxbar
  have hzero : ∑ i ∈ s, w i * (μ i - xbar) = 0 := by
    calc
      ∑ i ∈ s, w i * (μ i - xbar)
          = (∑ i ∈ s, w i * μ i) - ∑ i ∈ s, w i * xbar := by
              rw [← sum_sub_distrib]
              exact sum_congr rfl fun i _ => by ring
      _ = xbar - (∑ i ∈ s, w i) * xbar := by rw [hxbar, sum_mul]
      _ = 0 := by rw [hw1]; ring
  have havg : ∑ i ∈ s,
      w i * (sextuplePenalty xbar + sextuplePenaltySlope xbar * (μ i - xbar))
        = sextuplePenalty xbar := by
    calc
      ∑ i ∈ s,
          w i * (sextuplePenalty xbar + sextuplePenaltySlope xbar * (μ i - xbar))
          = (∑ i ∈ s, w i) * sextuplePenalty xbar
              + sextuplePenaltySlope xbar * ∑ i ∈ s, w i * (μ i - xbar) := by
                simp_rw [mul_add]
                rw [sum_add_distrib, sum_mul, mul_sum]
                congr 1
                exact sum_congr rfl fun i _ => by ring
      _ = sextuplePenalty xbar := by rw [hw1, hzero]; ring
  rw [← havg]
  exact sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (sextuplePenalty_support xbar (μ i)) (hw i hi)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Rectangular substochastic majorization.  Row sums are one; column sums may
be at most one because unused orthogonal directions have been discarded. -/
theorem sum_sextuplePenalty_rectangular_mulVec_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Matrix κ ι ℝ)
    (hSnonneg : ∀ k i, 0 ≤ S k i)
    (hSrow : ∀ k, ∑ i, S k i = 1)
    (hScol : ∀ i, ∑ k, S k i ≤ 1)
    (μ : ι → ℝ) :
    ∑ k, sextuplePenalty ((S *ᵥ μ) k) ≤ ∑ i, sextuplePenalty (μ i) := by
  calc
    ∑ k, sextuplePenalty ((S *ᵥ μ) k)
        ≤ ∑ k, ∑ i, S k i * sextuplePenalty (μ i) := by
          exact sum_le_sum fun k _ => by
            rw [mulVec, dotProduct]
            exact sextuplePenalty_sum_le univ (S k) μ
              (fun i _ => hSnonneg k i) (hSrow k)
    _ = ∑ i, (∑ k, S k i) * sextuplePenalty (μ i) := by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => by rw [← sum_mul]
    _ ≤ ∑ i, sextuplePenalty (μ i) := by
      exact sum_le_sum fun i _ => by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hScol i) (sextuplePenalty_nonneg (μ i))


/-- Karamata/Jensen for a doubly-stochastic matrix.  This is the scalar
majorization form of trace pinching. -/
theorem sum_sextuplePenalty_mulVec_le {S : Matrix ι ι ℝ}
    (hS : S ∈ doublyStochastic ℝ ι) (μ : ι → ℝ) :
    ∑ j, sextuplePenalty ((S *ᵥ μ) j) ≤ ∑ i, sextuplePenalty (μ i) := by
  rw [mem_doublyStochastic_iff_sum] at hS
  rcases hS with ⟨hSnonneg, hSrow, hScol⟩
  calc
    ∑ j, sextuplePenalty ((S *ᵥ μ) j)
        ≤ ∑ j, ∑ i, S j i * sextuplePenalty (μ i) := by
          exact sum_le_sum fun j _ => by
            rw [mulVec, dotProduct]
            exact sextuplePenalty_sum_le univ (S j) μ
              (fun i _ => hSnonneg j i) (hSrow j)
    _ = ∑ i, sextuplePenalty (μ i) := by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => by
        rw [← sum_mul, hScol i, one_mul]

/-- Eigenbasis-overlap form: squared entries of a unitary matrix give the
required doubly-stochastic barycentric weights. -/
theorem sum_sextuplePenalty_normSqMatrix_mulVec_le
    {𝕜 : Type*} [RCLike 𝕜] {W : Matrix ι ι 𝕜}
    (hW : W ∈ unitaryGroup ι 𝕜) (μ : ι → ℝ) :
    ∑ j, sextuplePenalty ((normSqMatrix W *ᵥ μ) j)
      ≤ ∑ i, sextuplePenalty (μ i) :=
  sum_sextuplePenalty_mulVec_le
    (normSqMatrix_mem_doublyStochastic_of_unitary hW) μ


/-! ### Diagonal and eigenbasis pinching -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A diagonal entry is a doubly-stochastic barycenter of the eigenvalues. -/
lemma re_diag_eq_normSqMatrix_mulVec {M : Matrix ι ι 𝕜}
    (hM : M.IsHermitian) (j : ι) :
    RCLike.re (M j j)
      = (normSqMatrix (hM.eigenvectorUnitary : Matrix ι ι 𝕜) *ᵥ hM.eigenvalues) j := by
  set U : Matrix ι ι 𝕜 := ↑hM.eigenvectorUnitary with hU
  have hMjj : M j j = ∑ i,
      U j i * (hM.eigenvalues i : 𝕜) * starRingEnd 𝕜 (U j i) := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_diagonal, star_apply, RCLike.star_def]
    simp only [Function.comp_apply]
    rfl
  rw [hMjj, map_sum]
  simp only [mulVec, dotProduct]
  refine sum_congr rfl fun i _ => ?_
  rw [show U j i * (hM.eigenvalues i : 𝕜) * starRingEnd 𝕜 (U j i)
        = (hM.eigenvalues i : 𝕜) * (U j i * starRingEnd 𝕜 (U j i)) by ring,
    RCLike.mul_conj,
    show ((hM.eigenvalues i : 𝕜) * ((‖U j i‖ : 𝕜) ^ 2) : 𝕜)
        = ((hM.eigenvalues i * ‖U j i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]
  simp [normSqMatrix, mul_comm]

/-- Rank-one trace pinching (Schur majorization): the sum of penalties of the
diagonal compressions is at most the spectral penalty of the whole matrix. -/
theorem sum_sextuplePenalty_diag_le_spectrum {M : Matrix ι ι 𝕜}
    (hM : M.IsHermitian) :
    ∑ j, sextuplePenalty (RCLike.re (M j j))
      ≤ ∑ i, sextuplePenalty (hM.eigenvalues i) := by
  calc
    ∑ j, sextuplePenalty (RCLike.re (M j j))
        = ∑ j, sextuplePenalty
            ((normSqMatrix (hM.eigenvectorUnitary : Matrix ι ι 𝕜)
              *ᵥ hM.eigenvalues) j) := by
                exact sum_congr rfl fun j _ => by
                  rw [re_diag_eq_normSqMatrix_mulVec hM j]
    _ ≤ ∑ i, sextuplePenalty (hM.eigenvalues i) :=
      sum_sextuplePenalty_normSqMatrix_mulVec_le hM.eigenvectorUnitary.2 _

/-- Matrix-functional version of rank-one trace pinching. -/
theorem sum_sextuplePenalty_diag_le_specMap {M : Matrix ι ι 𝕜}
    (hM : M.IsHermitian) :
    ∑ j, sextuplePenalty (RCLike.re (M j j))
      ≤ rtrace (specMap hM sextuplePenalty) := by
  rw [rtrace_specMap]
  exact sum_sextuplePenalty_diag_le_spectrum hM


/-- Diagonal entries after an arbitrary change of orthonormal basis are
barycenters of the original eigenvalues. -/
lemma re_diag_unitary_conj_eq_normSqMatrix_mulVec {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (U : Matrix ι ι 𝕜) (j : ι) :
    RCLike.re ((star U * A * U) j j)
      = (normSqMatrix
          (star U * (hA.eigenvectorUnitary : Matrix ι ι 𝕜)) *ᵥ hA.eigenvalues) j := by
  set E : Matrix ι ι 𝕜 := (hA.eigenvectorUnitary : Matrix ι ι 𝕜)
  set W : Matrix ι ι 𝕜 := star U * E
  have hstarW : star W = star E * U := by
    simp [W, StarMul.star_mul]
  have hconj : star U * A * U =
      W * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star W := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hstarW]
    simp only [W, E]
    noncomm_ring
  have hentry : (star U * A * U) j j = ∑ i,
      W j i * (hA.eigenvalues i : 𝕜) * starRingEnd 𝕜 (W j i) := by
    rw [hconj, Matrix.mul_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_diagonal, star_apply, RCLike.star_def]
    simp only [Function.comp_apply]
  rw [hentry, map_sum]
  simp only [mulVec, dotProduct]
  refine sum_congr rfl fun i _ => ?_
  rw [show W j i * (hA.eigenvalues i : 𝕜) * starRingEnd 𝕜 (W j i)
        = (hA.eigenvalues i : 𝕜) * (W j i * starRingEnd 𝕜 (W j i)) by ring,
    RCLike.mul_conj,
    show ((hA.eigenvalues i : 𝕜) * ((‖W j i‖ : 𝕜) ^ 2) : 𝕜)
        = ((hA.eigenvalues i * ‖W j i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]
  simp [normSqMatrix, W, E, mul_comm]

/-- Unitary-eigenbasis form of trace pinching.  A union of orthonormal
principal-block eigenbases is one such `U`. -/
theorem sum_sextuplePenalty_unitary_conj_diagonal_le_spectrum
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜) :
    ∑ j, sextuplePenalty (RCLike.re ((star U * A * U) j j))
      ≤ ∑ i, sextuplePenalty (hA.eigenvalues i) := by
  set W : Matrix ι ι 𝕜 :=
    star U * (hA.eigenvectorUnitary : Matrix ι ι 𝕜)
  have hW : W ∈ unitaryGroup ι 𝕜 :=
    mul_mem (Unitary.star_mem hU) hA.eigenvectorUnitary.2
  calc
    ∑ j, sextuplePenalty (RCLike.re ((star U * A * U) j j))
        = ∑ j, sextuplePenalty ((normSqMatrix W *ᵥ hA.eigenvalues) j) := by
            exact sum_congr rfl fun j _ => by
              rw [re_diag_unitary_conj_eq_normSqMatrix_mulVec hA U j]
    _ ≤ ∑ i, sextuplePenalty (hA.eigenvalues i) :=
      sum_sextuplePenalty_normSqMatrix_mulVec_le hW _

/-- Explicit eigenbasis witness form.  To prove a block pinching inequality,
assemble the block eigenvectors as the columns of `U` and instantiate `ev` with
the concatenated block spectra. -/
theorem sum_sextuplePenalty_le_specMap_of_unitary_diagonal
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜)
    (ev : ι → ℝ)
    (hdiag : ∀ j, ev j = RCLike.re ((star U * A * U) j j)) :
    ∑ j, sextuplePenalty (ev j) ≤ rtrace (specMap hA sextuplePenalty) := by
  rw [rtrace_specMap]
  simpa only [hdiag] using
    (sum_sextuplePenalty_unitary_conj_diagonal_le_spectrum hA hU)


/-- Partial eigenbasis witness form.  The embedding lists only the block
eigenvectors; nonnegative penalties of the unused orthonormal columns are
discarded. -/
theorem sum_sextuplePenalty_unitary_diagonal_embedding_le_spectrum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜)
    (e : κ ↪ ι) (ev : κ → ℝ)
    (hdiag : ∀ k, ev k = RCLike.re ((star U * A * U) (e k) (e k))) :
    ∑ k, sextuplePenalty (ev k) ≤ ∑ i, sextuplePenalty (hA.eigenvalues i) := by
  let g : ι → ℝ := fun j => sextuplePenalty (RCLike.re ((star U * A * U) j j))
  have himage : ∑ k, sextuplePenalty (ev k) = ∑ j ∈ univ.image e, g j := by
    calc
      ∑ k, sextuplePenalty (ev k) = ∑ k, g (e k) := by
        exact sum_congr rfl fun k _ => by simp [g, hdiag k]
      _ = ∑ j ∈ univ.image e, g j := by
        symm
        rw [sum_image]
        exact fun _ _ _ _ h => e.injective h
  rw [himage]
  exact le_trans
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ =>
      sextuplePenalty_nonneg _)
    (sum_sextuplePenalty_unitary_conj_diagonal_le_spectrum hA hU)

/-- Matrix-functional version of the partial eigenbasis witness theorem. -/
theorem sum_sextuplePenalty_le_specMap_of_unitary_diagonal_embedding
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜)
    (e : κ ↪ ι) (ev : κ → ℝ)
    (hdiag : ∀ k, ev k = RCLike.re ((star U * A * U) (e k) (e k))) :
    ∑ k, sextuplePenalty (ev k) ≤ rtrace (specMap hA sextuplePenalty) := by
  rw [rtrace_specMap]
  exact sum_sextuplePenalty_unitary_diagonal_embedding_le_spectrum
    hA hU e ev hdiag


/-! ### Completing an orthonormal compression family -/

/-- Complete an orthonormal family already assigned to a subset of the ambient
column labels, and return its coordinate matrix in the standard basis. -/
theorem exists_unitary_matrix_extension
    {v : ι → EuclideanSpace 𝕜 ι} {s : Set ι}
    (hv : Orthonormal 𝕜 (s.domRestrict v)) :
    ∃ U : Matrix ι ι 𝕜, U ∈ unitaryGroup ι 𝕜 ∧
      ∀ j ∈ s, (fun i => U i j) = (v j : ι → 𝕜) := by
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := 𝕜) (ι := ι))
  let std := EuclideanSpace.basisFun ι 𝕜
  let U : Matrix ι ι 𝕜 := std.toBasis.toMatrix b
  refine ⟨U, std.toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  intro j hj
  funext i
  change ((EuclideanSpace.basisFun ι 𝕜).repr (b j)) i = (v j) i
  rw [hb j hj]
  rfl

/-- The diagonal of `Uᴴ A U` is the Hermitian form of `A` on the columns of
`U`. -/
lemma re_diag_conj_eq_hermForm_column (A U : Matrix ι ι 𝕜) (j : ι) :
    RCLike.re ((star U * A * U) j j) = hermForm A (fun i => U i j) := by
  have h := hermForm_conj A U (Pi.single j (1 : 𝕜))
  have hleft : hermForm (Uᴴ * A * U) (Pi.single j (1 : 𝕜))
      = RCLike.re ((Uᴴ * A * U) j j) := by
    simp [hermForm]
  rw [hleft, Matrix.mulVec_single_one] at h
  change RCLike.re ((Uᴴ * A * U) j j) = hermForm A (U.col j)
  exact h

/-- Complete an abstract orthonormal family into ambient unitary columns at
the positions selected by an embedding. -/
theorem exists_unitary_matrix_extension_embedding
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ↪ ι) (v : κ → EuclideanSpace 𝕜 ι)
    (hv : Orthonormal 𝕜 v) :
    ∃ U : Matrix ι ι 𝕜, U ∈ unitaryGroup ι 𝕜 ∧
      ∀ k, U.col (e k) = (v k : ι → 𝕜) := by
  let vExt : ι → EuclideanSpace 𝕜 ι := Function.extend e v (fun _ => 0)
  let er : κ ≃ Set.range e := Equiv.ofInjective e e.injective
  have hfun : (Set.range e).domRestrict vExt = v ∘ er.symm := by
    funext j
    have hj : e (er.symm j) = j.1 := by
      change (er (er.symm j)).val = j.val
      exact congrArg Subtype.val (er.apply_symm_apply j)
    change vExt j.1 = v (er.symm j)
    rw [← hj]
    exact e.injective.extend_apply v (fun _ => 0) (er.symm j)
  have hvRange : Orthonormal 𝕜 ((Set.range e).domRestrict vExt) := by
    rw [hfun]
    exact hv.comp er.symm er.symm.injective
  obtain ⟨U, hU, hcol⟩ := exists_unitary_matrix_extension hvRange
  refine ⟨U, hU, fun k => ?_⟩
  have hrange : e k ∈ Set.range e := ⟨k, rfl⟩
  have hk := hcol (e k) hrange
  have hvext : vExt (e k) = v k := by
    exact e.injective.extend_apply v (fun _ => 0) k
  rw [hvext] at hk
  exact hk

/-- Witness-free trace compression for an orthonormal family.  The family may
be smaller than the ambient dimension; completion and unused-column disposal
are internal to the proof. -/
theorem sum_sextuplePenalty_orthonormal_hermForm_le_spectrum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (e : κ ↪ ι) (v : κ → EuclideanSpace 𝕜 ι)
    (hv : Orthonormal 𝕜 v) :
    ∑ k, sextuplePenalty (hermForm A (v k))
      ≤ ∑ i, sextuplePenalty (hA.eigenvalues i) := by
  obtain ⟨U, hU, hcol⟩ := exists_unitary_matrix_extension_embedding e v hv
  apply sum_sextuplePenalty_unitary_diagonal_embedding_le_spectrum
    hA hU e (fun k => hermForm A (v k))
  intro k
  rw [re_diag_conj_eq_hermForm_column]
  exact congrArg (hermForm A) (hcol k).symm

/-- Eigenvalue-labelled form of orthonormal-family trace compression. -/
theorem sum_sextuplePenalty_orthonormal_family_le_spectrum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (e : κ ↪ ι) (v : κ → EuclideanSpace 𝕜 ι)
    (hv : Orthonormal 𝕜 v) (ev : κ → ℝ)
    (hev : ∀ k, ev k = hermForm A (v k)) :
    ∑ k, sextuplePenalty (ev k)
      ≤ ∑ i, sextuplePenalty (hA.eigenvalues i) := by
  simpa only [hev] using
    (sum_sextuplePenalty_orthonormal_hermForm_le_spectrum hA e v hv)

/-- Matrix-functional form of orthonormal-family trace compression. -/
theorem sum_sextuplePenalty_orthonormal_family_le_specMap
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (e : κ ↪ ι) (v : κ → EuclideanSpace 𝕜 ι)
    (hv : Orthonormal 𝕜 v) (ev : κ → ℝ)
    (hev : ∀ k, ev k = hermForm A (v k)) :
    ∑ k, sextuplePenalty (ev k) ≤ rtrace (specMap hA sextuplePenalty) := by
  rw [rtrace_specMap]
  exact sum_sextuplePenalty_orthonormal_family_le_spectrum hA e v hv ev hev

end RHLinalg
