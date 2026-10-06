/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.LinAlg.SextuplePenaltyConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Automatic spectral pinching for disjoint principal blocks

This file embeds the eigenbases of disjoint principal coordinate blocks into
the ambient Euclidean space, extends their orthonormal union to an ambient
orthonormal basis, and applies convex spectral pinching for
`RHLinalg.sextuplePenalty`.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset Set
open scoped ComplexOrder InnerProductSpace

namespace RHLinalg
namespace SextupleBlockPinching

variable {𝕜 : Type*} [RCLike 𝕜]
variable {α β ι : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Extension by zero along a coordinate embedding. -/
def coordinateEmbed (e : α ↪ ι) (v : EuclideanSpace 𝕜 α) : EuclideanSpace 𝕜 ι :=
  ∑ a, v a • EuclideanSpace.single (e a) (1 : 𝕜)

@[simp] lemma coordinateEmbed_apply_image (e : α ↪ ι)
    (v : EuclideanSpace 𝕜 α) (a : α) :
    coordinateEmbed e v (e a) = v a := by
  classical
  simp only [coordinateEmbed, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, PiLp.ofLp_single]
  simp_rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp [e.injective.eq_iff]

lemma coordinateEmbed_apply_of_not_mem (e : α ↪ ι)
    (v : EuclideanSpace 𝕜 α) {i : ι} (hi : i ∉ Set.range e) :
    coordinateEmbed e v i = 0 := by
  classical
  have hne : ∀ a, i ≠ e a := fun a h => hi ⟨a, h.symm⟩
  simp only [coordinateEmbed, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, PiLp.ofLp_single]
  simp_rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp [hne]

/-- Extension by zero preserves the inner product. -/
lemma inner_coordinateEmbed (e : α ↪ ι) (v w : EuclideanSpace 𝕜 α) :
    ⟪coordinateEmbed e v, coordinateEmbed e w⟫_𝕜 = ⟪v, w⟫_𝕜 := by
  classical
  have hstd : Orthonormal 𝕜
      (fun a : α => EuclideanSpace.single (e a) (1 : 𝕜)) :=
    EuclideanSpace.orthonormal_single.comp e e.injective
  have h := hstd.inner_sum (fun a => v a) (fun a => w a) Finset.univ
  simpa [coordinateEmbed, PiLp.inner_apply, mul_comm] using h

/-- Vectors supported on disjoint embedded coordinate sets are orthogonal. -/
lemma inner_coordinateEmbed_eq_zero {e₁ e₂ : α ↪ ι}
    (hdisj : ∀ a₁ a₂, e₁ a₁ ≠ e₂ a₂)
    (v w : EuclideanSpace 𝕜 α) :
    ⟪coordinateEmbed e₁ v, coordinateEmbed e₂ w⟫_𝕜 = 0 := by
  classical
  have hne : ∀ a₂ a₁, e₂ a₂ ≠ e₁ a₁ := fun a₂ a₁ => (hdisj a₁ a₂).symm
  simp [coordinateEmbed, inner_sum, sum_inner, PiLp.inner_apply,
    PiLp.single_apply, hne]


/-- The rectangular coordinate-inclusion matrix associated to `e`. -/
def coordinateMatrix (e : α ↪ ι) : Matrix ι α 𝕜 :=
  fun i a => if i = e a then 1 else 0

lemma coordinateMatrix_mulVec (e : α ↪ ι) (v : EuclideanSpace 𝕜 α) :
    coordinateMatrix e *ᵥ (v : α → 𝕜) = (coordinateEmbed e v : ι → 𝕜) := by
  classical
  funext i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    rw [coordinateEmbed_apply_image]
    simp [coordinateMatrix, Matrix.mulVec, dotProduct, e.injective.eq_iff]
  · rw [coordinateEmbed_apply_of_not_mem e v hi]
    have hne : ∀ a, i ≠ e a := fun a h => hi ⟨a, h.symm⟩
    simp [coordinateMatrix, Matrix.mulVec, dotProduct, hne]

/-- Compressing by the coordinate-inclusion matrix selects the corresponding
principal submatrix. -/
lemma coordinateMatrix_compression (M : Matrix ι ι 𝕜) (e : α ↪ ι) :
    (((coordinateMatrix e)ᴴ * M * coordinateMatrix e) : Matrix α α 𝕜) =
      ((fun a b => M (e a) (e b)) : Matrix α α 𝕜) := by
  classical
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (e b)]
  · simp only [coordinateMatrix, if_pos, mul_one]
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (e a)]
    · simp [coordinateMatrix, Matrix.conjTranspose_apply]
    · intro i _ hi
      simp [coordinateMatrix, Matrix.conjTranspose_apply, hi]
    · simp
  · intro i _ hi
    simp [coordinateMatrix, hi]
  · simp

/-- A Hermitian form on an extended-by-zero vector is the form of the
corresponding principal compression. -/
lemma hermForm_coordinateEmbed (M : Matrix ι ι 𝕜) (e : α ↪ ι)
    (v : EuclideanSpace 𝕜 α) :
    hermForm M (coordinateEmbed e v) =
      hermForm ((fun a b => M (e a) (e b)) : Matrix α α 𝕜) v := by
  have h := hermForm_conj M (coordinateMatrix e) (v : α → 𝕜)
  rw [coordinateMatrix_compression (M := M) (e := e)] at h
  rw [coordinateMatrix_mulVec] at h
  exact h.symm

/-- The principal block selected by one fiber of a disjoint coordinate embedding. -/
def principalBlock (M : Matrix ι ι 𝕜) (e : β × α ↪ ι) (b : β) : Matrix α α 𝕜 :=
  fun i j => M (e (b, i)) (e (b, j))

lemma principalBlock_isHermitian {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (e : β × α ↪ ι) (b : β) : (principalBlock M e b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact Matrix.IsHermitian.ext_iff.mp hM (e (b, i)) (e (b, j))

/-- The coordinate embedding of one block. -/
def fiberEmbedding (e : β × α ↪ ι) (b : β) : α ↪ ι where
  toFun i := e (b, i)
  inj' _ _ h := congrArg Prod.snd (e.injective h)

/-- A principal-block eigenvector, extended by zero to ambient coordinates. -/
def embeddedBlockEigenvector {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (e : β × α ↪ ι) (k : β × α) : EuclideanSpace 𝕜 ι :=
  coordinateEmbed (fiberEmbedding e k.1)
    ((principalBlock_isHermitian hM e k.1).eigenvectorBasis k.2)

/-- The union of all embedded principal-block eigenbases is orthonormal. -/
theorem orthonormal_embeddedBlockEigenvector {M : Matrix ι ι 𝕜}
    (hM : M.IsHermitian) (e : β × α ↪ ι) :
    Orthonormal 𝕜 (embeddedBlockEigenvector hM e) := by
  rw [orthonormal_iff_ite]
  rintro ⟨b, j⟩ ⟨b', j'⟩
  by_cases hb : b = b'
  · subst b'
    simp only [embeddedBlockEigenvector]
    rw [inner_coordinateEmbed]
    simpa using (orthonormal_iff_ite.mp
      (principalBlock_isHermitian hM e b).eigenvectorBasis.orthonormal j j')
  · simp only [embeddedBlockEigenvector]
    rw [inner_coordinateEmbed_eq_zero]
    · simp [hb]
    · intro i i' heq
      exact hb (congrArg Prod.fst (e.injective heq))


/-- Each embedded block eigenvector has the Rayleigh value of its principal
block eigenvalue. -/
lemma eigenvalue_eq_hermForm_embeddedBlockEigenvector
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (e : β × α ↪ ι) (k : β × α) :
    (principalBlock_isHermitian hM e k.1).eigenvalues k.2 =
      hermForm M (embeddedBlockEigenvector hM e k) := by
  let hB := principalBlock_isHermitian hM e k.1
  let v := hB.eigenvectorBasis k.2
  calc
    hB.eigenvalues k.2 = hermForm (principalBlock M e k.1) v := by
      simpa only [hermForm] using hB.eigenvalues_eq k.2
    _ = hermForm M (coordinateEmbed (fiberEmbedding e k.1) v) := by
      have hmatrix :
          ((fun a b => M ((fiberEmbedding e k.1) a)
            ((fiberEmbedding e k.1) b)) : Matrix α α 𝕜) =
            principalBlock M e k.1 := by
        rfl
      rw [← hmatrix]
      exact (hermForm_coordinateEmbed M (fiberEmbedding e k.1) v).symm
    _ = hermForm M (embeddedBlockEigenvector hM e k) := by
      rfl

/-- Witness-free convex pinching into the ambient eigenvalue sum for any
finite family of disjoint equal-size principal coordinate blocks. -/
theorem sum_sextuplePenalty_principalBlocks_le_spectrum
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (e : β × α ↪ ι) :
    (∑ k : β × α, sextuplePenalty
      ((principalBlock_isHermitian hM e k.1).eigenvalues k.2))
      ≤ ∑ i, sextuplePenalty (hM.eigenvalues i) := by
  exact sum_sextuplePenalty_orthonormal_family_le_spectrum
    hM e (embeddedBlockEigenvector hM e)
    (orthonormal_embeddedBlockEigenvector hM e)
    (fun k => (principalBlock_isHermitian hM e k.1).eigenvalues k.2)
    (eigenvalue_eq_hermForm_embeddedBlockEigenvector hM e)

/-- Iterated-sum form of principal-block pinching into the ambient spectrum. -/
theorem sum_sum_sextuplePenalty_principalBlocks_le_spectrum
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (e : β × α ↪ ι) :
    (∑ b : β, ∑ j : α, sextuplePenalty
      ((principalBlock_isHermitian hM e b).eigenvalues j))
      ≤ ∑ i, sextuplePenalty (hM.eigenvalues i) := by
  simpa only [Fintype.sum_prod_type] using
    (sum_sextuplePenalty_principalBlocks_le_spectrum hM e)

/-- Witness-free convex pinching for any finite family of disjoint equal-size
principal coordinate blocks. -/
theorem sum_sextuplePenalty_principalBlocks_le_specMap
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (e : β × α ↪ ι) :
    (∑ k : β × α, sextuplePenalty
      ((principalBlock_isHermitian hM e k.1).eigenvalues k.2))
      ≤ rtrace (specMap hM sextuplePenalty) := by
  exact sum_sextuplePenalty_orthonormal_family_le_specMap
    hM e (embeddedBlockEigenvector hM e)
    (orthonormal_embeddedBlockEigenvector hM e)
    (fun k => (principalBlock_isHermitian hM e k.1).eigenvalues k.2)
    (eigenvalue_eq_hermForm_embeddedBlockEigenvector hM e)

/-- Iterated-sum form of automatic principal-block spectral pinching. -/
theorem sum_sum_sextuplePenalty_principalBlocks_le_specMap
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (e : β × α ↪ ι) :
    (∑ b : β, ∑ j : α, sextuplePenalty
      ((principalBlock_isHermitian hM e b).eigenvalues j))
      ≤ rtrace (specMap hM sextuplePenalty) := by
  simpa only [Fintype.sum_prod_type] using
    (sum_sextuplePenalty_principalBlocks_le_specMap hM e)

end SextupleBlockPinching
end RHLinalg

end
