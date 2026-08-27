/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/
import Zeta23.LinAlg.PosIndex
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.Order.Rearrangement

/-!
# Von Neumann's trace inequality

For Hermitian `A, B` with eigenvalues sorted in decreasing order
`a₀ ≥ a₁ ≥ …` and `b₀ ≥ b₁ ≥ …`,

  `Re tr(AB) ≤ ∑ᵢ aᵢ bᵢ`.

## Proof outline

Diagonalise `A = Uₐ Dₐ Uₐᴴ` and `B = Uᵦ Dᵦ Uᵦᴴ`. Setting `W := Uₐᴴ Uᵦ`
(unitary), a direct calculation gives

  `tr(AB) = tr(Dₐ W Dᵦ Wᴴ) = ∑ₖₗ aₖ · ‖Wₖₗ‖² · bₗ`.

The matrix `Sₖₗ := ‖Wₖₗ‖²` is doubly stochastic over `ℝ` (rows and columns
of a unitary matrix are unit vectors). By **Birkhoff–von Neumann**
(`exists_eq_sum_perm_of_mem_doublyStochastic`) every doubly stochastic
matrix is a convex combination of permutation matrices: `S = ∑_σ w_σ P_σ`.
For each permutation `σ`, `∑ₖ aₖ b_{σ k} ≤ ∑ₖ aₖ bₖ` by the **rearrangement
inequality** (`Monovary.sum_mul_comp_perm_le_sum_mul`), since both `a` and
`b` are antitone (hence monovary). Averaging over `σ` with weights `w_σ`
gives the result.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise squared-norm `‖Wᵢⱼ‖²` of a matrix, as a real matrix. -/
def normSqMatrix (W : Matrix n n 𝕜) : Matrix n n ℝ :=
  Matrix.of fun i j => ‖W i j‖ ^ 2

section Bilinear

/-- For a unitary matrix `W`, the entrywise-squared-norm matrix
`(i, j) ↦ ‖Wᵢⱼ‖²` is doubly stochastic over `ℝ`. -/
lemma normSqMatrix_mem_doublyStochastic_of_unitary
    {W : Matrix n n 𝕜} (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    normSqMatrix W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · -- row sum: `∑ⱼ ‖Wᵢⱼ‖² = re (W Wᴴ)ᵢᵢ = re 1 = 1`
    have h : (W * star W) i i = 1 := by rw [Unitary.mul_star_self_of_mem hW]; simp
    have h2 : RCLike.re ((W * star W) i i) = (1 : ℝ) := by rw [h]; simp
    simpa [normSqMatrix, Matrix.mul_apply, star_apply, RCLike.star_def,
      RCLike.mul_conj, map_sum] using h2
  · -- column sum: `∑ᵢ ‖Wᵢⱼ‖² = re (Wᴴ W)ⱼⱼ = re 1 = 1`
    have h : (star W * W) j j = 1 := by rw [Unitary.star_mul_self_of_mem hW]; simp
    have h2 : RCLike.re ((star W * W) j j) = (1 : ℝ) := by rw [h]; simp
    simpa [normSqMatrix, Matrix.mul_apply, star_apply, RCLike.star_def,
      RCLike.conj_mul, map_sum] using h2

/-- For Hermitian `A, B`, writing `W = Uₐᴴ Uᵦ` for the eigenvector unitaries,
`Re tr(AB) = ∑ₖₗ λₖ(A) · ‖Wₖₗ‖² · λₗ(B)`. -/
lemma re_trace_mul_eq_eigenvalue_bilinear {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace =
      ∑ k, ∑ l, hA.eigenvalues k *
        normSqMatrix (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) k l * hB.eigenvalues l := by
  set Ua : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set Ub : Matrix n n 𝕜 := ↑hB.eigenvectorUnitary
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  set W := star Ua * Ub
  have hUaUa : Ua * star Ua = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hUaUa' : star Ua * Ua = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  -- Step 1: `tr(AB) = tr(Dₐ W Dᵦ Wᴴ)` by spectral theorem + trace cycling.
  have hstarW : star Ub * Ua = star W := by
    show star Ub * Ua = star (star Ua * Ub); rw [StarMul.star_mul, star_star]
  have hAB : (A * B).trace = (Da * W * Db * star W).trace := by
    -- `Ua (Da W Db Wᴴ) Uaᴴ = (Ua Da Uaᴴ)(Ub Db Ubᴴ)` since `Ua Uaᴴ = 1`.
    have key : Ua * (Da * W * Db * star W) * star Ua
        = Ua * Da * star Ua * (Ub * Db * star Ub) := by
      have step : Ua * (Da * W * Db * star W) * star Ua
          = Ua * Da * star Ua * (Ub * Db * star Ub) * (Ua * star Ua) := by
        rw [← hstarW]
        show Ua * (Da * (star Ua * Ub) * Db * (star Ub * Ua)) * star Ua = _
        noncomm_ring
      rw [step, hUaUa, mul_one]
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, ← key,
      trace_mul_comm, ← mul_assoc, hUaUa', one_mul]
  -- Step 2: compute `tr(Dₐ W Dᵦ Wᴴ) = ∑ₖₗ aₖ Wₖₗ bₗ W̄ₖₗ`.
  -- Use `diagonal_mul`/`mul_diagonal` to evaluate entries of `Dₐ W Dᵦ`.
  have hentry : (Da * W * Db * star W).trace
      = ∑ k, ∑ l, (hA.eigenvalues k : 𝕜) * (hB.eigenvalues l : 𝕜)
          * (W k l * starRingEnd 𝕜 (W k l)) := by
    unfold Matrix.trace
    simp only [diag_apply]
    refine sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_diagonal, diagonal_mul, star_apply, RCLike.star_def]
    simp only [Function.comp_apply]; ring
  rw [hAB, hentry]
  -- Step 3: take `Re`; identify `z · conj z = ‖z‖²` and push reals.
  simp only [RCLike.mul_conj, map_sum, normSqMatrix, Matrix.of_apply]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  rw [show ((hA.eigenvalues k : 𝕜) * hB.eigenvalues l * (‖W k l‖ : 𝕜) ^ 2 : 𝕜)
        = ((hA.eigenvalues k * hB.eigenvalues l * ‖W k l‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]
  ring

end Bilinear

section Rearrangement

/-- Two antitone functions on a linear order monovary. -/
lemma _root_.Antitone.monovary_antitone {ι α : Type*} [LinearOrder ι] [Preorder α]
    {f g : ι → α} (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  fun _ _ hgij => hf (not_lt.mp fun hij => hgij.not_ge (hg hij.le))

/-- The core combinatorial step: for `a, b : n → ℝ` that monovary and
`S` doubly stochastic, `∑ₖₗ aₖ Sₖₗ bₗ ≤ ∑ₖ aₖ bₖ`.

Proof: `∑ₖₗ aₖ Sₖₗ bₗ = ∑ₖ aₖ (S *ᵥ b)ₖ = a ⬝ (S *ᵥ b)`. By Birkhoff,
`S *ᵥ b = ∑_σ w_σ · (b ∘ σ)` (via `permMatrix_mulVec`). For each `σ`,
`∑ₖ aₖ b(σ k) ≤ ∑ₖ aₖ bₖ` by rearrangement. Average with weights `w_σ`. -/
lemma bilinear_doublyStochastic_le_of_monovary {a b : n → ℝ}
    (hab : Monovary a b) {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ k, ∑ l, a k * S k l * b l ≤ ∑ k, a k * b k := by
  -- LHS `= ∑ₖ aₖ · (S *ᵥ b)ₖ`.
  have hlhs : ∑ k, ∑ l, a k * S k l * b l = ∑ k, a k * (S *ᵥ b) k := by
    simp only [mulVec, dotProduct, mul_sum, mul_assoc]
  rw [hlhs]
  -- Birkhoff: `S = ∑_σ w_σ • P_σ`.
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic hS
  rw [← hw_eq]
  simp only [sum_mulVec, smul_mulVec, permMatrix_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Function.comp_apply, mul_sum]
  rw [sum_comm]
  -- `∑_σ ∑ₖ aₖ · (w_σ · b(σ k)) = ∑_σ w_σ · ∑ₖ aₖ · b(σ k) ≤ ∑ₖ aₖ bₖ`.
  calc ∑ σ : Equiv.Perm n, ∑ k, a k * (w σ * b (σ k))
      = ∑ σ, w σ * ∑ k, a k * b (σ k) := by
        refine sum_congr rfl fun σ _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ ∑ σ, w σ * ∑ k, a k * b k := by
        refine sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (hw_nonneg σ)
        exact hab.sum_mul_comp_perm_le_sum_mul (σ := σ)
    _ = ∑ k, a k * b k := by rw [← sum_mul, hw_sum, one_mul]

end Rearrangement

/-- **Von Neumann's trace inequality** (Hermitian case). For Hermitian `A, B`
with eigenvalues sorted in decreasing order, `Re tr(AB) ≤ ∑ᵢ aᵢ bᵢ`. -/
theorem vonNeumann_trace_ineq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace
      ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  -- Step 1: express `Re tr(AB)` via the bilinear form in `normSqMatrix W`.
  rw [re_trace_mul_eq_eigenvalue_bilinear hA hB]
  set W := star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
    (hB.eigenvectorUnitary : Matrix n n 𝕜)
  have hW : W ∈ Matrix.unitaryGroup n 𝕜 :=
    mul_mem (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary hW
  -- Step 2: reindex `n → Fin (card n)` via the canonical equivalence `e`,
  -- under which `eigenvalues (e k) = eigenvalues₀ k`.
  set e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin _) with he_def
  have hevA : ∀ k, hA.eigenvalues (e k) = hA.eigenvalues₀ k := by
    intro k; simp [Matrix.IsHermitian.eigenvalues, he_def]
  have hevB : ∀ k, hB.eigenvalues (e k) = hB.eigenvalues₀ k := by
    intro k; simp [Matrix.IsHermitian.eigenvalues, he_def]
  -- Reindex both sums by `e`.
  have hre : ∑ k, ∑ l, hA.eigenvalues k * normSqMatrix W k l * hB.eigenvalues l
      = ∑ k, ∑ l, hA.eigenvalues₀ k * normSqMatrix W (e k) (e l) * hB.eigenvalues₀ l := by
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp]
    simp only [hevA, hevB]
  rw [hre]
  -- Step 3: apply the doubly-stochastic bilinear bound.
  refine bilinear_doublyStochastic_le_of_monovary ?_ ?_
  · exact hA.eigenvalues₀_antitone.monovary_antitone hB.eigenvalues₀_antitone
  · -- Reindexed `normSqMatrix W` is still doubly stochastic.
    exact reindex_mem_doublyStochastic (e₁ := e.symm) (e₂ := e.symm) hDS

end RHLinalg
