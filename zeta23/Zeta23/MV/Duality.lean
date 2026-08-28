/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.MV.Spacing
import Zeta23.MV
import Zeta23.LinAlg.HermitianPosPart

/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Zeta23/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

/-- The conclusion of step 3 (`Zeta23.MV.eigen_bound`, Eigen.lean) as a `Prop` with a general
constant: every solution of the normalized eigen-relation with a unit vector has `|μ| ≤ C`. -/
def EigenBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ), Adm freq δ →
    ∀ (u : ι → ℂ), ∑ n, ‖u n‖ ^ 2 = 1 → ∀ (μ : ℝ),
      (∀ m, ∑ n ∈ Finset.univ.erase m,
        ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n
          = (μ : ℂ) * Complex.I * u m) → |μ| ≤ C

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized kernel `k_{rs} = √δ_r √δ_s/(freq r − freq s)`, `0` on the diagonal. -/
def kfun (freq δ : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else Real.sqrt (δ r) * Real.sqrt (δ s) / (freq r - freq s)

omit [Fintype ι] in
lemma kfun_antisymm (freq δ : ι → ℝ) (r s : ι) : kfun freq δ s r = -kfun freq δ r s := by
  unfold kfun
  by_cases h : r = s
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, ← neg_div_neg_eq, neg_sub]; ring

/-- `M := i·K`, a Hermitian complex matrix. -/
def Mmat (freq δ : ι → ℝ) : Matrix ι ι ℂ := fun r s => (kfun freq δ r s : ℂ) * Complex.I

omit [Fintype ι] in
lemma Mmat_isHermitian (freq δ : ι → ℝ) : (Mmat freq δ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun r s => ?_
  simp only [Mmat, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    kfun_antisymm freq δ r s]
  push_cast
  ring

omit [DecidableEq ι] in
/-- `star v ⬝ᵥ v = Σ ‖v_i‖²` (as a complex number). -/
lemma star_dotProduct_self (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- Spectral expansion of the Hermitian form, complex-valued:
`x* A x = Σ_i ν_i ‖(U* x)_i‖²` with `U` the eigenvector unitary. -/
lemma star_dotProduct_mulVec_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x)
      = ((∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  conv_lhs => rw [← RHLinalg.specMap_id hA]
  unfold RHLinalg.specMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def]
  simp only [id, dotProduct, mulVec_diagonal, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul', mul_left_comm]
  rfl

/-- `Σ ‖(U* x)_i‖² = Σ ‖x_i‖²` for the eigenvector unitary `U`. -/
lemma sum_norm_sq_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  have h : star c ⬝ᵥ c = star x ⬝ᵥ x := by
    have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    rw [← hsc, hc_def, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [star_dotProduct_self, star_dotProduct_self] at h
  exact_mod_cast h

/-- Every eigenvalue of `M = iK` has absolute value `≤ C` (step 3 + Mathlib eigenbasis). -/
lemma abs_eigenvalue_le {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (j : ι) :
    |(Mmat_isHermitian freq δ).eigenvalues j| ≤ C := by
  set hM := Mmat_isHermitian freq δ
  set ν : ℝ := hM.eigenvalues j
  set v : ι → ℂ := ⇑(hM.eigenvectorBasis j) with hvdef
  have hv : Mmat freq δ *ᵥ v = ν • v := hM.mulVec_eigenvectorBasis j
  have hunit : ∑ n, ‖v n‖ ^ 2 = 1 := by
    have h1 : ‖hM.eigenvectorBasis j‖ = 1 := hM.eigenvectorBasis.orthonormal.1 j
    rw [← EuclideanSpace.norm_sq_eq, h1, one_pow]
  -- the eigen-relation in `eigen_bound`'s shape, with μ := −ν
  have heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n
        = ((-ν : ℝ) : ℂ) * Complex.I * v m := by
    intro m
    have hm := congrFun hv m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at hm
    -- Σ_s (k m s) I v s = ν v m ; drop the diagonal term (k m m = 0)
    have hsplit : ∑ s, Mmat freq δ m s * v s
        = ∑ s ∈ Finset.univ.erase m, (kfun freq δ m s : ℂ) * Complex.I * v s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
      simp [Mmat, kfun]
    rw [hsplit] at hm
    have hk : ∀ s ∈ Finset.univ.erase m, (kfun freq δ m s : ℂ) * Complex.I * v s
        = Complex.I * (((Real.sqrt (δ m) * Real.sqrt (δ s) / (freq m - freq s) : ℝ) : ℂ) * v s) := by
      intro s hs
      have hsm : m ≠ s := fun e => (Finset.mem_erase.mp hs).1 e.symm
      simp only [kfun, if_neg hsm]; ring
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum] at hm
    -- I * X = ν v_m  ⇒  X = (−ν) I v_m
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    calc ∑ n ∈ Finset.univ.erase m,
          ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n
        = -Complex.I * (Complex.I * ∑ n ∈ Finset.univ.erase m,
            ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * v n) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = -Complex.I * ((ν : ℂ) * v m) := by rw [hm]
      _ = ((-ν : ℝ) : ℂ) * Complex.I * v m := by push_cast; ring
  have := hb ι freq δ h v hunit (-ν) heig
  simpa using this

/-- The Hermitian form of `M` is bounded by `C ‖y‖²`. -/
lemma norm_form_le {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (y : ι → ℂ) :
    ‖star y ⬝ᵥ (Mmat freq δ *ᵥ y)‖ ≤ C * ∑ i, ‖y i‖ ^ 2 := by
  set hM := Mmat_isHermitian freq δ
  rw [star_dotProduct_mulVec_eq hM, Complex.norm_real, Real.norm_eq_abs, ← sum_norm_sq_unitary hM y,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (abs_eigenvalue_le hb h i) (sq_nonneg _)

/-- **Spectral reduction**: an eigenvalue bound `EigenBound C` gives `MVDiag C` — the
Montgomery–Vaughan weighted Hilbert inequality (diagonal / literature form, Zeta23/MV.lean). -/
theorem mvDiag_of_eigenBound {C : ℝ} (hb : EigenBound C) : MVDiag C := by
  intro ι _ _ freq δ x hinj hpos hadm
  have h : Adm freq δ := ⟨hinj, hpos, hadm⟩
  -- y_r := x_r / √δ_r
  set y : ι → ℂ := fun r => x r / (Real.sqrt (δ r) : ℂ) with hydef
  have hsq : ∀ r, (Real.sqrt (δ r) : ℂ) ≠ 0 := fun r => by
    exact_mod_cast (Real.sqrt_pos.mpr (hpos r)).ne'
  have hxy : ∀ r, x r = (Real.sqrt (δ r) : ℂ) * y r := fun r => by
    simp only [hydef]; field_simp [hsq r]
  -- Σ ‖y_r‖² = Σ ‖x_r‖²/δ_r
  have hnorm : ∑ r, ‖y r‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 / δ r := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hydef, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (hpos r).le]
  -- the double sum is rewritten termwise:
  -- Σ_{r,s} [r≠s] x_r x̄_s/(λ_r−λ_s) = Σ_r Σ_s y_r conj(y_s) k_{rs}
  have hterm : ∀ r s, (if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = y r * conj (y s) * (kfun freq δ r s : ℂ) := by
    intro r s
    by_cases hrs : r = s
    · simp [hrs, kfun]
    · rw [if_neg hrs]
      simp only [kfun, if_neg hrs, hxy r, hxy s, map_mul, Complex.conj_ofReal]
      have hf : ((freq r - freq s : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr (fun e => hrs (hinj e))
      push_cast
      field_simp
  have hsum : (∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = conj (star y ⬝ᵥ (Mmat freq δ *ᵥ y)) * Complex.I := by
    simp only [hterm, dotProduct, Matrix.mulVec, Mmat, Pi.star_apply, Complex.star_def, map_sum,
      map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (y r * conj (y s) * (kfun freq δ r s : ℂ)) * this
  rw [hsum, norm_mul, Complex.norm_I, mul_one, Complex.norm_conj, ← hnorm]
  exact norm_form_le hb h y

/-- … hence the bilinear H-MV of `Hypotheses.lean` with constant `2C` (polarization). -/
theorem mvHilbert_of_eigenBound {C : ℝ} (hC : 0 < C) (hb : EigenBound C) :
    ∃ C' : ℝ, 0 < C' ∧ MVHilbert C' :=
  exists_MVHilbert_of_diag ⟨C, hC, mvDiag_of_eigenBound hb⟩

end MV
end Zeta23

end
