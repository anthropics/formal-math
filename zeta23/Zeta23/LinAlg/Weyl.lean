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
import Zeta23.LinAlg.Sylvester
import Mathlib.Algebra.Order.Chebyshev

/-!
# Weyl's inequality and the thresholded Cauchy–Schwarz count

Paper §3, `lem:weyl` and `lem:CS`. These are the remaining two linear-algebra
tools (beyond `lem:inertia` and `lem:ranktrace`); they are needed for
Theorems B and C (simple zeros, distinct zeros) but not for Theorem A (2/3 on
the critical line).
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Weyl's eigenvalue perturbation inequality** (the paper's [lem:weyl], §3).
If `A, E` are Hermitian and `θ ≥ ‖E‖_op`, then `n₊^θ(A + E) ≤ n₊(A)`.

Proof in the paper: with eigenvalues in decreasing order, `λᵢ(A+E) ≤ λᵢ(A) + ‖E‖`
(Courant–Fischer). Hence `λᵢ(A+E) > θ ≥ ‖E‖` forces `λᵢ(A) > 0`.

That is the paper's proof. The Lean proof instead takes W := the range of the spectral truncation
(t − θ)⁺ of A + E (so dim W = n₊^θ(A+E)), shows that the Hermitian form of A is positive definite on W
(that of A + E exceeds θ‖x‖² there while that of E is at most θ‖x‖²), and concludes with the subspace
characterization of the positive index (`finrank_le_posIndex_of_posDefOn`, Sylvester.lean); the
hypothesis is stated as |λᵢ(E)| ≤ θ for every eigenvalue of E.
The operator norm `‖E‖_op` is
`Matrix.instNormedRing` (the `linftyOpNorm`), which for Hermitian matrices
equals `max |λᵢ|`. -/
theorem weyl_posIndexAbove_le {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {θ : ℝ}
    (hθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  set hM : (A + E).IsHermitian := hA.add hE
  -- `W := range(specMap hM (·−θ)⁺)` has `dim = posIndexAbove hM θ`
  -- and `hermForm (A+E) x > θ·‖x‖²` on `W ∖ {0}`.
  set W := LinearMap.range (specMap hM (fun t => (t - θ)⁺)).mulVecLin
  have hdimW : Module.finrank 𝕜 W = posIndexAbove hM θ :=
    finrank_range_truncPos hM θ
  have hgt : ∀ x ∈ W, x ≠ 0 → θ * ∑ i, ‖x i‖ ^ 2 < hermForm (A + E) x :=
    hermForm_gt_on_range_truncPos hM θ
  -- `hermForm E x ≤ θ·‖x‖²` always (all `λᵢ(E) ≤ |λᵢ(E)| ≤ θ`).
  have hEle : ∀ x, hermForm E x ≤ θ * ∑ i, ‖x i‖ ^ 2 := by
    intro x
    exact hermForm_le_of_eigenvalues_le hE
      (fun i => (le_abs_self _).trans (hθ i)) x
  -- Hence `A` is positive definite on `W`.
  have hposW : PosDefOn A W := by
    intro x hxW hne
    have h1 := hgt x hxW hne
    have h2 := hEle x
    have h3 : hermForm (A + E) x = hermForm A x + hermForm E x := hermForm_add A E x
    linarith
  -- Hard Sylvester: `dim W ≤ posIndex hA`.
  calc posIndexAbove hM θ
      = Module.finrank 𝕜 W := hdimW.symm
    _ ≤ posIndex hA := finrank_le_posIndex_of_posDefOn hA hposW

/-- **Thresholded Cauchy–Schwarz count** (the paper's [lem:CS], §3).
For Hermitian `R` with `tr R > θ · d`,
  `n₊^θ(R) ≥ (tr R − θd)² / tr(R²)`.

Proof: With `S := ∑_{λᵢ > θ} λᵢ`, note `S ≥ tr R − θd > 0` (negative
eigenvalues only help). By Cauchy–Schwarz, `S² ≤ n₊^θ(R) · ∑_{λᵢ>θ} λᵢ²
≤ n₊^θ(R) · tr(R²)`.

This is a pure real-eigenvalue statement; the proof is Cauchy–Schwarz on the
eigenvalues above the threshold. -/
theorem cauchySchwarz_count {R : Matrix n n 𝕜} (hR : R.IsHermitian)
    {θ : ℝ} (hθ : 0 ≤ θ) (htr : θ * Fintype.card n < rtrace R) :
    (rtrace R - θ * Fintype.card n) ^ 2 / frobSq R
      ≤ (posIndexAbove hR θ : ℝ) := by
  set ev := hR.eigenvalues
  set s : Finset n := {i | θ < ev i} with hs_def
  -- `S := ∑ᵢ∈s evᵢ` satisfies `S ≥ rtrace R − θ·d`, since `∑ᵢ∉s evᵢ ≤ θ·d`.
  have hcompl : ∑ i ∈ sᶜ, ev i ≤ θ * Fintype.card n :=
    calc ∑ i ∈ sᶜ, ev i
        ≤ ∑ _i ∈ sᶜ, θ := by
          refine sum_le_sum fun i hi => ?_
          simp only [hs_def, mem_compl, mem_filter, mem_univ, true_and, not_lt] at hi
          exact hi
      _ = θ * #sᶜ := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ θ * Fintype.card n :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_univ _)) hθ
  have hS : rtrace R - θ * Fintype.card n ≤ ∑ i ∈ s, ev i := by
    have : rtrace R = ∑ i ∈ s, ev i + ∑ i ∈ sᶜ, ev i := by
      rw [rtrace_eq_sum_eigenvalues hR, ← sum_add_sum_compl s]
    linarith
  have hSpos : 0 < ∑ i ∈ s, ev i := lt_of_lt_of_le (by linarith) hS
  -- Cauchy–Schwarz: `S² ≤ #s · ∑ᵢ∈s evᵢ²`.
  have hCS : (∑ i ∈ s, ev i) ^ 2 ≤ #s * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- `∑ᵢ∈s evᵢ² ≤ ∑ᵢ evᵢ² = frobSq R`.
  have hsub : ∑ i ∈ s, (ev i) ^ 2 ≤ frobSq R := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hR]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _ => sq_nonneg _)
  -- `s` is nonempty (else `∑ᵢ∈s evᵢ = 0`, contradicting `hSpos`).
  obtain ⟨i₀, hi₀⟩ := nonempty_of_sum_ne_zero hSpos.ne'
  have hevi₀ : θ < ev i₀ := by simpa [hs_def, mem_filter] using hi₀
  have hfrobpos : 0 < frobSq R :=
    lt_of_lt_of_le
      (lt_of_lt_of_le (pow_pos (hθ.trans_lt hevi₀) 2)
        (single_le_sum (fun i _ => sq_nonneg (ev i)) hi₀))
      hsub
  -- Combine: `(rtrace R − θd)² ≤ S² ≤ #s · ∑ᵢ∈s evᵢ² ≤ #s · frobSq R`.
  have hmain : (rtrace R - θ * Fintype.card n) ^ 2 ≤ #s * frobSq R := calc
    (rtrace R - θ * Fintype.card n) ^ 2
        ≤ (∑ i ∈ s, ev i) ^ 2 := by
          apply sq_le_sq' <;> linarith
    _ ≤ #s * ∑ i ∈ s, (ev i) ^ 2 := hCS
    _ ≤ #s * frobSq R := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
  -- Divide by `frobSq R > 0`.
  rw [div_le_iff₀ hfrobpos]
  simpa [posIndexAbove, hs_def, mul_comm] using hmain

end RHLinalg
