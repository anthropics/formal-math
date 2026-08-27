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

/-!
# Positive and negative parts of a Hermitian matrix

For a Hermitian matrix `Q` with spectral decomposition `Q = U diag(λ) Uᴴ`,
define `Q₊ := U diag(λ⁺) Uᴴ` and `Q₋ := U diag(λ⁻) Uᴴ` where
`λ⁺ = max(λ,0)`, `λ⁻ = max(−λ,0)`.

Then `Q = Q₊ − Q₋`, both are PSD, `Q₊ Q₋ = 0`, and `rank Q₊ = n₊(Q)`.

This is equivalent to the CFC `Q⁺`/`Q⁻` via `Matrix.IsHermitian.cfc_eq`, but
the direct spectral construction keeps the eigenvalue bookkeeping explicit,
which is what the rank–trace proof needs.
-/

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a real function to a Hermitian matrix via its spectral decomposition:
`specMap hA f := U diag(f ∘ λ) Uᴴ`. (This is `Matrix.IsHermitian.cfc`, reproduced
here to keep imports light and bookkeeping explicit.) -/
def specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    (diagonal (fun i => (f (hA.eigenvalues i) : 𝕜)))

lemma specMap_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (specMap hA f).IsHermitian := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  refine isHermitian_mul_mul_conjTranspose _ ?_
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp [RCLike.star_def])

lemma specMap_id {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA id = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

lemma specMap_sub {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA (f - g) = specMap hA f - specMap hA g := by
  unfold specMap
  rw [← map_sub]
  congr 1
  simp only [← diagonal_sub, Pi.sub_apply, RCLike.ofReal_sub]

lemma specMap_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA (f * g) = specMap hA f * specMap hA g := by
  unfold specMap
  rw [← map_mul, diagonal_mul_diagonal]
  simp only [Pi.mul_apply, RCLike.ofReal_mul]

lemma specMap_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA 0 = 0 := by
  unfold specMap; simp

/-- The Hermitian form `xᴴ(specMap hA f)x` in eigenbasis coordinates:
setting `c := Uᴴx`, we have `Re(xᴴ(specMap hA f)x) = ∑ᵢ f(λᵢ)·‖cᵢ‖²`. -/
lemma hermForm_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (specMap hA f *ᵥ x))
      = ∑ i, f (hA.eigenvalues i) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  -- `xᴴ U D Uᴴ x = cᴴ D c` where `c = Uᴴ x`, since `star x ᵥ* U = star c`.
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  unfold specMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def,
    show star c ⬝ᵥ (diagonal (fun i => (f (hA.eigenvalues i) : 𝕜)) *ᵥ c)
      = ∑ i, (f (hA.eigenvalues i) : 𝕜) * (starRingEnd 𝕜 (c i) * c i) by
      simp only [dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def]
      exact sum_congr rfl fun i _ => by ring]
  simp only [RCLike.conj_mul, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show ((f (hA.eigenvalues i) : 𝕜) * (‖c i‖ : 𝕜) ^ 2 : 𝕜)
      = ((f (hA.eigenvalues i) * ‖c i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]

/-- The real-valued trace of `specMap hA f` is `∑ᵢ f(λᵢ)`. -/
lemma rtrace_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtrace (specMap hA f) = ∑ i, f (hA.eigenvalues i) := by
  unfold specMap rtrace
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul,
    trace_diagonal]
  simp

/-- The squared Frobenius norm of `specMap hA f` is `∑ᵢ f(λᵢ)²`. -/
lemma frobSq_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    frobSq (specMap hA f) = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
  unfold frobSq
  rw [(specMap_isHermitian hA f).eq, ← specMap_mul,
    show (f * f : ℝ → ℝ) = fun x => (f x) ^ 2 from funext fun x => by
      simp only [Pi.mul_apply, sq]]
  exact rtrace_specMap hA _

/-- The rank of `specMap hA f` is the number of `i` with `f(λᵢ) ≠ 0`. -/
lemma rank_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (specMap hA f).rank = #{i | f (hA.eigenvalues i) ≠ 0} := by
  have hdet : IsUnit (hA.eigenvectorUnitary : Matrix n n 𝕜).det :=
    Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary
  have hdet' : IsUnit (star (hA.eigenvectorUnitary : Matrix n n 𝕜)).det := by
    rw [show star (hA.eigenvectorUnitary : Matrix n n 𝕜)
        = (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ from rfl, det_conjTranspose]
    exact hdet.star
  unfold specMap
  rw [conjStarAlgAut_apply,
    rank_mul_eq_left_of_isUnit_det _ _ hdet',
    rank_mul_eq_right_of_isUnit_det _ _ hdet,
    rank_diagonal]
  simp only [ne_eq, RCLike.ofReal_eq_zero, Fintype.card_subtype]

/-- `specMap hA f` is PSD whenever `f(λᵢ) ≥ 0` for all `i`. -/
lemma specMap_posSemidef {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (specMap hA f).PosSemidef := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  refine (PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg (K := 𝕜) |>.mpr (hf i)

section PosNegPart

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- Positive part `A₊ := U diag(λ⁺) Uᴴ`. -/
def hermPosPart : Matrix n n 𝕜 := specMap hA (·⁺)

/-- Negative part `A₋ := U diag(λ⁻) Uᴴ`. -/
def hermNegPart : Matrix n n 𝕜 := specMap hA (·⁻)

lemma hermPosPart_sub_hermNegPart : hermPosPart hA - hermNegPart hA = A := by
  unfold hermPosPart hermNegPart
  rw [← specMap_sub, show ((·⁺) - (·⁻) : ℝ → ℝ) = id from
    funext fun x => posPart_sub_negPart x, specMap_id]

lemma hermPosPart_posSemidef : (hermPosPart hA).PosSemidef :=
  specMap_posSemidef hA fun _ => posPart_nonneg _

lemma hermNegPart_posSemidef : (hermNegPart hA).PosSemidef :=
  specMap_posSemidef hA fun _ => negPart_nonneg _

private lemma real_posPart_mul_negPart (x : ℝ) : x⁺ * x⁻ = 0 := by
  rcases le_total 0 x with h | h
  · simp [negPart_eq_zero.mpr h]
  · simp [posPart_eq_zero.mpr h]

lemma hermPosPart_mul_hermNegPart : hermPosPart hA * hermNegPart hA = 0 := by
  unfold hermPosPart hermNegPart
  rw [← specMap_mul, show ((·⁺) * (·⁻) : ℝ → ℝ) = 0 from
    funext fun x => real_posPart_mul_negPart x, specMap_zero]

lemma hermNegPart_mul_hermPosPart : hermNegPart hA * hermPosPart hA = 0 := by
  unfold hermPosPart hermNegPart
  rw [← specMap_mul, show ((·⁻) * (·⁺) : ℝ → ℝ) = 0 from
    funext fun x => by rw [Pi.mul_apply, mul_comm]; exact real_posPart_mul_negPart x,
    specMap_zero]

lemma rank_hermPosPart : (hermPosPart hA).rank = posIndex hA := by
  unfold hermPosPart posIndex
  rw [rank_specMap]
  congr 1; ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero, not_le]

lemma rtrace_hermPosPart : rtrace (hermPosPart hA) = ∑ i, (hA.eigenvalues i)⁺ :=
  rtrace_specMap hA _

lemma rtrace_hermNegPart : rtrace (hermNegPart hA) = ∑ i, (hA.eigenvalues i)⁻ :=
  rtrace_specMap hA _

lemma rtrace_sub_decomp : rtrace A = rtrace (hermPosPart hA) - rtrace (hermNegPart hA) := by
  conv_lhs => rw [← hermPosPart_sub_hermNegPart hA]
  simp [rtrace, trace_sub, map_sub]

lemma frobSq_hermPosPart : frobSq (hermPosPart hA) = ∑ i, ((hA.eigenvalues i)⁺) ^ 2 :=
  frobSq_specMap hA _

lemma frobSq_hermNegPart : frobSq (hermNegPart hA) = ∑ i, ((hA.eigenvalues i)⁻) ^ 2 :=
  frobSq_specMap hA _

end PosNegPart

end RHLinalg
