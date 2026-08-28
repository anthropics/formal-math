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
import Zeta23.LinAlg.Sylvester

/-!
# Inertia under pull-back (paper §3, `lem:inertia`)

For a Hermitian form `Q` on `ℂᵐ` and a linear map `𝒜 : U → ℂᵐ`, the positive
index of the pulled-back form `Q ∘ 𝒜` is at most the positive index of `Q`.

## Matrix formulation

If `Q : Matrix m m 𝕜` is Hermitian and `B : Matrix m d 𝕜` represents a linear
map `𝕜ᵈ → 𝕜ᵐ`, then `BᴴQB` is the matrix of the pulled-back form on `𝕜ᵈ`,
and `n₊(BᴴQB) ≤ n₊(Q)`.

## Proof

Via the subspace characterization of `posIndex` (`Sylvester.lean`):
- Let `Vp := range (BᴴQB)₊`, which has dimension `posIndex h(BᴴQB)` and on
  which `BᴴQB` is positive definite (`posDefOn_range_hermPosPart`).
- For `x ∈ Vp ∖ {0}`: `(Bx)ᴴQ(Bx) = xᴴ(BᴴQB)x > 0`, so `Bx ≠ 0`; hence
  `B|_{Vp}` is injective.
- `B(Vp) ⊆ 𝕜ᵐ` has dimension `= dim Vp` and `Q` is positive definite on it.
- By `finrank_le_posIndex_of_posDefOn hQ`, `dim B(Vp) ≤ posIndex hQ`.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]

/-- **Inertia under pull-back** (paper `lem:inertia`, matrix form).
For Hermitian `Q` and any matrix `B`, the pulled-back form `BᴴQB` has
positive index at most that of `Q`. -/
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) ≤ posIndex hQ := by
  set M := Bᴴ * Q * B
  set hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
  -- `Vp := range M₊`, dim = posIndex hM, M pos-def on it.
  set Vp := LinearMap.range (hermPosPart hM).mulVecLin
  have hdimV : Module.finrank 𝕜 Vp = posIndex hM := finrank_range_hermPosPart hM
  have hposV : PosDefOn M Vp := posDefOn_range_hermPosPart hM
  -- `B|_{Vp}` is injective (kernel vector `x ≠ 0` has `(Bx)ᴴQ(Bx) = xᴴMx > 0`,
  -- so `Bx ≠ 0`).
  set LB : (d → 𝕜) →ₗ[𝕜] (m → 𝕜) := B.mulVecLin
  have hinj : Function.Injective (LB.domRestrict Vp) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxV⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : B *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos : 0 < hermForm M x := hposV x hxV hne'
    rw [hermForm_conj Q B x, hxL'] at hpos
    simp [hermForm] at hpos
  -- `B(Vp) ⊆ 𝕜ᵐ` has `Q` pos-def on it.
  have hposBV : PosDefOn Q (LinearMap.range (LB.domRestrict Vp)) := by
    rintro _ ⟨⟨x, hxV⟩, rfl⟩ hne
    simp only [LinearMap.domRestrict_apply, LB, mulVecLin_apply] at *
    have hne' : x ≠ 0 := by
      rintro rfl; apply hne; simp
    rw [← hermForm_conj Q B x]
    exact hposV x hxV hne'
  -- Chain: posIndex hM = dim Vp = dim B(Vp) ≤ posIndex hQ.
  calc posIndex hM
      = Module.finrank 𝕜 Vp := hdimV.symm
    _ = Module.finrank 𝕜 (LinearMap.range (LB.domRestrict Vp)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ posIndex hQ := finrank_le_posIndex_of_posDefOn hQ hposBV

/-- **Subadditivity of the positive index** (paper §3, after `lem:inertia`).
`n₊(Q₁ + Q₂) ≤ n₊(Q₁) + n₊(Q₂)`. -/
theorem posIndex_add_le {Q₁ Q₂ : Matrix m m 𝕜}
    (hQ₁ : Q₁.IsHermitian) (hQ₂ : Q₂.IsHermitian) :
    posIndex (hQ₁.add hQ₂) ≤ posIndex hQ₁ + posIndex hQ₂ := by
  -- Any `(Q₁+Q₂)`-pos-def subspace `Vp` satisfies: `(Q₁)₊ + (Q₂)₊` is
  -- injective on it (same argument as the hard direction, with
  -- `P := (Q₁)₊ + (Q₂)₊` which dominates `Q₁+Q₂`). Hence
  -- `dim Vp ≤ rank((Q₁)₊ + (Q₂)₊) ≤ rank(Q₁)₊ + rank(Q₂)₊`.
  obtain ⟨Vp, hposV, hdimV⟩ := posIndex_eq_max_finrank_posDefOn (hQ₁.add hQ₂)
  rw [← hdimV]
  set P := hermPosPart hQ₁ + hermPosPart hQ₂
  set L : (m → 𝕜) →ₗ[𝕜] (m → 𝕜) := P.mulVecLin
  -- `P − (Q₁+Q₂) = (Q₁)₋ + (Q₂)₋` is PSD, so on `ker P`, `hermForm (Q₁+Q₂) ≤ 0`.
  have hPsub : P - (Q₁ + Q₂) = hermNegPart hQ₁ + hermNegPart hQ₂ := by
    simp only [P, ← hermPosPart_sub_hermNegPart hQ₁, ← hermPosPart_sub_hermNegPart hQ₂]
    abel
  have hPsub_psd : (P - (Q₁ + Q₂)).PosSemidef := by
    rw [hPsub]; exact (hermNegPart_posSemidef hQ₁).add (hermNegPart_posSemidef hQ₂)
  have hinj : Function.Injective (L.domRestrict Vp) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxV⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : P *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hform_le : hermForm (Q₁ + Q₂) x ≤ 0 := by
      have : hermForm (Q₁ + Q₂) x = hermForm P x - hermForm (P - (Q₁ + Q₂)) x := by
        rw [hermForm_sub]; ring
      rw [this, show hermForm P x = 0 by unfold hermForm; rw [hxL']; simp]
      linarith [hermForm_nonneg_of_posSemidef hPsub_psd x]
    exact absurd (hposV x hxV hne') (not_lt.mpr hform_le)
  calc Module.finrank 𝕜 Vp
      = Module.finrank 𝕜 (LinearMap.range (L.domRestrict Vp)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxV⟩, rfl⟩; exact ⟨x, rfl⟩
    _ = P.rank := rfl
    _ ≤ (hermPosPart hQ₁).rank + (hermPosPart hQ₂).rank := by
        -- `rank(A+B) ≤ rank A + rank B` via `range(A+B) ⊆ range A ⊔ range B`.
        unfold Matrix.rank
        refine le_trans (Submodule.finrank_mono ?_)
          (Submodule.finrank_add_le_finrank_add_finrank _ _)
        rintro _ ⟨x, rfl⟩
        simp only [P, mulVecLin_apply, add_mulVec]
        exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    _ = posIndex hQ₁ + posIndex hQ₂ := by rw [rank_hermPosPart, rank_hermPosPart]

end RHLinalg
