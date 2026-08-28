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
import Zeta23.LinAlg.HermitianPosPart
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Sylvester's law of inertia for Hermitian matrices (subspace bound)

We prove the key inequality: any subspace `W ⊆ 𝕜ⁿ` on which the Hermitian
form `x ↦ Re(xᴴAx)` is positive definite has dimension at most
`posIndex hA`.

The proof is short: `A = A₊ − A₋` with both parts PSD (`HermitianPosPart`).
If `A₊ · x = 0` for `x ∈ W ∖ {0}`, then `xᴴAx = −xᴴA₋x ≤ 0`, contradicting
positive-definiteness on `W`. So `(A₊ *ᵥ ·)|_W` is injective, hence
`dim W ≤ rank A₊ = posIndex hA`.

This is the engine behind `lem:inertia`: pulling back a Hermitian form
cannot increase its positive index.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian form `x ↦ Re(star x ⬝ (A *ᵥ x))` associated to a matrix. -/
def hermForm (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ (A *ᵥ x))

/-- `W` is a subspace on which `hermForm A` is positive definite. -/
def PosDefOn (A : Matrix n n 𝕜) (W : Submodule 𝕜 (n → 𝕜)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermForm A x

omit [DecidableEq n] in
lemma hermForm_conj {m : Type*} [Fintype m] [DecidableEq m]
    (Q : Matrix n n 𝕜) (B : Matrix n m 𝕜) (x : m → 𝕜) :
    hermForm (Bᴴ * Q * B) x = hermForm Q (B *ᵥ x) := by
  unfold hermForm
  congr 2
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star x) Bᴴ,
    ← star_mulVec]

omit [DecidableEq n] in
lemma hermForm_add (A B : Matrix n n 𝕜) (x : n → 𝕜) :
    hermForm (A + B) x = hermForm A x + hermForm B x := by
  unfold hermForm
  simp [add_mulVec, dotProduct_add, map_add]

omit [DecidableEq n] in
lemma hermForm_sub (A B : Matrix n n 𝕜) (x : n → 𝕜) :
    hermForm (A - B) x = hermForm A x - hermForm B x := by
  unfold hermForm
  simp [sub_mulVec, dotProduct_sub, map_sub]

omit [DecidableEq n] in
/-- `hermForm A x ≥ 0` when `A` is PSD. -/
lemma hermForm_nonneg_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (x : n → 𝕜) : 0 ≤ hermForm A x :=
  hA.re_dotProduct_nonneg x

/-- **Sylvester's inequality (hard direction)**: any subspace on which the
Hermitian form is positive definite has dimension at most `posIndex hA`.

This is the subspace characterization of `n₊` that makes `lem:inertia`
trivial. -/
theorem finrank_le_posIndex_of_posDefOn {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {W : Submodule 𝕜 (n → 𝕜)} (hW : PosDefOn A W) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  -- `A₊ *ᵥ ·` is injective on `W`: kernel element has `xᴴAx = −xᴴA₋x ≤ 0`.
  set L : (n → 𝕜) →ₗ[𝕜] (n → 𝕜) := (hermPosPart hA).mulVecLin
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    -- `hxL : L ⟨x, hxW⟩ = 0`, i.e. `hermPosPart hA *ᵥ x = 0`.
    have hxL' : hermPosPart hA *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hAx : hermForm A x ≤ 0 := by
      rw [← hermPosPart_sub_hermNegPart hA, hermForm_sub]
      have h1 : hermForm (hermPosPart hA) x = 0 := by
        unfold hermForm; rw [hxL']; simp
      have h2 : 0 ≤ hermForm (hermNegPart hA) x :=
        hermForm_nonneg_of_posSemidef (hermNegPart_posSemidef hA) x
      linarith
    exact absurd (hW x hxW hne') (not_lt.mpr hAx)
  -- `dim W = dim range(L|_W) ≤ dim range(L) = rank A₊ = posIndex hA`.
  calc Module.finrank 𝕜 W
      = Module.finrank 𝕜 (LinearMap.range (L.domRestrict W)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxW⟩, rfl⟩
        exact ⟨x, rfl⟩
    _ = (hermPosPart hA).rank := rfl
    _ = posIndex hA := rank_hermPosPart hA

open Unitary in
/-- **Sylvester's inequality (easy direction)**: the Hermitian form is
positive definite on `range A₊`, which has dimension `posIndex hA`.

For `z = A₊ · y ∈ range A₊`, the eigenbasis coordinates `c := Uᴴz` satisfy
`cᵢ = λᵢ⁺ · (Uᴴy)ᵢ`, so `cᵢ = 0` whenever `λᵢ ≤ 0`. Hence
`zᴴAz = ∑ᵢ λᵢ|cᵢ|² = ∑_{λᵢ>0} λᵢ|cᵢ|²`, each term ≥ 0; and `z ≠ 0 ⟹ c ≠ 0`
(U unitary) forces some positive term. -/
theorem posDefOn_range_hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    PosDefOn A (LinearMap.range (hermPosPart hA).mulVecLin) := by
  rintro _ ⟨y, rfl⟩ hne
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set z := (hermPosPart hA).mulVecLin y with hz_def
  change z ≠ 0 at hne
  change 0 < hermForm A z
  set d := star U *ᵥ y with hd_def
  -- `c := Uᴴ · z = Uᴴ·U·diag(λ⁺)·Uᴴ·y = diag(λ⁺)·d`, so `cᵢ = λᵢ⁺·dᵢ`.
  have hc_eq : star U *ᵥ z = fun i => (((hA.eigenvalues i)⁺ : ℝ) : 𝕜) * d i := by
    have hz' : z = hermPosPart hA *ᵥ y := rfl
    rw [hz']; unfold hermPosPart specMap
    rw [conjStarAlgAut_apply, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul,
      ← Matrix.mulVec_mulVec, ← hd_def]
    funext i
    simp only [mulVec, diagonal_dotProduct]
  -- `hermForm A z = ∑ᵢ λᵢ · ‖(Uᴴz)ᵢ‖² = ∑ᵢ λᵢ · (λᵢ⁺)² · ‖dᵢ‖²`.
  have hformA : hermForm A z
      = ∑ i, hA.eigenvalues i * ((hA.eigenvalues i)⁺) ^ 2 * ‖d i‖ ^ 2 := by
    have hAz : A *ᵥ z = specMap hA id *ᵥ z := by rw [specMap_id]
    unfold hermForm
    rw [hAz, hermForm_specMap hA id z, hc_eq]
    refine sum_congr rfl fun i _ => ?_
    simp only [id_eq, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    ring
  rw [hformA]
  -- Each term `≥ 0`; `z ≠ 0 ⟹ some cᵢ ≠ 0 ⟹ some term > 0`.
  have hterm_nn : ∀ i, 0 ≤ hA.eigenvalues i * ((hA.eigenvalues i)⁺) ^ 2 * ‖d i‖ ^ 2 := by
    intro i
    rcases le_or_gt (hA.eigenvalues i) 0 with h | h
    · simp [posPart_eq_zero.mpr h]
    · exact mul_nonneg (mul_nonneg h.le (sq_nonneg _)) (sq_nonneg _)
  refine sum_pos' (fun i _ => hterm_nn i) ?_
  -- `z ≠ 0 ⟹ Uᴴz ≠ 0` (Uᴴ injective since U unitary).
  have hUinj : Function.Injective (star U *ᵥ ·) := by
    intro a b hab
    have hab' : star U *ᵥ a = star U *ᵥ b := hab
    have : (U * star U) *ᵥ a = (U * star U) *ᵥ b := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab']
    rwa [Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec,
      one_mulVec] at this
  have hc_ne : (fun i => (((hA.eigenvalues i)⁺ : ℝ) : 𝕜) * d i) ≠ 0 := by
    rw [← hc_eq]
    intro h
    exact hne (hUinj (h.trans (mulVec_zero _).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc_ne
  refine ⟨i, mem_univ i, ?_⟩
  simp only [Pi.zero_apply, mul_ne_zero_iff, RCLike.ofReal_ne_zero] at hi
  have hevi : 0 < hA.eigenvalues i := by
    by_contra h
    exact hi.1 (posPart_eq_zero.mpr (not_lt.mp h))
  have hdi' : (0 : ℝ) < ‖d i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi.2) 2
  have hpp : (0 : ℝ) < ((hA.eigenvalues i)⁺) ^ 2 := by
    rw [posPart_eq_self.mpr hevi.le]; exact pow_pos hevi 2
  exact mul_pos (mul_pos hevi hpp) hdi'

/-- `hermForm I x = ∑ᵢ ‖xᵢ‖²` (the squared `ℓ²` norm). -/
lemma hermForm_one (x : n → 𝕜) :
    hermForm (1 : Matrix n n 𝕜) x = ∑ i, ‖x i‖ ^ 2 := by
  unfold hermForm
  simp only [one_mulVec, dotProduct, Pi.star_apply, RCLike.star_def, map_sum,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- `∑ᵢ ‖cᵢ‖²` is preserved by the unitary change of variables `c = Uᴴx`. -/
lemma sum_normSq_unitary_mulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x : n → 𝕜) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2
      = ∑ i, ‖x i‖ ^ 2 := by
  have h := hermForm_specMap hA 1 x
  simp only [Pi.one_apply, one_mul] at h
  rw [← h, ← hermForm_one x]
  unfold hermForm
  rw [show specMap hA 1 = (1 : Matrix n n 𝕜) by unfold specMap; simp]

/-- `hermForm A x ≤ θ · ‖x‖²` whenever every eigenvalue of `A` is `≤ θ`.
Equivalently, `A ⪯ θ·I`. -/
lemma hermForm_le_of_eigenvalues_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {θ : ℝ} (hθ : ∀ i, hA.eigenvalues i ≤ θ) (x : n → 𝕜) :
    hermForm A x ≤ θ * ∑ i, ‖x i‖ ^ 2 := by
  have hAx : A *ᵥ x = specMap hA id *ᵥ x := by rw [specMap_id]
  unfold hermForm
  rw [hAx, hermForm_specMap hA id x, ← sum_normSq_unitary_mulVec hA x, mul_sum]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by simpa using hθ i) (sq_nonneg _)

open Unitary in
/-- **Generalized easy Sylvester direction**: on `range(specMap hA (·−θ)⁺)`,
the form satisfies `hermForm A x > θ · ‖x‖²` for `x ≠ 0`. The dimension of
this range is `posIndexAbove hA θ` (via `rank_specMap`).

The proof is identical to `posDefOn_range_hermPosPart` (which is the `θ=0`
case) with `λᵢ > 0` replaced by `λᵢ > θ`. -/
theorem hermForm_gt_on_range_truncPos {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (θ : ℝ) :
    ∀ x ∈ LinearMap.range (specMap hA (fun t => (t - θ)⁺)).mulVecLin, x ≠ 0 →
      θ * ∑ i, ‖x i‖ ^ 2 < hermForm A x := by
  rintro _ ⟨y, rfl⟩ hne
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set g : ℝ → ℝ := fun t => (t - θ)⁺
  set z := (specMap hA g).mulVecLin y with hz_def
  change z ≠ 0 at hne
  set d := star U *ᵥ y with hd_def
  -- `c := Uᴴz = diag(g∘λ)·d`, so `cᵢ = g(λᵢ)·dᵢ`, vanishing where `λᵢ ≤ θ`.
  have hc_eq : star U *ᵥ z = fun i => ((g (hA.eigenvalues i) : ℝ) : 𝕜) * d i := by
    have hz' : z = specMap hA g *ᵥ y := rfl
    rw [hz']; unfold specMap
    rw [conjStarAlgAut_apply, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul,
      ← Matrix.mulVec_mulVec, ← hd_def]
    funext i
    simp only [mulVec, diagonal_dotProduct]
  -- `hermForm A z = ∑ᵢ λᵢ·(g(λᵢ))²·‖dᵢ‖²` and `‖z‖² = ∑ᵢ (g(λᵢ))²·‖dᵢ‖²`.
  have hformA : hermForm A z
      = ∑ i, hA.eigenvalues i * (g (hA.eigenvalues i)) ^ 2 * ‖d i‖ ^ 2 := by
    have hAz : A *ᵥ z = specMap hA id *ᵥ z := by rw [specMap_id]
    unfold hermForm
    rw [hAz, hermForm_specMap hA id z, hc_eq]
    refine sum_congr rfl fun i _ => ?_
    simp only [id_eq, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    ring
  have hnormz : ∑ i, ‖z i‖ ^ 2
      = ∑ i, (g (hA.eigenvalues i)) ^ 2 * ‖d i‖ ^ 2 := by
    rw [← sum_normSq_unitary_mulVec hA z, hc_eq]
    refine sum_congr rfl fun i _ => ?_
    simp only [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  rw [hformA, hnormz, mul_sum]
  -- Termwise: `(λᵢ − θ)·g(λᵢ)²·‖dᵢ‖² ≥ 0`, with strict `>` at some `i`.
  rw [← sub_pos, ← sum_sub_distrib]
  have hterm_nn : ∀ i, 0 ≤ hA.eigenvalues i * (g (hA.eigenvalues i))^2 * ‖d i‖^2
      - θ * ((g (hA.eigenvalues i))^2 * ‖d i‖^2) := by
    intro i
    have heq : hA.eigenvalues i * (g (hA.eigenvalues i))^2 * ‖d i‖^2
        - θ * ((g (hA.eigenvalues i))^2 * ‖d i‖^2)
        = (hA.eigenvalues i - θ) * ((g (hA.eigenvalues i))^2 * ‖d i‖^2) := by ring
    rw [heq]
    rcases le_or_gt (hA.eigenvalues i) θ with h | h
    · simp [g, posPart_eq_zero.mpr (sub_nonpos.mpr h)]
    · exact mul_nonneg (sub_nonneg.mpr h.le) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  refine sum_pos' (fun i _ => hterm_nn i) ?_
  -- `z ≠ 0 ⟹ Uᴴz ≠ 0 ⟹ some cᵢ ≠ 0`, and that `i` has `λᵢ > θ`.
  have hUinj : Function.Injective (star U *ᵥ ·) := by
    intro a b hab
    have hab' : star U *ᵥ a = star U *ᵥ b := hab
    have : (U * star U) *ᵥ a = (U * star U) *ᵥ b := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab']
    rwa [Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec,
      one_mulVec] at this
  have hc_ne : (fun i => ((g (hA.eigenvalues i) : ℝ) : 𝕜) * d i) ≠ 0 := by
    rw [← hc_eq]
    exact fun h => hne (hUinj (h.trans (mulVec_zero _).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc_ne
  refine ⟨i, mem_univ i, ?_⟩
  simp only [Pi.zero_apply, mul_ne_zero_iff, RCLike.ofReal_ne_zero] at hi
  have hevi : θ < hA.eigenvalues i := by
    by_contra h
    exact hi.1 (posPart_eq_zero.mpr (sub_nonpos.mpr (not_lt.mp h)))
  have hgi : 0 < (g (hA.eigenvalues i)) ^ 2 := by
    refine pow_pos ?_ 2
    simp only [g]; rw [posPart_eq_self.mpr (sub_nonneg.mpr hevi.le)]; linarith
  have hdi : 0 < ‖d i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi.2) 2
  have heq : hA.eigenvalues i * (g (hA.eigenvalues i))^2 * ‖d i‖^2
      - θ * ((g (hA.eigenvalues i))^2 * ‖d i‖^2)
      = (hA.eigenvalues i - θ) * ((g (hA.eigenvalues i))^2 * ‖d i‖^2) := by ring
  rw [heq]
  exact mul_pos (sub_pos.mpr hevi) (mul_pos hgi hdi)

lemma finrank_range_truncPos {A : Matrix n n 𝕜} (hA : A.IsHermitian) (θ : ℝ) :
    Module.finrank 𝕜 (LinearMap.range (specMap hA (fun t => (t - θ)⁺)).mulVecLin)
      = posIndexAbove hA θ := by
  show (specMap hA (fun t => (t - θ)⁺)).rank = _
  rw [rank_specMap]; unfold posIndexAbove
  congr 1; ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero, not_le,
    sub_pos]

/-- The dimension of `range A₊` is `posIndex hA`. -/
lemma finrank_range_hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Module.finrank 𝕜 (LinearMap.range (hermPosPart hA).mulVecLin) = posIndex hA := by
  rw [← rank_hermPosPart hA]; rfl

/-- **Sylvester's law of inertia (subspace characterization)**. -/
theorem posIndex_eq_max_finrank_posDefOn {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ W : Submodule 𝕜 (n → 𝕜), PosDefOn A W ∧
      Module.finrank 𝕜 W = posIndex hA :=
  ⟨_, posDefOn_range_hermPosPart hA, finrank_range_hermPosPart hA⟩

end RHLinalg
