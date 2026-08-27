/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide.lean — paper §4 "The zero side: signature and rank", Block structure + prop:block.
Builds on the §3 formalization (Zeta23.LinAlg, namespace RHLinalg): posIndex, posIndex_add_le
(subadditivity, the corollary of lem:inertia), Sylvester's subspace characterization,
posIndex_eq_rank_of_posSemidef.

Reference text: the paper, labels [eq:AE], [eq:Ncount], [eq:hatunits], [prop:block].

Design: this file is ζ-free. Section 1 is generic Hermitian-matrix
lemmas missing from Mathlib/RHLinalg. Section 2 proves prop:block for an ABSTRACT finite
zero configuration `ZeroBlockData` (distinct points z with explicit multiplicities m z ≥ 1,
the involution σ = (ρ ↦ 1 − conj ρ) with m ∘ σ = m, and evaluation vectors v z = (φ̂(γ_z − τ_k))_k with
v (σ z) = conj ∘ v z). Section 3 instantiates from Defs.lean's ZeroConfig, φ̂, τ_k, a, L and
lem:poisson.
-/
import Zeta23.LinAlg
import Zeta23.Defs
import Zeta23.Assembly.Inputs
import Zeta23.Hypotheses.GzGp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide

/-! ## Section 1. Generic lemmas on rank and positive index -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `rank (A + B) ≤ rank A + rank B` for matrices (Mathlib has this only for linear maps). -/
lemma rank_add_le (A B : Matrix n n 𝕜) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro _ ⟨x, rfl⟩
  simp only [mulVecLin_apply, add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

omit [DecidableEq n] in
/-- Rank of a finite sum is at most the sum of given rank bounds. -/
lemma rank_sum_le {α : Type*} (s : Finset α) (f : α → Matrix n n 𝕜) (b : α → ℕ)
    (h : ∀ a ∈ s, (f a).rank ≤ b a) : (∑ a ∈ s, f a).rank ≤ ∑ a ∈ s, b a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (rank_add_le _ _).trans
      (Nat.add_le_add (h a (mem_insert_self a s)) (ih fun x hx => h x (mem_insert_of_mem hx)))

omit [DecidableEq n] in
/-- A scalar multiple of a rank-one matrix `w vᵀ` has rank at most one. -/
lemma rank_smul_vecMulVec_le (c : 𝕜) (w v : n → 𝕜) :
    (c • vecMulVec w v).rank ≤ 1 := by
  rw [← smul_vecMulVec]
  exact rank_vecMulVec_le _ _

omit [DecidableEq n] in
lemma hermForm_smul (r : ℝ) (A : Matrix n n 𝕜) (x : n → 𝕜) :
    hermForm ((r : 𝕜) • A) x = r * hermForm A x := by
  unfold hermForm
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, RCLike.re_ofReal_mul]

/-- The positive index is at most the rank: `#{λᵢ > 0} ≤ #{λᵢ ≠ 0}`. -/
lemma posIndex_le_rank {A : Matrix n n 𝕜} (hA : A.IsHermitian) : posIndex hA ≤ A.rank := by
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold posIndex
  exact card_le_card (fun i => by
    simp only [mem_filter, mem_univ, true_and]
    exact fun h => h.ne')

/-- If the Hermitian form of `A` is nonpositive everywhere then `n₊(A) = 0`. -/
lemma posIndex_eq_zero_of_hermForm_nonpos {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ x, hermForm A x ≤ 0) : posIndex hA = 0 := by
  obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  rw [← hdim, Submodule.finrank_eq_zero]
  by_contra hne
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hne
  exact absurd (hW x hxW hx0) (not_lt.mpr (h x))

/-- `n₊(−N) = 0` for `N ⪰ 0`. -/
lemma posIndex_neg_eq_zero_of_posSemidef {N : Matrix n n 𝕜} (hN : N.PosSemidef) :
    posIndex hN.isHermitian.neg = 0 := by
  refine posIndex_eq_zero_of_hermForm_nonpos _ fun x => ?_
  have : hermForm (-N) x = - hermForm N x := by
    unfold hermForm; rw [neg_mulVec, dotProduct_neg, map_neg]
  rw [this, neg_nonpos]
  exact hermForm_nonneg_of_posSemidef hN x

/-- `n₊(P − N) ≤ rank P` for `P, N ⪰ 0`: subadditivity (lem:inertia) plus `n₊(P) = rank P`, `n₊(−N) = 0`. -/
lemma posIndex_sub_le_rank {P N : Matrix n n 𝕜} (hP : P.PosSemidef) (hN : N.PosSemidef) :
    posIndex (hP.isHermitian.sub hN.isHermitian) ≤ P.rank := by
  have h := posIndex_add_le hP.isHermitian hN.isHermitian.neg
  rw [posIndex_eq_rank_of_posSemidef hP, posIndex_neg_eq_zero_of_posSemidef hN, add_zero] at h
  convert h using 2; exact (sub_eq_add_neg P N)

/-- The positive index is invariant under multiplication by a positive real scalar. -/
lemma posIndex_smul_pos {A : Matrix n n 𝕜} (hA : A.IsHermitian) {r : ℝ} (hr : 0 < r)
    (hrA : ((r : 𝕜) • A).IsHermitian) : posIndex hrA = posIndex hA := by
  apply le_antisymm
  · obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hrA
    rw [← hdim]
    refine finrank_le_posIndex_of_posDefOn hA fun x hx hx0 => ?_
    have := hW x hx hx0
    rw [hermForm_smul] at this
    exact pos_of_mul_pos_right this hr.le
  · obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hA
    rw [← hdim]
    refine finrank_le_posIndex_of_posDefOn hrA fun x hx hx0 => ?_
    rw [hermForm_smul]
    exact mul_pos hr (hW x hx hx0)

/-- Rank is invariant under multiplication by a nonzero scalar. -/
lemma rank_smul_of_ne_zero (A : Matrix n n 𝕜) {c : 𝕜} (hc : c ≠ 0) : (c • A).rank = A.rank := by
  apply le_antisymm
  · simpa using rank_mul_le_right (c • (1 : Matrix n n 𝕜)) A
  · calc A.rank = ((c⁻¹ • (1 : Matrix n n 𝕜)) * (c • A)).rank := by
          rw [Matrix.smul_mul, one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ ≤ (c • A).rank := rank_mul_le_right _ _

end Generic

/-! ## Section 2. The abstract block structure (paper §4: [eq:AE], Block structure, [eq:Ncount], [prop:block])

Paper §4, Block structure, verbatim: "Let 𝒵(I') be the set of distinct zeros with γ ∈ I'. Classify its
points as follows: 𝒮₁: β = ½ and m_ρ = 1 (simple zeros on the line); s₁ := #𝒮₁; 𝒮₂: β = ½ and
m_ρ ≥ 2; s₂ := #𝒮₂; 𝒫: unordered pairs {ρ, 1−ρ̄} with β ≠ ½ (both members lie in 𝒵(I'), they are
distinct points, and m_{1−ρ̄} = m_ρ); p := #𝒫. Thus #𝒵(I') = s₁+s₂+2p and, counting with
multiplicity, N(I') = Σ_{𝒮₁} 1 + Σ_{𝒮₂} m_ρ + Σ_{𝒫} 2m_ρ ≥ s₁+2s₂+2p. [eq:Ncount]
Write N_on(I') := Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ, so that also N(I') ≥ N_on(I') + 2p."

We encode 𝒵(I') as a finite index type ι, the grid {0,…,d−1} as a finite type d, and carry:
multiplicities m (≥ 1, explicit — zeros are DISTINCT points), the involution σ = (ρ ↦ 1−ρ̄)
restricted to 𝒵(I') (it preserves the ordinate, hence 𝒵(I')), and the evaluation vectors
u_ρ = (φ̂(γ_ρ − τ_k))_{k<d} ∈ ℂ^d with u_{1−ρ̄} = conj u_ρ (from γ_{1−ρ̄} = conj γ_ρ, τ_k ∈ ℝ, and
conj φ̂(z̄) = φ̂(z) [subsec:family after eq:fk]). On-line ⟺ β = ½ ⟺ σ ρ = ρ.
-/

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Abstract zero-side data of the window 𝒵(I') [§4 Block structure]: distinct points z : ι with
explicit multiplicity `m z ≥ 1`, evaluation vectors `v z = (φ̂(γ_z − τ_k))_k`, and the involution
`σ = (ρ ↦ 1 − ρ̄)` with `m ∘ σ = m` and `v (σ z) = conj ∘ v z`. -/
structure ZeroBlockData (ι d : Type*) where
  /-- multiplicity m_ρ of the distinct zero ρ -/
  m : ι → ℕ
  one_le_m : ∀ z, 1 ≤ m z
  /-- evaluation vector u_ρ := (φ̂(γ_ρ − τ_k))_{0 ≤ k < d} -/
  v : ι → d → ℂ
  /-- ρ ↦ 1 − ρ̄ on 𝒵(I') -/
  σ : ι → ι
  σ_invol : Function.Involutive σ
  /-- m_{1−ρ̄} = m_ρ -/
  m_σ : ∀ z, m (σ z) = m z
  /-- u_{1−ρ̄} = conj u_ρ -/
  v_σ : ∀ z, v (σ z) = star (v z)

namespace ZeroBlockData

variable (D : ZeroBlockData ι d)

/-- 𝒮₁ ∪ 𝒮₂: on-line points (β = ½ ⟺ fixed by ρ ↦ 1−ρ̄). -/
def onLine : Finset ι := {z | D.σ z = z}

/-- 𝒮₁: on-line and simple (m_ρ = 1). -/
def S₁ : Finset ι := {z | D.σ z = z ∧ D.m z = 1}

/-- 𝒮₂: on-line with m_ρ ≥ 2. -/
def S₂ : Finset ι := {z | D.σ z = z ∧ 2 ≤ D.m z}

/-- s₁ := #𝒮₁ -/
def s₁ : ℕ := #D.S₁

/-- s₂ := #𝒮₂ -/
def s₂ : ℕ := #D.S₂

/-- N(I') = Σ_{ρ ∈ 𝒵(I')} m_ρ (with multiplicity) [eq:Ncount]. -/
def Ncount : ℕ := ∑ z, D.m z

/-- N_on(I') := Σ_{ρ ∈ 𝒮₁ ∪ 𝒮₂} m_ρ. -/
def Non : ℕ := ∑ z ∈ D.onLine, D.m z

/-- A choice of one representative from each off-line pair {ρ, 1−ρ̄} ∈ 𝒫; `p := #R`.
(At instantiation: R = the members with β > ½.) -/
structure PairReps where
  R : Finset ι
  off : ∀ z ∈ R, D.σ z ≠ z
  σ_not_mem : ∀ z ∈ R, D.σ z ∉ R
  cover : ∀ z, D.σ z ≠ z → z ∈ R ∨ D.σ z ∈ R

variable {D}

/-- p := #𝒫, the number of off-line pairs. -/
def PairReps.p (P : D.PairReps) : ℕ := #P.R

/-- Representatives always exist (pick the smaller member of each pair in any linear order). -/
def pairRepsOfLinearOrder [LinearOrder ι] (D : ZeroBlockData ι d) : D.PairReps where
  R := {z | z < D.σ z}
  off z hz := by
    simp only [mem_filter, mem_univ, true_and] at hz; exact fun h => by rw [h] at hz; exact lt_irrefl _ hz
  σ_not_mem z hz := by
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [D.σ_invol z]; exact not_lt.mpr hz.le
  cover z hz := by
    simp only [mem_filter, mem_univ, true_and]
    rcases lt_or_gt_of_ne hz with h | h
    · right; rwa [D.σ_invol z]
    · left; exact h

variable (D) (P : D.PairReps)

lemma mem_onLine {z : ι} : z ∈ D.onLine ↔ D.σ z = z := by simp [onLine]

/-- Splitting a sum over 𝒵(I') = 𝒮₁ ∪ 𝒮₂ ∪ ⋃𝒫 into on-line points and pairs. -/
lemma sum_split {M : Type*} [AddCommMonoid M] (f : ι → M) :
    ∑ z, f z = ∑ z ∈ D.onLine, f z + ∑ z ∈ P.R, (f z + f (D.σ z)) := by
  classical
  have hσinj : Set.InjOn D.σ P.R := fun a _ b _ h => D.σ_invol.injective h
  have hdisj2 : Disjoint P.R (P.R.image D.σ) := by
    rw [disjoint_iff_ne]; rintro a ha _ hb rfl
    obtain ⟨w, hw, hwa⟩ := mem_image.mp hb
    exact P.σ_not_mem w hw (hwa ▸ ha)
  have hdisj1 : Disjoint D.onLine (P.R ∪ P.R.image D.σ) := by
    rw [disjoint_iff_ne]; rintro a ha b hb rfl
    rw [mem_onLine] at ha
    rcases mem_union.mp hb with hb | hb
    · exact P.off a hb ha
    · obtain ⟨w, hw, hwa⟩ := mem_image.mp hb
      apply P.off w hw
      have := congrArg D.σ hwa
      rw [D.σ_invol w] at this
      rw [this, ha]; exact ha
  have hcover : (univ : Finset ι) = D.onLine ∪ (P.R ∪ P.R.image D.σ) := by
    ext z
    simp only [mem_univ, mem_union, mem_onLine, mem_image, true_iff]
    by_cases h : D.σ z = z
    · exact Or.inl h
    · rcases P.cover z h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨D.σ z, h', D.σ_invol z⟩)
  calc ∑ z, f z = ∑ z ∈ D.onLine ∪ (P.R ∪ P.R.image D.σ), f z := by rw [← hcover]
    _ = _ := by rw [sum_union hdisj1, sum_union hdisj2, sum_image hσinj, sum_add_distrib]

/-- #𝒵(I') = #(𝒮₁∪𝒮₂) + 2p. -/
lemma card_eq_onLine_add : Fintype.card ι = #D.onLine + 2 * P.p := by
  have := D.sum_split P (fun _ => (1 : ℕ))
  simpa [sum_const, smul_eq_mul, PairReps.p, Nat.mul_comm] using this

lemma onLine_eq_S₁_union_S₂ : D.onLine = D.S₁ ∪ D.S₂ := by
  ext z
  simp only [onLine, S₁, S₂, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · intro h
    rcases Nat.lt_or_ge (D.m z) 2 with h2 | h2
    · left; exact ⟨h, le_antisymm (Nat.lt_succ_iff.mp h2) (D.one_le_m z)⟩
    · right; exact ⟨h, h2⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

lemma disjoint_S₁_S₂ : Disjoint D.S₁ D.S₂ := by
  rw [disjoint_iff_ne]; rintro a ha _ hb rfl
  simp only [S₁, S₂, mem_filter, mem_univ, true_and] at ha hb
  omega

/-- #(𝒮₁ ∪ 𝒮₂) = s₁ + s₂. -/
lemma card_onLine : #D.onLine = D.s₁ + D.s₂ := by
  rw [onLine_eq_S₁_union_S₂, card_union_of_disjoint D.disjoint_S₁_S₂]; rfl

/-- "#𝒵(I') = s₁ + s₂ + 2p" [§4 Block structure]. -/
theorem card_eq : Fintype.card ι = D.s₁ + D.s₂ + 2 * P.p := by
  rw [D.card_eq_onLine_add P, card_onLine]

/-- N_on(I') ≥ s₁ + 2 s₂ (since m_ρ = 1 on 𝒮₁ and m_ρ ≥ 2 on 𝒮₂). -/
lemma s₁_add_two_s₂_le_Non : D.s₁ + 2 * D.s₂ ≤ D.Non := by
  unfold Non s₁ s₂
  rw [onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂]
  apply Nat.add_le_add
  · rw [card_eq_sum_ones]
    exact sum_le_sum fun z hz => D.one_le_m z
  · rw [card_eq_sum_ones, mul_sum]
    exact sum_le_sum fun z hz => by
      simp only [S₂, mem_filter, mem_univ, true_and] at hz; simpa using hz.2

/-- "N(I') ≥ N_on(I') + 2p" [§4, after eq:Ncount]. -/
theorem Non_add_two_p_le_Ncount : D.Non + 2 * P.p ≤ D.Ncount := by
  unfold Ncount Non PairReps.p
  rw [D.sum_split P, card_eq_sum_ones, mul_sum]
  apply Nat.add_le_add_left
  exact sum_le_sum fun z _ => by
    have := D.one_le_m z; have := D.one_le_m (D.σ z); omega

/-- [eq:Ncount]: "N(I') = Σ_{𝒮₁} 1 + Σ_{𝒮₂} m_ρ + Σ_{𝒫} 2m_ρ ≥ s₁ + 2s₂ + 2p". -/
theorem s₁_add_two_s₂_add_two_p_le_Ncount : D.s₁ + 2 * D.s₂ + 2 * P.p ≤ D.Ncount :=
  (Nat.add_le_add_right D.s₁_add_two_s₂_le_Non _).trans (D.Non_add_two_p_le_Ncount P)

/-! ### The matrix A [eq:AE] and its decomposition -/

/-- A_{kl} := Σ_{ρ : γ ∈ I'} m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l)  [eq:AE]; i.e. A = Σ_ρ m_ρ u_ρ u_ρᵀ
(transpose, NOT conjugate-transpose). -/
def blockA : Matrix d d ℂ := ∑ z, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma blockA_apply (k l : d) : D.blockA k l = ∑ z, (D.m z : ℂ) * (D.v z k * D.v z l) := by
  simp [blockA, Matrix.sum_apply, vecMulVec_apply]

/-- u_ρ is a real vector for ρ on the line. -/
lemma star_v_of_onLine {z : ι} (hz : D.σ z = z) : star (D.v z) = D.v z := by
  rw [← D.v_σ, hz]

/-- "A is real symmetric (same argument as for G: conjugation permutes the summands via ρ ↦ 1−ρ̄)". -/
theorem blockA_isHermitian : D.blockA.IsHermitian := by
  unfold blockA Matrix.IsHermitian
  rw [conjTranspose_sum]
  simp_rw [conjTranspose_smul, conjTranspose_vecMulVec, ← D.v_σ]
  simp only [star_natCast]
  exact Fintype.sum_equiv D.σ_invol.toPerm _ _ fun z => by simp [D.m_σ]

lemma blockA_transpose : D.blockAᵀ = D.blockA := by
  unfold blockA
  rw [transpose_sum]
  simp_rw [transpose_smul, transpose_vecMulVec]

/-- Every entry of A is real. -/
lemma star_blockA_apply (k l : d) : star (D.blockA k l) = D.blockA k l := by
  have h1 := congrFun (congrFun D.blockA_isHermitian l) k
  have h2 := congrFun (congrFun D.blockA_transpose l) k
  rw [conjTranspose_apply] at h1
  rw [transpose_apply] at h2
  rw [h1, ← h2]

/-- real part vector x_ρ := Re u_ρ (as a complex vector) -/
def xv (z : ι) : d → ℂ := fun k => ((D.v z k).re : ℂ)
/-- imaginary part vector y_ρ := Im u_ρ (as a complex vector) -/
def yv (z : ι) : d → ℂ := fun k => ((D.v z k).im : ℂ)

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma star_xv (z : ι) : star (D.xv z) = D.xv z := by
  funext k; simp [xv]
omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma star_yv (z : ι) : star (D.yv z) = D.yv z := by
  funext k; simp [yv]

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- The pair block: m(u uᵀ + ū ūᵀ) = 2m(x xᵀ − y yᵀ) for u = x + iy. -/
lemma pair_term (z : ι) :
    (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)
      + (D.m (D.σ z) : ℂ) • vecMulVec (D.v (D.σ z)) (D.v (D.σ z))
      = ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.xv z) (D.xv z)
        - ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.yv z) (D.yv z) := by
  rw [D.m_σ, D.v_σ]
  ext k l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, smul_eq_mul, xv, yv, RCLike.star_def]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- the on-line part Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ u_ρ u_ρᵀ -/
def onPart : Matrix d d ℂ := ∑ z ∈ D.onLine, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)
/-- Σ_𝒫 2m_ρ x_ρ x_ρᵀ -/
def rePart : Matrix d d ℂ := ∑ z ∈ P.R, ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.xv z) (D.xv z)
/-- Σ_𝒫 2m_ρ y_ρ y_ρᵀ -/
def imPart : Matrix d d ℂ := ∑ z ∈ P.R, ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.yv z) (D.yv z)

/-- A = (on-line part) + (Σ_𝒫 2m x xᵀ − Σ_𝒫 2m y yᵀ). -/
lemma blockA_decomp : D.blockA = D.onPart + (D.rePart P - D.imPart P) := by
  unfold blockA onPart rePart imPart
  rw [D.sum_split P, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun z _ => D.pair_term z

omit [DecidableEq d] in
/-- c • x xᵀ ⪰ 0 for a real vector x and real c ≥ 0. -/
lemma posSemidef_smul_vecMulVec {x : d → ℂ} (hx : star x = x) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • vecMulVec x x).PosSemidef := by
  have h := posSemidef_vecMulVec_self_star x
  rw [hx] at h
  exact h.smul (Complex.zero_le_real.mpr hc)

lemma onPart_posSemidef : D.onPart.PosSemidef := by
  unfold onPart
  refine posSemidef_sum _ fun z hz => ?_
  have := posSemidef_smul_vecMulVec (D.star_v_of_onLine ((D.mem_onLine).mp hz)) (Nat.cast_nonneg (D.m z))
  simpa using this

lemma rePart_posSemidef : (D.rePart P).PosSemidef := by
  unfold rePart
  exact posSemidef_sum _ fun z _ => posSemidef_smul_vecMulVec (D.star_xv z) (by positivity)

lemma imPart_posSemidef : (D.imPart P).PosSemidef := by
  unfold imPart
  exact posSemidef_sum _ fun z _ => posSemidef_smul_vecMulVec (D.star_yv z) (by positivity)

lemma rank_onPart_le : D.onPart.rank ≤ #D.onLine := by
  unfold onPart
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma rank_rePart_le : (D.rePart P).rank ≤ P.p := by
  unfold rePart PairReps.p
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

omit [DecidableEq ι] in
/-- "A is a sum of #𝒵(I') matrices of rank one" ⟹ rank A ≤ #𝒵(I') [prop:block (i)]. -/
theorem rank_blockA_le : D.blockA.rank ≤ Fintype.card ι := by
  unfold blockA
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma posIndex_congr {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    posIndex hA = posIndex hB := by
  subst h; rfl

/-- **prop:block (i), positive index**: "n₊(Ã) ≤ s₁ + s₂ + p" — stated for A itself; positive
scalings (Ã = A/L, Â = A/(aL²)) do not change n₊, see `posIndex_smul_pos`. Paper proof: pull-back of
the direct sum of s₁+s₂ positive 1×1 forms and p hyperbolic 2×2 forms under the evaluation map,
lem:inertia. Lean proof: the same inertia bound via subadditivity (RHLinalg.posIndex_add_le, the
paper's stated corollary of lem:inertia) applied to A = P₀ + (X − Y) with P₀ = Σ_on m u uᵀ ⪰ 0 of
rank ≤ s₁+s₂ and X = Σ_𝒫 2m x xᵀ ⪰ 0 of rank ≤ p, Y ⪰ 0 (each hyperbolic block m(uuᵀ+ūūᵀ) =
2m(xxᵀ − yyᵀ)). -/
theorem posIndex_blockA_le : posIndex D.blockA_isHermitian ≤ D.s₁ + D.s₂ + P.p := by
  have hOn := D.onPart_posSemidef
  have hRe := D.rePart_posSemidef P
  have hIm := D.imPart_posSemidef P
  have h1 := posIndex_add_le hOn.isHermitian (hRe.isHermitian.sub hIm.isHermitian)
  have h2 := posIndex_sub_le_rank hRe hIm
  rw [posIndex_eq_rank_of_posSemidef hOn] at h1
  rw [posIndex_congr D.blockA_isHermitian (hOn.isHermitian.add (hRe.isHermitian.sub hIm.isHermitian))
    (D.blockA_decomp P), ← card_onLine]
  exact h1.trans (Nat.add_le_add D.rank_onPart_le (h2.trans (D.rank_rePart_le P)))

/-- prop:block (i) for any positive multiple r•A (Ã = A/L: "Dividing by L > 0 changes nothing"). -/
theorem posIndex_smul_blockA_le {r : ℝ} (hr : 0 < r) (h : ((r : ℂ) • D.blockA).IsHermitian) :
    posIndex h ≤ D.s₁ + D.s₂ + P.p := by
  have key : posIndex h = posIndex D.blockA_isHermitian := posIndex_smul_pos D.blockA_isHermitian hr h
  exact key ▸ D.posIndex_blockA_le P

/-- prop:block (i), rank, for any nonzero multiple: "rank(Ã) ≤ s₁ + s₂ + 2p = #𝒵(I')". -/
theorem rank_smul_blockA_le {r : ℂ} (hr : r ≠ 0) :
    (r • D.blockA).rank ≤ D.s₁ + D.s₂ + 2 * P.p := by
  rw [rank_smul_of_ne_zero _ hr, ← D.card_eq P]; exact D.rank_blockA_le

/-! ### prop:block (ii): Â = P + Q in the units [eq:hatunits] -/

/-- P := (aL²)⁻¹ Σ_{ρ ∈ 𝒮₁∪𝒮₂} m_ρ u_ρ u_ρᵀ  [prop:block proof of (ii)], with c := aL². -/
def blockP (c : ℝ) : Matrix d d ℂ := ((c⁻¹ : ℝ) : ℂ) • D.onPart

/-- Q := Â − P, "the sum of the pair contributions". -/
def blockQ (c : ℝ) : Matrix d d ℂ := ((c⁻¹ : ℝ) : ℂ) • (D.blockA - D.onPart)

/-- Â = P + Q where Â := A/(aL²) [eq:hatunits] (here: c⁻¹ • A with c = aL²). -/
theorem blockP_add_blockQ (c : ℝ) : D.blockP c + D.blockQ c = ((c⁻¹ : ℝ) : ℂ) • D.blockA := by
  unfold blockP blockQ; rw [← smul_add, add_sub_cancel]

lemma blockQ_eq (c : ℝ) : D.blockQ c = ((c⁻¹ : ℝ) : ℂ) • (D.rePart P - D.imPart P) := by
  unfold blockQ; congr 1
  rw [D.blockA_decomp P, add_sub_cancel_left]

/-- "P is … positive semidefinite". -/
theorem blockP_posSemidef {c : ℝ} (hc : 0 < c) : (D.blockP c).PosSemidef :=
  D.onPart_posSemidef.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

/-- "P is real symmetric": Hermitian with real entries. -/
theorem star_blockP_apply (c : ℝ) (k l : d) : star (D.blockP c k l) = D.blockP c k l := by
  simp only [blockP, onPart, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul,
    star_mul', star_sum, RCLike.star_def, Complex.conj_ofReal, map_natCast]
  congr 1
  refine sum_congr rfl fun z hz => ?_
  have h := congrFun (D.star_v_of_onLine ((D.mem_onLine).mp hz))
  simp only [Pi.star_apply, RCLike.star_def] at h
  rw [h, h]

/-- "of rank ≤ s₁ + s₂". -/
theorem rank_blockP_le {c : ℝ} (hc : 0 < c) : (D.blockP c).rank ≤ D.s₁ + D.s₂ := by
  unfold blockP
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne')), ← card_onLine]
  exact D.rank_onPart_le

/-- tr(m u uᵀ) for real u: m Σ_k u_k² = m ‖u‖². -/
lemma rtrace_onPart : rtrace D.onPart = ∑ z ∈ D.onLine, (D.m z : ℝ) * ∑ k, ‖D.v z k‖ ^ 2 := by
  unfold onPart rtrace
  rw [trace_sum, map_sum]
  refine sum_congr rfl fun z hz => ?_
  have h := congrFun (D.star_v_of_onLine ((D.mem_onLine).mp hz))
  rw [trace_smul, trace_vecMulVec, smul_eq_mul, dotProduct]
  have : ∑ k, D.v z k * D.v z k = ((∑ k, ‖D.v z k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun k _ => ?_
    have hk : (starRingEnd ℂ) (D.v z k) = D.v z k := by
      have := h k; rwa [Pi.star_apply, RCLike.star_def] at this
    calc D.v z k * D.v z k = (starRingEnd ℂ) (D.v z k) * D.v z k := by rw [hk]
      _ = _ := RCLike.conj_mul (D.v z k)
  rw [this, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

/-- "by Lemma [lem:poisson], tr P = (aL²)⁻¹ Σ m_ρ Σ_{0≤k<d} φ̂(γ_ρ−τ_k)² ≤ (aL²)⁻¹ Σ m_ρ Σ_{k∈ℤ}
φ̂(γ_ρ−τ_k)² = N_on(I')". The Poisson input enters ONLY as the hypothesis `hPois`: for each on-line
ρ ∈ 𝒵(I'), Σ_{0≤k<d} |φ̂(γ_ρ − τ_k)|² ≤ c = aL² (finite partial sum of the nonnegative series whose
full sum over k ∈ ℤ is exactly aL² by lem:poisson). -/
theorem rtrace_blockP_le {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (D.blockP c) ≤ (D.Non : ℝ) := by
  have htr : rtrace (D.blockP c) = c⁻¹ * rtrace D.onPart := by
    simp only [rtrace, blockP, trace_smul, smul_eq_mul, RCLike.re_to_complex, Complex.re_ofReal_mul]
  unfold Non
  rw [htr, rtrace_onPart, mul_sum, Nat.cast_sum]
  refine sum_le_sum fun z hz => ?_
  rw [← mul_assoc, mul_comm (c⁻¹), mul_assoc]
  have hm : (0 : ℝ) ≤ D.m z := Nat.cast_nonneg _
  calc (D.m z : ℝ) * (c⁻¹ * ∑ k, ‖D.v z k‖ ^ 2) ≤ D.m z * (c⁻¹ * c) := by
        gcongr; exact hPois z hz
    _ = D.m z := by rw [inv_mul_cancel₀ hc.ne', mul_one]

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma isHermitian_real_smul {A : Matrix d d ℂ} (hA : A.IsHermitian) (r : ℝ) :
    ((r : ℂ) • A).IsHermitian :=
  hA.smul (by rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])

/-- Q is Hermitian (real symmetric). -/
theorem blockQ_isHermitian (c : ℝ) : (D.blockQ c).IsHermitian :=
  isHermitian_real_smul (D.blockA_isHermitian.sub D.onPart_posSemidef.isHermitian) _

/-- Every entry of Q is real. -/
theorem star_blockQ_apply (c : ℝ) (k l : d) : star (D.blockQ c k l) = D.blockQ c k l := by
  have hA := D.star_blockA_apply k l
  have hP := D.star_blockP_apply c k l
  have : D.blockQ c k l = ((c⁻¹ : ℝ) : ℂ) * D.blockA k l - D.blockP c k l := by
    simp [blockQ, blockP, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub]
  rw [this, star_sub, star_mul', hA, hP, RCLike.star_def, Complex.conj_ofReal]

/-- **prop:block (ii)**: "n₊(Q) ≤ p" — "The form c ↦ c*Qc is the pull-back under 𝒜 of the direct
sum of the p hyperbolic blocks alone, so n₊(Q) ≤ p by Lemma [lem:inertia]". -/
theorem posIndex_blockQ_le {c : ℝ} (hc : 0 < c) :
    posIndex (D.blockQ_isHermitian c) ≤ P.p := by
  have hRe := D.rePart_posSemidef P
  have hIm := D.imPart_posSemidef P
  have hH := hRe.isHermitian.sub hIm.isHermitian
  rw [posIndex_congr (D.blockQ_isHermitian c) (isHermitian_real_smul hH c⁻¹) (D.blockQ_eq P c)]
  have key : posIndex (isHermitian_real_smul hH c⁻¹) = posIndex hH :=
    posIndex_smul_pos hH (inv_pos.mpr hc) _
  rw [key]
  exact (posIndex_sub_le_rank hRe hIm).trans (D.rank_rePart_le P)

end ZeroBlockData

end Block

/-! ## Section 3. Instantiation against Zeta23.Defs: 𝒵(I') ⊂ ZeroConfig, A = Z.Az P T  [eq:AE]

Here ι := 𝒵(I') = Z.ZIprime T (finite by ZeroConfig.finite_window), d := Fin (P.d T),
m := Z.mult, σ := reflect = (ρ ↦ 1 − conj ρ), v ρ k := φ̂(γ_ρ − τ_k) with γ_ρ = gammaOf ρ, τ_k = P.tau T k.
The analytic inputs are explicit hypotheses of this section (discharged elsewhere in the
repository from Zeta23.Taper / Zeta23.Poisson: Params.phiHat_conj, Params.phiHat_ofReal,
Params.hasSum_phiHatR_sq):
  hconj : ∀ z, φ̂(conj z) = conj φ̂(z)                       [subsec:family, after eq:fk]
  hreal : ∀ r : ℝ, φ̂(r) = φ̂_ℝ(r) (φ̂ real on ℝ)
  hPois : ∀ γ : ℝ, HasSum (k ↦ φ̂(γ − τ_k)²) (aL²)            [lem:poisson, "in particular"]
-/

section Inst

open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ)

lemma ZIprime_finite : (Z.ZIprime T).Finite := Z.finite_window _ _

/-- 𝒵(I') as a Finset of ℂ. -/
def ZI : Finset ℂ := (ZIprime_finite Z T).toFinset

lemma mem_ZI {ρ : ℂ} : ρ ∈ ZI Z T ↔ ρ ∈ Z.ZIprime T := Set.Finite.mem_toFinset _

lemma coe_ZI : ((ZI Z T : Finset ℂ) : Set ℂ) = Z.ZIprime T := Set.Finite.coe_toFinset _

lemma mem_ZIprime_iff {ρ : ℂ} :
    ρ ∈ Z.ZIprime T ↔ ρ ∈ Z.carrier ∧ T - D0 T < ρ.im ∧ ρ.im ≤ 2 * T + D0 T := by
  simp [ZeroConfig.ZIprime, ZeroConfig.window]

omit Z T in
lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by simp [reflect]
omit Z T in
lemma reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
omit Z T in
lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

omit Z T in
/-- fixed points of ρ ↦ 1 − ρ̄ are exactly the points with β = 1/2 -/
lemma reflect_eq_self_iff (ρ : ℂ) : reflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h; have := congrArg Complex.re h; rw [reflect_re] at this; linarith
  · intro h
    apply Complex.ext
    · rw [reflect_re, h]; norm_num
    · rw [reflect_im]

omit Z T in
/-- γ_{1−ρ̄} = conj γ_ρ. -/
lemma gammaOf_reflect (ρ : ℂ) : gammaOf (reflect ρ) = starRingEnd ℂ (gammaOf ρ) := by
  simp only [gammaOf, reflect, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_I]
  field_simp
  ring

omit Z T in
/-- For ρ on the line, γ_ρ = γ = Im ρ is real. -/
lemma gammaOf_of_re_eq_half {ρ : ℂ} (h : ρ.re = 1 / 2) : gammaOf ρ = (ρ.im : ℂ) := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext
  · simp
  · simp [h]

lemma reflect_mem_ZI {ρ : ℂ} (h : ρ ∈ ZI Z T) : reflect ρ ∈ ZI Z T := by
  rw [mem_ZI, mem_ZIprime_iff] at h ⊢
  exact ⟨Z.reflect_mem ρ h.1, by rw [reflect_im]; exact h.2⟩

lemma mem_carrier_of_mem_ZI {ρ : ℂ} (h : ρ ∈ ZI Z T) : ρ ∈ Z.carrier :=
  ((mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp h)).1

/-- Block data of 𝒵(I') with an arbitrary σ-equivariant family of vectors v (the counting facts do
not depend on v; the matrix facts use v ρ = (φ̂(γ_ρ − τ_k))_k). -/
def mkData {d : Type*} (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z)) :
    ZeroBlockData (ZI Z T) d where
  m z := Z.mult z
  one_le_m z := Z.one_le_mult _ (mem_carrier_of_mem_ZI Z T z.2)
  v := v
  σ z := ⟨reflect z, reflect_mem_ZI Z T z.2⟩
  σ_invol _ := Subtype.ext (reflect_reflect _)
  m_σ z := Z.mult_reflect _ (mem_carrier_of_mem_ZI Z T z.2)
  v_σ := hv

section mk
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

@[simp] lemma mkData_m (z : ZI Z T) : (mkData Z T v hv).m z = Z.mult z := rfl
@[simp] lemma mkData_v : (mkData Z T v hv).v = v := rfl
@[simp] lemma mkData_σ (z : ZI Z T) : ((mkData Z T v hv).σ z : ℂ) = reflect z := rfl

lemma mkData_σ_eq_iff (z : ZI Z T) : (mkData Z T v hv).σ z = z ↔ (z : ℂ).re = 1 / 2 := by
  rw [Subtype.ext_iff, mkData_σ, reflect_eq_self_iff]

/-- Canonical representatives of the off-line pairs: the member with β > 1/2. -/
def mkPairReps : (mkData Z T v hv).PairReps where
  R := {z | 1 / 2 < (z : ℂ).re}
  off z hz h := by
    rw [mkData_σ_eq_iff] at h
    simp only [mem_filter, mem_univ, true_and] at hz
    linarith
  σ_not_mem z hz h := by
    simp only [mem_filter, mem_univ, true_and, mkData_σ, reflect_re] at hz h
    linarith
  cover z hz := by
    rw [ne_eq, mkData_σ_eq_iff] at hz
    simp only [mem_filter, mem_univ, true_and, mkData_σ, reflect_re]
    rcases lt_or_gt_of_ne hz with h | h
    · right; linarith
    · left; exact h

omit Z T in
lemma card_filter_coe (s : Finset ℂ) (p : ℂ → Prop) (q : s → Prop)
    (h : ∀ z : s, q z ↔ p z) : #{z : s | q z} = #(s.filter p) := by
  apply Finset.card_bij (fun (z : s) _ => (z : ℂ))
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨z.2, (h z).mp hz⟩
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb
    simp only [mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp only [mem_filter, mem_univ, true_and]; exact (h _).mpr hb.2, rfl⟩

omit Z T in
lemma sum_filter_coe {M : Type*} [AddCommMonoid M] (s : Finset ℂ) (p : ℂ → Prop) (q : s → Prop)
    (h : ∀ z : s, q z ↔ p z) (f : ℂ → M) :
    ∑ z ∈ ({z : s | q z} : Finset s), f z = ∑ z ∈ s.filter p, f z := by
  apply Finset.sum_bij (fun (z : s) _ => (z : ℂ))
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨z.2, (h z).mp hz⟩
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb
    simp only [mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp only [mem_filter, mem_univ, true_and]; exact (h _).mpr hb.2, rfl⟩
  · intro z _; rfl

lemma S1_eq : Z.S1 T = ↑((ZI Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)) := by
  ext ρ
  simp only [ZeroConfig.S1, ZeroConfig.onLine, ZeroConfig.simple, Set.mem_inter_iff,
    Set.mem_setOf_eq, Finset.coe_filter, mem_ZI]
  tauto

lemma S2_eq : Z.S2 T = ↑((ZI Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ 2 ≤ Z.mult ρ)) := by
  ext ρ
  simp only [ZeroConfig.S2, ZeroConfig.onLine, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.coe_filter, mem_ZI]
  tauto

lemma offLine_eq : Z.offLine T = ↑((ZI Z T).filter (fun ρ => ¬ ρ.re = 1 / 2)) := by
  ext ρ
  simp only [ZeroConfig.offLine, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, mem_ZI, ne_eq]

lemma s1_eq_mk : Z.s1 T = (mkData Z T v hv).s₁ := by
  rw [ZeroConfig.s1, S1_eq, Set.ncard_coe_finset, ZeroBlockData.s₁, ZeroBlockData.S₁]
  convert (card_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    (fun z => (mkData Z T v hv).σ z = z ∧ (mkData Z T v hv).m z = 1)
    fun z => by rw [mkData_σ_eq_iff]; rfl).symm using 2
  all_goals first | exact Finset.filter_congr_decidable _ _ _ | exact (Finset.filter_congr_decidable _ _ _).symm

lemma s2_eq_mk : Z.s2 T = (mkData Z T v hv).s₂ := by
  rw [ZeroConfig.s2, S2_eq, Set.ncard_coe_finset, ZeroBlockData.s₂, ZeroBlockData.S₂]
  convert (card_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2 ∧ 2 ≤ Z.mult ρ)
    (fun z => (mkData Z T v hv).σ z = z ∧ 2 ≤ (mkData Z T v hv).m z)
    fun z => by rw [mkData_σ_eq_iff]; rfl).symm using 2
  all_goals first | exact Finset.filter_congr_decidable _ _ _ | exact (Finset.filter_congr_decidable _ _ _).symm

/-- #offLine = 2p. -/
lemma card_offLine_eq_mk : (Z.offLine T).ncard = 2 * (mkPairReps Z T v hv).p := by
  rw [offLine_eq, Set.ncard_coe_finset]
  have h1 := (mkData Z T v hv).card_eq_onLine_add (mkPairReps Z T v hv)
  have h2 : #((ZI Z T).filter fun ρ => ρ.re = 1 / 2) + #((ZI Z T).filter fun ρ => ¬ ρ.re = 1 / 2)
      = #(ZI Z T) := Finset.card_filter_add_card_filter_not _
  have h3 : #(mkData Z T v hv).onLine = #((ZI Z T).filter fun ρ => ρ.re = 1 / 2) := by
    convert card_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2) (fun z => (mkData Z T v hv).σ z = z)
      (fun z => mkData_σ_eq_iff Z T v hv z) using 2
    ext; simp [ZeroBlockData.onLine]
  have h4 : Fintype.card (ZI Z T) = #(ZI Z T) := Fintype.card_coe _
  omega

lemma p_eq_mk : Z.p T = (mkPairReps Z T v hv).p := by
  rw [ZeroConfig.p, card_offLine_eq_mk Z T v hv]; omega

lemma NIprime_eq_mk : Z.NIprime T = (mkData Z T v hv).Ncount := by
  rw [ZeroConfig.NIprime, ZeroConfig.N, ZeroBlockData.Ncount]
  change ∑ᶠ ρ ∈ Z.ZIprime T, Z.mult ρ = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprime_finite Z T), ← Finset.sum_coe_sort]
  rfl

lemma NonIprime_eq_mk : Z.NonIprime T = (mkData Z T v hv).Non := by
  rw [ZeroConfig.NonIprime, ZeroConfig.N0, ZeroBlockData.Non, ZeroBlockData.onLine]
  have hset : Z.window (T - D0 T) (2 * T + D0 T) ∩ ZeroConfig.onLine
      = ↑((ZI Z T).filter fun ρ => ρ.re = 1 / 2) := by
    ext ρ
    simp only [ZeroConfig.onLine, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, mem_ZI,
      ZeroConfig.ZIprime]
  rw [hset, finsum_mem_coe_finset]
  convert (sum_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2) (fun z => (mkData Z T v hv).σ z = z)
    (fun z => mkData_σ_eq_iff Z T v hv z) (fun ρ => Z.mult ρ)).symm using 2
  · ext; simp
  · rfl

end mk

/-- the zero family of vectors (for the v-independent counting statements) -/
def zeroVec : ZI Z T → Unit → ℂ := fun _ _ => 0

lemma zeroVec_reflect : ∀ z : ZI Z T, zeroVec Z T ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (zeroVec Z T z) :=
  fun _ => by ext; simp [zeroVec]

/-- **"#𝒵(I') = s₁ + s₂ + 2p"**  [§4 Block structure] (Defs' provisional p := #offLine/2). -/
theorem ncard_ZIprime_eq : (Z.ZIprime T).ncard = Z.s1 T + Z.s2 T + 2 * Z.p T := by
  have hv := zeroVec_reflect Z T
  rw [← coe_ZI, Set.ncard_coe_finset, s1_eq_mk Z T _ hv, s2_eq_mk Z T _ hv, p_eq_mk Z T _ hv,
    ← ZeroBlockData.card_eq _ (mkPairReps Z T _ hv), Fintype.card_coe]

/-- #offLine(I') = 2p: Defs' p := ncard(offLine)/2 loses nothing. -/
theorem ncard_offLine_eq : (Z.offLine T).ncard = 2 * Z.p T := by
  have hv := zeroVec_reflect Z T
  rw [p_eq_mk Z T _ hv, card_offLine_eq_mk Z T _ hv]

/-- **[eq:Ncount]** "N(I') = Σ_{𝒮₁}1 + Σ_{𝒮₂}m_ρ + Σ_{𝒫}2m_ρ ≥ s₁ + 2s₂ + 2p". -/
theorem s1_add_two_s2_add_two_p_le_NIprime : Z.s1 T + 2 * Z.s2 T + 2 * Z.p T ≤ Z.NIprime T := by
  have hv := zeroVec_reflect Z T
  rw [s1_eq_mk Z T _ hv, s2_eq_mk Z T _ hv, p_eq_mk Z T _ hv, NIprime_eq_mk Z T _ hv]
  exact ZeroBlockData.s₁_add_two_s₂_add_two_p_le_Ncount _ _

/-- **"N(I') ≥ N_on(I') + 2p"** [§4, after eq:Ncount]. -/
theorem NonIprime_add_two_p_le_NIprime : Z.NonIprime T + 2 * Z.p T ≤ Z.NIprime T := by
  have hv := zeroVec_reflect Z T
  rw [p_eq_mk Z T _ hv, NIprime_eq_mk Z T _ hv, NonIprime_eq_mk Z T _ hv]
  exact ZeroBlockData.Non_add_two_p_le_Ncount _ _

/-! ### The matrix A = Z.Az P T and prop:block for Ã := P.tilde T A, Â := P.hat T A -/

variable (P : Params)

/-- Hypothesis shape: conj φ̂(z̄) = φ̂(z) [subsec:family after eq:fk]; = Params.phiHat_conj (Taper.lean). -/
abbrev PhiHatConj : Prop := ∀ z : ℂ, P.phiHat T (starRingEnd ℂ z) = starRingEnd ℂ (P.phiHat T z)
/-- Hypothesis shape: φ̂ is real on ℝ; = Params.phiHat_ofReal (Taper.lean). -/
abbrev PhiHatReal : Prop := ∀ r : ℝ, P.phiHat T r = (P.phiHatR T r : ℂ)
/-- Hypothesis shape: lem:poisson "in particular Σ_{k∈ℤ} φ̂(γ−τ_k)² = aL²" for real γ;
= Params.hasSum_phiHatR_sq (Poisson.lean). -/
abbrev PoissonSq : Prop :=
  ∀ γ : ℝ, HasSum (fun k : ℤ => P.phiHatR T (γ - P.tau T k) ^ 2) (P.a T * P.L T ^ 2)

/-- the evaluation vectors u_ρ := (φ̂(γ_ρ − τ_k))_{0≤k<d}  [prop:block proof] -/
def evalVec : ZI Z T → Fin (P.d T) → ℂ := fun z k => P.phiHat T (gammaOf z - P.tau T k)

variable {Z T P}

/-- u_{1−ρ̄} = conj u_ρ (from γ_{1−ρ̄} = conj γ_ρ, τ_k ∈ ℝ, φ̂(conj w) = conj φ̂(w)). -/
lemma evalVec_reflect (hconj : PhiHatConj T P) :
    ∀ z : ZI Z T, evalVec Z T P ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (evalVec Z T P z) := by
  intro z
  funext k
  simp only [evalVec, Pi.star_apply, RCLike.star_def]
  rw [gammaOf_reflect, ← hconj, map_sub, Complex.conj_ofReal]

variable (Z T P)

/-- The block data of 𝒵(I') [eq:AE]: m := Z.mult, u_ρ := (φ̂(γ_ρ − τ_k))_{0≤k<d}, σ := ρ ↦ 1 − ρ̄. -/
def blockData (hconj : PhiHatConj T P) : ZeroBlockData (ZI Z T) (Fin (P.d T)) :=
  mkData Z T (evalVec Z T P) (evalVec_reflect hconj)

/-- **A = Σ_{ρ∈𝒵(I')} m_ρ u_ρ u_ρᵀ**: Defs' finsum matrix Z.Az P T [eq:AE] is the abstract blockA. -/
theorem Az_eq_blockA (hconj : PhiHatConj T P) : Z.Az P T = (blockData Z T P hconj).blockA := by
  ext k l
  rw [ZeroBlockData.blockA_apply]
  change ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprime_finite Z T), ← Finset.sum_coe_sort]
  refine sum_congr rfl fun z _ => ?_
  simp only [ZeroConfig.Gsummand, blockData, mkData, evalVec]
  ring

/-- A is Hermitian (indeed real symmetric). -/
theorem Az_isHermitian (hconj : PhiHatConj T P) : (Z.Az P T).IsHermitian := by
  rw [Az_eq_blockA Z T P hconj]; exact ZeroBlockData.blockA_isHermitian _

/-- Every entry of A is real. -/
theorem star_Az_apply (hconj : PhiHatConj T P) (k l : Fin (P.d T)) :
    star (Z.Az P T k l) = Z.Az P T k l := by
  rw [Az_eq_blockA Z T P hconj]; exact ZeroBlockData.star_blockA_apply _ k l

omit Z in
lemma tilde_eq {n : Type*} (M : Matrix n n ℂ) : P.tilde T M = (((P.L T)⁻¹ : ℝ) : ℂ) • M := by
  unfold Params.tilde; push_cast; rfl

omit Z in
lemma hat_eq {n : Type*} (M : Matrix n n ℂ) :
    P.hat T M = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • M := by
  unfold Params.hat; push_cast; rfl

theorem tilde_Az_isHermitian (hconj : PhiHatConj T P) : (P.tilde T (Z.Az P T)).IsHermitian := by
  rw [tilde_eq]; exact ZeroBlockData.isHermitian_real_smul (Az_isHermitian Z T P hconj) _

theorem hat_Az_isHermitian (hconj : PhiHatConj T P) : (P.hat T (Z.Az P T)).IsHermitian := by
  rw [hat_eq]; exact ZeroBlockData.isHermitian_real_smul (Az_isHermitian Z T P hconj) _

/-- **prop:block (i)**: "n₊(Ã) ≤ s₁ + s₂ + p" (Ã := A/L; any Hermitian-ness witness h). -/
theorem posIndex_tilde_Az_le (hconj : PhiHatConj T P) (hL : 0 < P.L T)
    (h : (P.tilde T (Z.Az P T)).IsHermitian) :
    posIndex h ≤ Z.s1 T + Z.s2 T + Z.p T := by
  rw [s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj),
    p_eq_mk Z T _ (evalVec_reflect hconj)]
  have h' : ((((P.L T)⁻¹ : ℝ) : ℂ) • (blockData Z T P hconj).blockA).IsHermitian := by
    rw [← Az_eq_blockA, ← tilde_eq]; exact h
  rw [ZeroBlockData.posIndex_congr h h' (by rw [tilde_eq, Az_eq_blockA Z T P hconj])]
  exact ZeroBlockData.posIndex_smul_blockA_le _ _ (inv_pos.mpr hL) h'

/-- **prop:block (i)**: "rank(Ã) ≤ s₁ + s₂ + 2p = #𝒵(I')". -/
theorem rank_tilde_Az_le (hconj : PhiHatConj T P) (hL : 0 < P.L T) :
    (P.tilde T (Z.Az P T)).rank ≤ Z.s1 T + Z.s2 T + 2 * Z.p T := by
  rw [s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj),
    p_eq_mk Z T _ (evalVec_reflect hconj), tilde_eq, Az_eq_blockA Z T P hconj]
  exact ZeroBlockData.rank_smul_blockA_le _ _ (by exact_mod_cast (inv_ne_zero hL.ne'))

/-- P of prop:block (ii): (aL²)⁻¹ Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ u_ρ u_ρᵀ. -/
def hatP (hconj : PhiHatConj T P) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  (blockData Z T P hconj).blockP (P.a T * P.L T ^ 2)

/-- Q of prop:block (ii): Â − P ("the sum of the pair contributions"). -/
def hatQ (hconj : PhiHatConj T P) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  (blockData Z T P hconj).blockQ (P.a T * P.L T ^ 2)

/-- **prop:block (ii)**: "Â = P + Q" with Â := A/(aL²) [eq:hatunits]. -/
theorem hat_Az_eq_hatP_add_hatQ (hconj : PhiHatConj T P) :
    P.hat T (Z.Az P T) = hatP Z T P hconj + hatQ Z T P hconj := by
  rw [hatP, hatQ, ZeroBlockData.blockP_add_blockQ, hat_eq, Az_eq_blockA Z T P hconj]

/-- **prop:block (ii)**: "P ⪰ 0". -/
theorem hatP_posSemidef (hconj : PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2) :
    (hatP Z T P hconj).PosSemidef :=
  ZeroBlockData.blockP_posSemidef _ hc

/-- **prop:block (ii)**: P "real symmetric" — real entries (Hermitian from hatP_posSemidef). -/
theorem star_hatP_apply (hconj : PhiHatConj T P) (k l : Fin (P.d T)) :
    star (hatP Z T P hconj k l) = hatP Z T P hconj k l :=
  ZeroBlockData.star_blockP_apply _ _ k l

/-- **prop:block (ii)**: "rank P ≤ s₁ + s₂". -/
theorem rank_hatP_le (hconj : PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2) :
    (hatP Z T P hconj).rank ≤ Z.s1 T + Z.s2 T := by
  rw [s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.rank_blockP_le _ hc

/-- The finite Poisson bound for an on-line zero ρ: Σ_{0≤k<d} |φ̂(γ_ρ − τ_k)|² ≤ aL²  (the terms are
≥ 0 and the full sum over k ∈ ℤ is exactly aL² by lem:poisson). -/
lemma sum_normSq_v_le (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (z : ZI Z T) (hz : z ∈ (blockData Z T P hconj).onLine) :
    ∑ k, ‖(blockData Z T P hconj).v z k‖ ^ 2 ≤ P.a T * P.L T ^ 2 := by
  rw [ZeroBlockData.mem_onLine] at hz
  have hz' : (z : ℂ).re = 1 / 2 := (mkData_σ_eq_iff Z T _ _ z).mp hz
  have hv : ∀ k : Fin (P.d T), ‖(blockData Z T P hconj).v z k‖ ^ 2
      = P.phiHatR T ((z : ℂ).im - P.tau T k) ^ 2 := by
    intro k
    simp only [blockData, mkData_v, evalVec]
    rw [gammaOf_of_re_eq_half hz', ← Complex.ofReal_sub, hreal, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hv]
  let e : Fin (P.d T) ↪ ℤ := ⟨fun k => ((k : ℕ) : ℤ), fun a b h => Fin.ext (by
    have h' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := h
    exact_mod_cast h')⟩
  have := sum_le_hasSum (Finset.univ.map e) (fun i _ => sq_nonneg _) (hPois (z : ℂ).im)
  rwa [sum_map] at this

/-- **prop:block (ii)**: "tr P ≤ N_on(I')" — "by Lemma [lem:poisson], tr P = (aL²)⁻¹ Σ m_ρ
Σ_{0≤k<d} φ̂(γ_ρ−τ_k)² ≤ (aL²)⁻¹ Σ m_ρ Σ_{k∈ℤ} φ̂(γ_ρ−τ_k)² = N_on(I')". -/
theorem rtrace_hatP_le (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    rtrace (hatP Z T P hconj) ≤ (Z.NonIprime T : ℝ) := by
  rw [NonIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.rtrace_blockP_le _ hc (sum_normSq_v_le Z T P hconj hreal hPois)

/-- **prop:block (ii)**: Q is Hermitian. -/
theorem hatQ_isHermitian (hconj : PhiHatConj T P) : (hatQ Z T P hconj).IsHermitian :=
  ZeroBlockData.blockQ_isHermitian _ _

/-- **prop:block (ii)**: Q "real symmetric" — real entries. -/
theorem star_hatQ_apply (hconj : PhiHatConj T P) (k l : Fin (P.d T)) :
    star (hatQ Z T P hconj k l) = hatQ Z T P hconj k l :=
  ZeroBlockData.star_blockQ_apply _ _ k l

/-- **prop:block (ii)**: "n₊(Q) ≤ p" (by lem:inertia), for any Hermitian-ness witness h. -/
theorem posIndex_hatQ_le (hconj : PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2)
    (h : (hatQ Z T P hconj).IsHermitian) : posIndex h ≤ Z.p T := by
  rw [p_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.posIndex_blockQ_le _ (mkPairReps Z T _ _) hc

end Inst

/-! ## Section 4. Packaging for Assembly: `Zeta23.Assembly.BlockInputs` -/

section Package

open Zeta23

/-- prop:block (i)+(ii) and [eq:Ncount] at height T, packaged exactly as `Assembly.thmA_abstract`
consumes them (p := Z.p T), from the explicit analytic hypotheses. See Zeta23/ZeroSide/Final.lean
for the version with the hypotheses discharged from Taper/Poisson. -/
theorem blockInputsAt (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hL : 0 < P.L T) (hc : 0 < P.a T * P.L T ^ 2) :
    Assembly.BlockInputs Z P T where
  hat := ⟨hatP Z T P hconj, hatQ Z T P hconj, Z.p T, hatP_posSemidef Z T P hconj hc,
    hatQ_isHermitian Z T P hconj, hat_Az_eq_hatP_add_hatQ Z T P hconj, rank_hatP_le Z T P hconj hc,
    rtrace_hatP_le Z T P hconj hreal hPois hc, posIndex_hatQ_le Z T P hconj hc _,
    by exact_mod_cast NonIprime_add_two_p_le_NIprime Z T⟩
  tilde := ⟨Z.p T, tilde_Az_isHermitian Z T P hconj, posIndex_tilde_Az_le Z T P hconj hL _,
    (ncard_ZIprime_eq Z T).symm ▸ rank_tilde_Az_le Z T P hconj hL,
    by exact_mod_cast s1_add_two_s2_add_two_p_le_NIprime Z T⟩

/-! ### The export for Main.lean: eventually-in-T form with only the genuinely external inputs left

hconj / hreal are discharged here from Zeta23.GzGp.phiHat_conj / phiHat_ofReal
(φ real and even); 0 < L eventually since L = λ·log(T/2π) → ∞. What remains as hypotheses, both in
∀ᶠ form: positivity of a [eq:abdef] (Main has it from Taper: 1 − 2w/L ≤ b ≤ a) and lem:poisson
(Zeta23.Poisson: Params.hasSum_phiHatR_sq). Zeta23/ZeroSide/Final.lean discharges those two as well. -/

/-- L = λ·log(T/2π) → ∞ as T → ∞ (for λ > 0). -/
lemma tendsto_L_atTop' (P : Params) (hlam : 0 < P.lam) : Filter.Tendsto P.L Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const (by positivity))
  exact (h.const_mul_atTop hlam).congr fun T => by simp [Params.L, l]

/-- **Export consumed by Main.lean**: prop:block + [eq:Ncount], eventually
in T, modulo only (ha) a > 0 eventually and (hPois) lem:poisson eventually. -/
theorem eventually_blockInputs_of (Z : ZeroConfig) (P : Params) (hP : P.Valid)
    (ha : ∀ᶠ T in Filter.atTop, 0 < P.a T) (hPois : ∀ᶠ T in Filter.atTop, PoissonSq T P) :
    ∀ᶠ T in Filter.atTop, Assembly.BlockInputs Z P T := by
  filter_upwards [ha, hPois, (tendsto_L_atTop' P hP.lam_pos).eventually_gt_atTop 0] with T haT hPT hLT
  exact blockInputsAt Z P T (fun z => GzGp.phiHat_conj P T z) (fun r => GzGp.phiHat_ofReal P T r) hPT
    hLT (mul_pos haT (pow_pos hLT 2))

end Package

end Zeta23.ZeroSide
