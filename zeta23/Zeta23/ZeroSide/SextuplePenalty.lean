/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ZeroSide
import Zeta23.ZeroSide.RankTraceMult
import Zeta23.LinAlg.SextuplePenalty

/-!
# The simple-zero sextuple penalty on the zero side

This file keeps only the simple on-line atoms in the positive-semidefinite
part of the normalized zero block.  The residual contains the multiple
on-line atoms and the reflected off-line pairs.  This is the exact split used
in K36, §2.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide

open RankTraceMult

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

namespace ZeroBlockData

variable (D : ZeroBlockData ι d)

/-- The unnormalized contribution from the simple on-line centers. -/
def simplePart : Matrix d d ℂ :=
  ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The unnormalized contribution from the multiple on-line centers. -/
def multiplePart : Matrix d d ℂ :=
  ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The normalized simple on-line vectors. -/
def simpleVhat (c : ℝ) : D.S₁ → d → ℂ :=
  fun z k => D.v z k / (Real.sqrt c : ℂ)

/-- The matrix whose columns are the normalized simple on-line vectors. -/
def simpleColumns (c : ℝ) : Matrix d D.S₁ ℂ :=
  Wmat (fun _ : D.S₁ => (1 : ℝ)) (D.simpleVhat c)

/-- The simple-zero column Gram matrix `WᴴW`. -/
def simpleGram (c : ℝ) : Matrix D.S₁ D.S₁ ℂ :=
  (D.simpleColumns c)ᴴ * D.simpleColumns c

/-- `P₁ = WWᴴ`, the normalized Gram contribution of the simple on-line centers. -/
def simpleBlockP (c : ℝ) : Matrix d d ℂ :=
  D.simpleColumns c * (D.simpleColumns c)ᴴ

/-- `Q = c⁻¹ A - P₁`. -/
def simpleBlockQ (c : ℝ) : Matrix d d ℂ :=
  (((c⁻¹ : ℝ) : ℂ) • D.blockA) - D.simpleBlockP c

/-- The proof-independent simple-zero spectral penalty, computed on `WᴴW`.
The column index type has exactly `s₁` elements, so this is already the
zero-padded sum of length `s₁`. -/
def blockSextuplePenalty (c : ℝ) : ℝ :=
  ∑ i, sextuplePenalty ((Matrix.posSemidef_conjTranspose_mul_self
    (D.simpleColumns c)).isHermitian.eigenvalues i)

lemma mem_onLine_of_mem_S₁ {z : ι} (hz : z ∈ D.S₁) : z ∈ D.onLine := by
  rw [D.mem_onLine]
  have h : D.σ z = z ∧ D.m z = 1 := by
    simpa only [S₁, mem_filter, mem_univ, true_and] using hz
  exact h.1

lemma mem_onLine_of_mem_S₂ {z : ι} (hz : z ∈ D.S₂) : z ∈ D.onLine := by
  rw [D.mem_onLine]
  have h : D.σ z = z ∧ 2 ≤ D.m z := by
    simpa only [S₂, mem_filter, mem_univ, true_and] using hz
  exact h.1

lemma m_eq_one_of_mem_S₁ {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
  have h : D.σ z = z ∧ D.m z = 1 := by
    simpa only [S₁, mem_filter, mem_univ, true_and] using hz
  exact h.2

/-- The on-line block splits exactly into its simple and multiple parts. -/
lemma onPart_eq_simplePart_add_multiplePart :
    D.onPart = D.simplePart + D.multiplePart := by
  unfold onPart simplePart multiplePart
  rw [D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂]

lemma simplePart_posSemidef : D.simplePart.PosSemidef := by
  unfold simplePart
  refine posSemidef_sum _ fun z hz => ?_
  exact posSemidef_smul_vecMulVec
    (D.star_v_of_onLine ((D.mem_onLine_of_mem_S₁ hz |> D.mem_onLine.mp)))
    (Nat.cast_nonneg (D.m z))

lemma multiplePart_posSemidef : D.multiplePart.PosSemidef := by
  unfold multiplePart
  refine posSemidef_sum _ fun z hz => ?_
  exact posSemidef_smul_vecMulVec
    (D.star_v_of_onLine ((D.mem_onLine_of_mem_S₂ hz |> D.mem_onLine.mp)))
    (Nat.cast_nonneg (D.m z))

lemma rank_multiplePart_le : D.multiplePart.rank ≤ D.s₂ := by
  unfold multiplePart s₂
  refine (rank_sum_le _ _ (fun _ => 1)
    fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

/-- `WWᴴ` is positive semidefinite, without any positivity assumption on `c`. -/
theorem simpleBlockP_posSemidef (c : ℝ) : (D.simpleBlockP c).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The simple Gram has the canonical positive-semidefinite witness. -/
theorem simpleGram_posSemidef (c : ℝ) : (D.simpleGram c).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `rank P₁ ≤ s₁`, since `P₁` factors through its `s₁` columns. -/
theorem rank_simpleBlockP_le (c : ℝ) : (D.simpleBlockP c).rank ≤ D.s₁ := by
  calc
    (D.simpleBlockP c).rank ≤ (D.simpleColumns c).rank := by
      exact rank_mul_le_left _ _
    _ ≤ Fintype.card D.S₁ := Matrix.rank_le_card_width _
    _ = D.s₁ := by simp [s₁]

/-- For `c > 0`, `WWᴴ` is exactly the normalized simple contribution. -/
theorem simpleBlockP_eq_smul_simplePart {c : ℝ} (hc : 0 < c) :
    D.simpleBlockP c = (((c⁻¹ : ℝ) : ℂ) • D.simplePart) := by
  ext a b
  change Pmat (fun _ : D.S₁ => (1 : ℝ)) (D.simpleVhat c) a b = _
  rw [Pmat_apply (fun _ => by norm_num)]
  simp only [simplePart, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    smul_eq_mul, simpleVhat, Finset.mul_sum]
  rw [← Finset.sum_coe_sort D.S₁]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzOn : D.σ z = z := D.mem_onLine.mp (D.mem_onLine_of_mem_S₁ z.2)
  have hreal : starRingEnd ℂ (D.v z b) = D.v z b := by
    have h := congrFun (D.star_v_of_onLine hzOn) b
    rwa [Pi.star_apply, RCLike.star_def] at h
  have hm : D.m z = 1 := D.m_eq_one_of_mem_S₁ z.2
  rw [map_div₀, hreal, Complex.conj_ofReal, hm]
  norm_num
  have hsq : ((Real.sqrt c : ℂ)) ^ 2 = (c : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  have hsqrt : (Real.sqrt c : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [div_mul_div_comm, ← sq, hsq]
  field_simp

/-- The residual is Hermitian. -/
theorem simpleBlockQ_isHermitian (c : ℝ) : (D.simpleBlockQ c).IsHermitian :=
  (isHermitian_real_smul D.blockA_isHermitian _).sub
    (D.simpleBlockP_posSemidef c).isHermitian

/-- The residual consists of the normalized multiple on-line block plus the
old reflected-pair residual. -/
theorem simpleBlockQ_eq (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    D.simpleBlockQ c = (((c⁻¹ : ℝ) : ℂ) • D.multiplePart) + D.blockQ c := by
  rw [simpleBlockQ, D.simpleBlockP_eq_smul_simplePart hc, ← smul_sub]
  rw [D.blockA_decomp Pr, D.onPart_eq_simplePart_add_multiplePart]
  rw [add_assoc, add_sub_cancel_left, smul_add, D.blockQ_eq Pr]

/-- The positive index of the residual is at most one direction per multiple
on-line center and one direction per reflected off-line pair. -/
theorem posIndex_simpleBlockQ_le (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (D.simpleBlockQ_isHermitian c) ≤ D.s₂ + Pr.p := by
  let M : Matrix d d ℂ := (((c⁻¹ : ℝ) : ℂ) • D.multiplePart)
  have hM : M.PosSemidef :=
    D.multiplePart_posSemidef.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  have hrM : M.rank ≤ D.s₂ := by
    have hne : (((c⁻¹ : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (inv_ne_zero hc.ne')
    calc
      M.rank = D.multiplePart.rank := by
        dsimp [M]
        exact rank_smul_of_ne_zero D.multiplePart hne
      _ ≤ D.s₂ := D.rank_multiplePart_le
  have hEq : D.simpleBlockQ c = M + D.blockQ c := D.simpleBlockQ_eq Pr hc
  calc
    posIndex (D.simpleBlockQ_isHermitian c) =
        posIndex (hM.isHermitian.add (D.blockQ_isHermitian c)) :=
      posIndex_congr _ _ hEq
    _ ≤ posIndex hM.isHermitian + posIndex (D.blockQ_isHermitian c) :=
      posIndex_add_le _ _
    _ ≤ D.s₂ + Pr.p := Nat.add_le_add
      ((posIndex_eq_rank_of_posSemidef hM).le.trans hrM)
      (D.posIndex_blockQ_le Pr hc)

/-- `P₁ + Q = c⁻¹ A`. -/
theorem simpleBlockP_add_simpleBlockQ (c : ℝ) :
    D.simpleBlockP c + D.simpleBlockQ c = (((c⁻¹ : ℝ) : ℂ) • D.blockA) := by
  unfold simpleBlockQ
  abel

/-- The truncated Poisson norm bound gives `tr P₁ ≤ s₁`. -/
theorem rtrace_simpleBlockP_le {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (D.simpleBlockP c) ≤ (D.s₁ : ℝ) := by
  change rtrace (Pmat (fun _ : D.S₁ => (1 : ℝ)) (D.simpleVhat c)) ≤ _
  rw [rtrace_Pmat (fun _ => by norm_num)]
  simp only [one_mul]
  calc
    ∑ z : D.S₁, xsq (D.simpleVhat c) z ≤ ∑ _z : D.S₁, (1 : ℝ) := by
      exact Finset.sum_le_sum fun z _ => by
        unfold xsq simpleVhat
        have hs : ∀ k, ‖D.v z k / (Real.sqrt c : ℂ)‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
          intro k
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.sqrt_pos.mpr hc), div_pow, Real.sq_sqrt hc.le]
        simp_rw [hs]
        rw [← Finset.sum_div, div_le_one hc]
        exact hPois z (D.mem_onLine_of_mem_S₁ z.2)
    _ = (D.s₁ : ℝ) := by simp [s₁]

/-- The exact K36 count budget `tr P₁ + 2(s₂+p) ≤ N(I')`. -/
theorem rtrace_simpleBlockP_add_two_budget_le (Pr : D.PairReps) {c : ℝ}
    (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (D.simpleBlockP c) + 2 * ((D.s₂ + Pr.p : ℕ) : ℝ) ≤ (D.Ncount : ℝ) := by
  have htr := D.rtrace_simpleBlockP_le hc hPois
  have hcount : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  push_cast at hcount ⊢
  linarith

/-- The zero-padded spectrum of `P₁=WWᴴ` equals the ordinary spectral sum on
`K=WᴴW`.  The transfer is applied to `sextuplePenalty - 1`, whose value at
zero is zero. -/
theorem paddedPenalty_simpleBlockP_eq_blockSextuplePenalty (c : ℝ) :
    paddedSextuplePenalty (D.simpleBlockP_posSemidef c).isHermitian D.s₁ =
      D.blockSextuplePenalty c := by
  have htransfer₀ := sum_eigenvalues_comm (D.simpleColumns c)
    (fun x => sextuplePenalty x - 1) (by simp)
  have htransfer :
      (∑ i, (sextuplePenalty
          ((D.simpleBlockP_posSemidef c).isHermitian.eigenvalues i) - 1)) =
        ∑ j, (sextuplePenalty
          ((D.simpleGram_posSemidef c).isHermitian.eigenvalues j) - 1) := by
    simpa only [simpleBlockP_posSemidef, simpleGram_posSemidef,
      simpleBlockP, simpleGram] using htransfer₀
  unfold paddedSextuplePenalty sextupleSpectralRemainder blockSextuplePenalty
  rw [htransfer]
  have hcard : Fintype.card D.S₁ = D.s₁ := by simp [s₁]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ]
  rw [hcard]
  ring_nf
  congr 1

/-- **Strengthened simple-line block inequality (K36 §2).** -/
theorem sextuplePenalty_block (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace ((((c⁻¹ : ℝ) : ℂ) • D.blockA))
      - frobSq ((((c⁻¹ : ℝ) : ℂ) • D.blockA))
      - 2 * (D.Ncount : ℝ) + D.blockSextuplePenalty c ≤ (D.s₁ : ℝ) := by
  have hRT := rank_trace_ineq_two_sextuplePenalty
    (D.simpleBlockP_posSemidef c) (D.simpleBlockQ_isHermitian c)
    (D.rank_simpleBlockP_le c) (D.posIndex_simpleBlockQ_le Pr hc)
  rw [D.paddedPenalty_simpleBlockP_eq_blockSextuplePenalty c] at hRT
  have hbudget := D.rtrace_simpleBlockP_add_two_budget_le Pr hc hPois
  rw [← D.simpleBlockP_add_simpleBlockQ c, rtrace_add]
  push_cast at hRT hbudget ⊢
  linarith

end ZeroBlockData
end Block

/-! ## Concrete zero block and proof-free column Gram -/

section Inst

open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- The canonical block data, using the proved conjugation identity.  Unlike
`blockData`, this definition has no proof argument. -/
def sextupleBlockData : ZeroBlockData (ZI Z T) (Fin (P.d T)) :=
  blockData Z T P (fun z => GzGp.phiHat_conj P T z)

/-- The actual normalized simple-zero column matrix for `𝒮₁(I')`. -/
def simpleZeroColumns :
    Matrix (Fin (P.d T)) (sextupleBlockData Z T P).S₁ ℂ :=
  (sextupleBlockData Z T P).simpleColumns (P.a T * P.L T ^ 2)

/-- The proof-free simple-zero Gram matrix `K=WᴴW`. -/
def simpleZeroGram :
    Matrix (sextupleBlockData Z T P).S₁ (sextupleBlockData Z T P).S₁ ℂ :=
  (simpleZeroColumns Z T P)ᴴ * simpleZeroColumns Z T P

/-- The proof-free concrete spectral penalty at `(Z,P,T)`. -/
def simpleSextuplePenalty : ℝ :=
  ∑ i, sextuplePenalty ((Matrix.posSemidef_conjTranspose_mul_self
    (simpleZeroColumns Z T P)).isHermitian.eigenvalues i)

@[simp] theorem simpleZeroColumns_apply (k : Fin (P.d T))
    (z : (sextupleBlockData Z T P).S₁) :
    simpleZeroColumns Z T P k z =
      evalVec Z T P z k / (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) := by
  simp [simpleZeroColumns, sextupleBlockData, ZeroBlockData.simpleColumns,
    ZeroBlockData.simpleVhat, Wmat, blockData, mkData_v]

/-- The concrete Gram is positive semidefinite. -/
theorem simpleZeroGram_posSemidef : (simpleZeroGram Z T P).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The scalar penalty is exactly the spectral sum on `simpleZeroGram`. -/
theorem simpleSextuplePenalty_eq_gram :
    simpleSextuplePenalty Z T P =
      ∑ i, sextuplePenalty
        ((simpleZeroGram_posSemidef Z T P).isHermitian.eigenvalues i) := by
  rfl

/-- The concrete sextuple penalty is nonnegative. -/
theorem simpleSextuplePenalty_nonneg : 0 ≤ simpleSextuplePenalty Z T P := by
  exact Finset.sum_nonneg fun i _ => sextuplePenalty_nonneg _

/-- The normalized simple-only positive part. -/
def hatP1 : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  (sextupleBlockData Z T P).simpleBlockP (P.a T * P.L T ^ 2)

/-- The complementary normalized residual. -/
def hatQ1 : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  (sextupleBlockData Z T P).simpleBlockQ (P.a T * P.L T ^ 2)

lemma blockSextuplePenalty_eq_simpleSextuplePenalty :
    (sextupleBlockData Z T P).blockSextuplePenalty (P.a T * P.L T ^ 2) =
      simpleSextuplePenalty Z T P := by
  rfl

lemma blockData_eq_sextupleBlockData (hconj : PhiHatConj T P) :
    blockData Z T P hconj = sextupleBlockData Z T P := by
  unfold sextupleBlockData
  congr

/-- The normalized AF zero block is `hatP1 + hatQ1`. -/
theorem hat_Az_eq_hatP1_add_hatQ1 :
    P.hat T (Z.Az P T) = hatP1 Z T P + hatQ1 Z T P := by
  rw [hatP1, hatQ1, ZeroBlockData.simpleBlockP_add_simpleBlockQ]
  rw [hat_eq, Az_eq_blockA Z T P (fun z => GzGp.phiHat_conj P T z)]
  rfl

/-- `hatP1` is positive semidefinite. -/
theorem hatP1_posSemidef : (hatP1 Z T P).PosSemidef :=
  ZeroBlockData.simpleBlockP_posSemidef _ _

/-- Concrete `WWᴴ`/`WᴴW` padding bridge. -/
theorem paddedPenalty_hatP1_eq_simpleSextuplePenalty :
    paddedSextuplePenalty (hatP1_posSemidef Z T P).isHermitian (Z.s1 T) =
      simpleSextuplePenalty Z T P := by
  have hs : Z.s1 T = (sextupleBlockData Z T P).s₁ := by
    change Z.s1 T = (mkData Z T (evalVec Z T P)
      (evalVec_reflect (fun z => GzGp.phiHat_conj P T z))).s₁
    exact s1_eq_mk Z T (evalVec Z T P)
      (evalVec_reflect (fun z => GzGp.phiHat_conj P T z))
  rw [hs]
  change paddedSextuplePenalty
      ((sextupleBlockData Z T P).simpleBlockP_posSemidef
        (P.a T * P.L T ^ 2)).isHermitian
      (sextupleBlockData Z T P).s₁ = simpleSextuplePenalty Z T P
  calc
    _ = (sextupleBlockData Z T P).blockSextuplePenalty
        (P.a T * P.L T ^ 2) :=
      ZeroBlockData.paddedPenalty_simpleBlockP_eq_blockSextuplePenalty _ _
    _ = simpleSextuplePenalty Z T P :=
      blockSextuplePenalty_eq_simpleSextuplePenalty Z T P

/-- `rank hatP1 ≤ s₁(I')`. -/
theorem rank_hatP1_le : (hatP1 Z T P).rank ≤ Z.s1 T := by
  rw [hatP1, s1_eq_mk Z T _ (evalVec_reflect (fun z => GzGp.phiHat_conj P T z))]
  exact ZeroBlockData.rank_simpleBlockP_le _ _

/-- `hatQ1` is Hermitian. -/
theorem hatQ1_isHermitian : (hatQ1 Z T P).IsHermitian :=
  ZeroBlockData.simpleBlockQ_isHermitian _ _

/-- The residual has at most `s₂+p` positive directions. -/
theorem posIndex_hatQ1_le (hc : 0 < P.a T * P.L T ^ 2) :
    posIndex (hatQ1_isHermitian Z T P) ≤ Z.s2 T + Z.p T := by
  change posIndex ((sextupleBlockData Z T P).simpleBlockQ_isHermitian
    (P.a T * P.L T ^ 2)) ≤ Z.s2 T + Z.p T
  rw [s2_eq_mk Z T _ (evalVec_reflect (fun z => GzGp.phiHat_conj P T z)),
    p_eq_mk Z T _ (evalVec_reflect (fun z => GzGp.phiHat_conj P T z))]
  exact ZeroBlockData.posIndex_simpleBlockQ_le _ (mkPairReps Z T _ _) hc

/-- The concrete exact trace/count budget. -/
theorem rtrace_hatP1_add_two_budget_le
    (hPois : PoissonSq T P) (hc : 0 < P.a T * P.L T ^ 2) :
    rtrace (hatP1 Z T P) + 2 * ((Z.s2 T + Z.p T : ℕ) : ℝ) ≤ (Z.NIprime T : ℝ) := by
  let hconj : PhiHatConj T P := fun z => GzGp.phiHat_conj P T z
  let hreal : PhiHatReal T P := fun r => GzGp.phiHat_ofReal P T r
  rw [hatP1, s2_eq_mk Z T _ (evalVec_reflect hconj),
    p_eq_mk Z T _ (evalVec_reflect hconj),
    NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.rtrace_simpleBlockP_add_two_budget_le _
    (mkPairReps Z T _ _) hc (sum_normSq_v_le Z T P hconj hreal hPois)

/-- **Concrete strengthened AF block inequality.** -/
theorem hatAz_sextuplePenalty (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ) + simpleSextuplePenalty Z T P ≤ (Z.s1 T : ℝ) := by
  let hconj : PhiHatConj T P := fun z => GzGp.phiHat_conj P T z
  let hreal : PhiHatReal T P := fun r => GzGp.phiHat_ofReal P T r
  have h := ZeroBlockData.sextuplePenalty_block
    (blockData Z T P hconj) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
  unfold blockData at h
  rw [← NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    ← s1_eq_mk Z T _ (evalVec_reflect hconj)] at h
  rw [← blockSextuplePenalty_eq_simpleSextuplePenalty Z T P]
  rw [hat_eq, Az_eq_blockA Z T P hconj]
  exact h

/-- Short name for the concrete strengthened AF block inequality. -/
theorem hatAz_sextuple (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ) + simpleSextuplePenalty Z T P ≤ (Z.s1 T : ℝ) :=
  hatAz_sextuplePenalty Z T P hPois hc

end Inst

end Zeta23.ZeroSide
