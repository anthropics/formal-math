/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide/Mult.lean — the multiplicity-aware zero side: Lemma R (Zeta23/ZeroSide/RankTraceMult.lean) applied to the block
structure of Zeta23/ZeroSide.lean.  At the level of 𝒵(I′) (abstract ZeroBlockData, then the concrete Â = hat(A_z)):
   c = 2:  4·tr Â − ‖Â‖_F² − 2·N(I′) ≤ s₁                     (simple zeros on the line)
   c = 3:  6·tr Â − ‖Â‖_F² − 3·N(I′) ≤ 2·#𝒵(I′) = 2·N_d(I′)      (distinct zeros)
using only ‖v_ρ‖² ≤ aL² (the truncated Poisson sum, no edge leak) and n₊(Q) ≤ p.
-/
import Zeta23.ZeroSide
import Zeta23.ZeroSide.RankTraceMult

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

/-- the normalized on-line vectors v_z/√c (c = aL²) over the on-line index subtype. -/
def vhat (c : ℝ) : D.onLine → d → ℂ := fun z k => D.v z k / (Real.sqrt c : ℂ)

/-- the on-line multiplicities as reals. -/
def mhat : D.onLine → ℝ := fun z => (D.m z : ℝ)

lemma mhat_nonneg (z : D.onLine) : 0 ≤ D.mhat z := Nat.cast_nonneg _

/-- blockP c = Pmat (multiplicities) (normalized on-line vectors). -/
theorem blockP_eq_Pmat {c : ℝ} (hc : 0 < c) : D.blockP c = Pmat (𝕜 := ℂ) D.mhat (D.vhat c) := by
  ext a b
  rw [Pmat_apply (fun z => D.mhat_nonneg z)]
  simp only [blockP, onPart, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_coe_sort D.onLine]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : D.σ z = z := (D.mem_onLine).mp z.2
  have hreal : starRingEnd ℂ (D.v z b) = D.v z b := by
    have := congrFun (D.star_v_of_onLine hz) b
    rwa [Pi.star_apply, RCLike.star_def] at this
  simp only [mhat, vhat]
  rw [map_div₀, hreal, Complex.conj_ofReal]
  have hsq : ((Real.sqrt c : ℂ)) ^ 2 = (c : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  have hc0 : (Real.sqrt c : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [div_mul_div_comm, ← sq, hsq]
  push_cast
  field_simp

/-- ‖v_z/√c‖² ≤ 1 from the truncated Poisson bound Σ_k‖v_z k‖² ≤ c. -/
lemma xsq_vhat_le {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (z : D.onLine) :
    xsq (D.vhat c) z ≤ 1 := by
  unfold xsq vhat
  have hs : ∀ k, ‖D.v z k / (Real.sqrt c : ℂ)‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
    intro k
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc), div_pow,
      Real.sq_sqrt hc.le]
  simp_rw [hs]
  rw [← Finset.sum_div, div_le_one hc]
  exact hPois z z.2

/-- #{z on-line : m z = 1} = s₁. -/
lemma card_onLine_m_eq_one : (D.onLine.filter (fun z => D.m z = 1)).card = D.s₁ := by
  unfold s₁ S₁ onLine
  rw [Finset.filter_filter]

/-- counting over the on-line SUBTYPE equals counting over the Finset. -/
lemma card_sub_filter (q : ℕ → Prop) [DecidablePred q] :
    ((Finset.univ : Finset D.onLine).filter (fun z : D.onLine => q (D.m z))).card
      = (D.onLine.filter (fun z => q (D.m z))).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1; ext z
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
  · rintro ⟨hz, hm⟩; exact ⟨⟨z, hz⟩, hm, rfl⟩

lemma card_two_add_card_ge_three :
    (D.onLine.filter (fun z => D.m z = 2)).card + (D.onLine.filter (fun z => 3 ≤ D.m z)).card = D.s₂ := by
  unfold s₂ S₂
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext z
    simp only [Finset.mem_union, Finset.mem_filter, onLine, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, hm⟩ | ⟨h, hm⟩) <;> exact ⟨h, by omega⟩
    · rintro ⟨h, hm⟩
      rcases Nat.lt_or_ge (D.m z) 3 with h3 | h3
      · left; exact ⟨h, by omega⟩
      · right; exact ⟨h, h3⟩
  · rw [Finset.disjoint_filter]; intro z _ h; omega

lemma Non_ge_weighted :
    ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ) + 2 * (D.onLine.filter (fun z => D.m z = 2)).card
      + 3 * (D.onLine.filter (fun z => 3 ≤ D.m z)).card ≤ (D.Non : ℝ) := by
  unfold Non
  have key : ∀ z ∈ D.onLine, ((if D.m z = 1 then 1 else 0) + 2 * (if D.m z = 2 then 1 else 0)
      + 3 * (if 3 ≤ D.m z then 1 else 0) : ℝ) ≤ (D.m z : ℝ) := by
    intro z _
    have h1 := D.one_le_m z
    by_cases a : D.m z = 1
    · simp [a]
    by_cases b : D.m z = 2
    · simp [b]
    have c3 : 3 ≤ D.m z := by omega
    rw [if_neg a, if_neg b, if_pos c3]; norm_num
    exact_mod_cast c3
  have := Finset.sum_le_sum key
  rw [Nat.cast_sum]
  refine le_trans (le_of_eq ?_) this
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]

/-- **c = 2 at the block level**:  4·tr Â − ‖Â‖² − 2N(I′) ≤ s₁   (Â := c⁻¹·A = blockP + blockQ, c = aL²). -/
theorem mult_two (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ) ≤ (D.s₁ : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c) (D.xsq_vhat_le hc hPois)
    (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc) (c := 2) (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  have hk : ∑ z : D.onLine, kc 2 (D.mhat z) = 3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) := by
    have := sum_kc_two_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => 2 ≤ n), D.card_onLine_m_eq_one]
    have h2 : (D.onLine.filter (fun z => 2 ≤ D.m z)).card = D.s₂ := by
      unfold s₂ S₂ onLine; rw [Finset.filter_filter]
    rw [h2]
  have hN := D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hN' : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by exact_mod_cast hN
  rw [hk] at hR
  norm_num at hR
  linarith

/-- **c = 3 at the block level**:  6·tr Â − ‖Â‖² − 3N(I′) ≤ 2·#𝒵(I′). -/
theorem mult_three (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    6 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 3 * (D.Ncount : ℝ)
      ≤ 2 * (Fintype.card ι : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c) (D.xsq_vhat_le hc hPois)
    (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc) (c := 3) (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  set a₁ : ℝ := ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ)
  set a₂ : ℝ := ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ)
  set a₃ : ℝ := ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ)
  have hk : ∑ z : D.onLine, kc 3 (D.mhat z) = 5 * a₁ + 8 * a₂ + 9 * a₃ := by
    have := sum_kc_three_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => n = 2), D.card_sub_filter (fun n => 3 ≤ n)]
  have hs1 : a₁ = D.s₁ := by simp only [a₁]; rw [D.card_onLine_m_eq_one]
  have hs2 : a₂ + a₃ = D.s₂ := by simp only [a₂, a₃]; exact_mod_cast D.card_two_add_card_ge_three
  have hNon : a₁ + 2 * a₂ + 3 * a₃ ≤ D.Non := D.Non_ge_weighted
  have hN : (D.Non : ℝ) + 2 * Pr.p ≤ D.Ncount := by exact_mod_cast D.Non_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card ι : ℝ) = D.s₁ + D.s₂ + 2 * Pr.p := by exact_mod_cast D.card_eq Pr
  have ha₂ : 0 ≤ a₂ := Nat.cast_nonneg _
  have ha₃ : 0 ≤ a₃ := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ Pr.p := Nat.cast_nonneg _
  rw [hk] at hR
  norm_num at hR
  linarith

end ZeroBlockData
end Block

/-! ### the concrete Â = hat(A_z) -/

section Inst
open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- **c = 2**: 4·tr Â − ‖Â‖_F² − 2·N(I′) ≤ s₁(I′)   for Â = P.hat T (Z.Az P T). -/
theorem hatAz_mult2 (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ) ≤ (Z.s1 T : ℝ) := by
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    s1_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.mult_two _ (mkPairReps Z T _ _) hc (sum_normSq_v_le Z T P hconj hreal hPois)

/-- **c = 3**: 6·tr Â − ‖Â‖_F² − 3·N(I′) ≤ 2·#𝒵(I′) = 2·N_d(I′). -/
theorem hatAz_mult3 (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    6 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T)) - 3 * (Z.NIprime T : ℝ)
      ≤ 2 * ((Z.ZIprime T).ncard : ℝ) := by
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    ncard_ZIprime_eq, s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj),
    p_eq_mk Z T _ (evalVec_reflect hconj)]
  have h := ZeroBlockData.mult_three _ (mkPairReps Z T _ (evalVec_reflect hconj)) hc (sum_normSq_v_le Z T P hconj hreal hPois)
  rw [ZeroBlockData.card_eq _ (mkPairReps Z T _ (evalVec_reflect hconj))] at h
  exact_mod_cast h

end Inst

end Zeta23.ZeroSide
