/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ZeroSide.Mult
import Zeta23.Defs.UnionCounting

/-!
# Multiplicity-aware zero-side inequality for the union count

The coefficient is sharp for the available block data.  Simple off-line pairs and
reflected pairs of double zeros are simultaneous equality cases.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide

open RankTraceMult

/-- The rank-trace parameter `2 + √2`. -/
def unionC : ℝ := 2 + Real.sqrt 2

/-- The bad-mass coefficient `3/2 + √2`. -/
def unionQ : ℝ := 3 / 2 + Real.sqrt 2

lemma unionC_pos : 0 < unionC := by
  unfold unionC
  positivity

lemma unionQ_pos : 0 < unionQ := by
  unfold unionQ
  positivity

lemma unionC_sq : unionC ^ 2 = 2 * (2 * unionC - 1) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold unionC
  nlinarith

lemma unionC_sq_eq_four_unionQ : unionC ^ 2 = 4 * unionQ := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold unionC unionQ
  nlinarith

lemma union_coeff_sub : 2 * unionC - 1 - unionQ = unionQ := by
  unfold unionC unionQ
  ring

lemma union_coeff_eq_two_unionQ : 2 * unionC - 1 = 2 * unionQ := by
  unfold unionC unionQ
  ring

lemma two_unionC_eq_one_add_two_unionQ : 2 * unionC = 1 + 2 * unionQ := by
  linarith [union_coeff_eq_two_unionQ]

lemma unionC_le_four : unionC ≤ 4 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold unionC
  nlinarith

lemma two_le_unionQ : 2 ≤ unionQ := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold unionQ
  nlinarith

lemma unionQ_le_three : unionQ ≤ 3 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold unionQ
  nlinarith

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

namespace ZeroBlockData

variable (D : ZeroBlockData ι d)

/-- Number of simple off-line reflected pairs. -/
def simplePairs (P : D.PairReps) : ℕ := #(P.R.filter fun z => D.m z = 1)

/-- Multiplicity mass of all off-line multiple zeros, including both reflected points. -/
def badMass (P : D.PairReps) : ℕ :=
  2 * ∑ z ∈ P.R.filter (fun z => 2 ≤ D.m z), D.m z

/-- Multiplicity mass of zeros that are simple or fixed by reflection. -/
def unionMass (P : D.PairReps) : ℕ := D.Non + 2 * D.simplePairs P

/-- The union mass and bad mass partition the total multiplicity. -/
theorem Ncount_eq_unionMass_add_badMass (P : D.PairReps) :
    D.Ncount = D.unionMass P + D.badMass P := by
  classical
  unfold Ncount unionMass simplePairs badMass Non
  rw [D.sum_split P]
  simp_rw [D.m_σ]
  have hpoint : ∀ z : ι, D.m z + D.m z =
      2 * (if D.m z = 1 then 1 else 0) +
        2 * (if 2 ≤ D.m z then D.m z else 0) := by
    intro z
    rcases Nat.lt_or_ge (D.m z) 2 with h | h
    · have hm : D.m z = 1 := by have := D.one_le_m z; omega
      simp [hm]
    · have hm : D.m z ≠ 1 := by omega
      simp [hm, h]
      omega
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, ← Finset.sum_filter]
  simp only [Nat.cast_id]
  omega

/-- Scalar bound for every positive on-line multiplicity. -/
lemma kc_unionC_nat_le (m : ℕ) (hm : 1 ≤ m) :
    kc unionC (m : ℝ) ≤ (2 * unionC - 1) * m := by
  by_cases h1 : m = 1
  · subst m
    rw [kc_of_le]
    · norm_num
    · unfold unionC
      have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      norm_num
      linarith
  · have hm2 : 2 ≤ m := by omega
    have hk : kc unionC (m : ℝ) ≤ unionC ^ 2 := by
      unfold kc
      nlinarith [sq_nonneg (max (unionC - (m : ℝ)) 0)]
    have hc : 0 < 2 * unionC - 1 := by
      unfold unionC
      have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    rw [unionC_sq] at hk
    nlinarith

/-- Scalar bound for one off-line pair. -/
lemma pair_unionC_le (m : ℕ) (hm : 1 ≤ m) :
    unionC ^ 2 ≤
      2 * (2 * unionC - 1) * m - unionQ * (if 2 ≤ m then 2 * m else 0) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst m
    simp only [Nat.reduceLeDiff, ↓reduceIte, Nat.cast_one, Nat.cast_zero, mul_zero]
    rw [unionC_sq]
    norm_num
  · rw [if_pos h]
    have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast h
    rw [unionC_sq_eq_four_unionQ]
    have hq := unionQ_pos
    have hcoeff := union_coeff_sub
    push_cast
    nlinarith


/-- The positive-index charge of an off-line pair is paid by its good mass when simple
and by its bad mass otherwise. -/
lemma pair_charge_unionC_le (m : ℕ) (hm : 1 ≤ m) :
    unionC ^ 2 ≤
      (2 * unionC - 1) * 2 * (if m = 1 then (1 : ℝ) else 0) +
        unionQ * 2 * (if 2 ≤ m then (m : ℝ) else 0) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst m
    norm_num
    rw [unionC_sq]
    ring_nf
    exact le_rfl
  · have hm1 : m ≠ 1 := by omega
    rw [if_neg hm1, if_pos h]
    simp only [mul_zero, zero_add]
    rw [unionC_sq_eq_four_unionQ]
    have hq := unionQ_pos
    have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith

/-- Bookkeeping specialization of Lemma R at `2 + √2`. -/
theorem kc_union_bookkeeping_le (P : D.PairReps) :
    (∑ z : D.onLine, kc unionC (D.mhat z)) + unionC ^ 2 * (P.p : ℝ)
      ≤ (2 * unionC - 1) * (D.unionMass P : ℝ) + unionQ * (D.badMass P : ℝ) := by
  classical
  have hon : (∑ z : D.onLine, kc unionC (D.mhat z))
      ≤ (2 * unionC - 1) * (D.Non : ℝ) := by
    unfold Non mhat
    rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_coe_sort D.onLine]
    exact Finset.sum_le_sum fun z _ => kc_unionC_nat_le (D.m z) (D.one_le_m z)
  have hpairs : unionC ^ 2 * (P.p : ℝ)
      ≤ (2 * unionC - 1) * (2 * D.simplePairs P : ℝ) +
        unionQ * (D.badMass P : ℝ) := by
    unfold PairReps.p simplePairs badMass
    push_cast
    calc
      unionC ^ 2 * (#P.R : ℝ) = ∑ z ∈ P.R, unionC ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ z ∈ P.R, ((2 * unionC - 1) * 2 *
          (if D.m z = 1 then (1 : ℝ) else 0) +
            unionQ * 2 * (if 2 ≤ D.m z then (D.m z : ℝ) else 0)) := by
        exact Finset.sum_le_sum fun z _ => pair_charge_unionC_le (D.m z) (D.one_le_m z)
      _ = (2 * unionC - 1) * (2 * (#({z ∈ P.R | D.m z = 1}) : ℝ)) +
          unionQ * (2 * ∑ z ∈ P.R with 2 ≤ D.m z, (D.m z : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_boole, ← Finset.sum_filter]
        ring
  unfold unionMass
  push_cast at hon hpairs ⊢
  nlinarith

/-- **Union block inequality.**  This is the leak-free finite-compression-safe replacement
for the false coefficient-three depth inequality. -/
theorem union_rank_trace (P : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    2 * unionC * rtrace (D.blockP c + D.blockQ c) -
        frobSq (D.blockP c + D.blockQ c)
      ≤ (2 * unionC - 1) * (D.unionMass P : ℝ) + unionQ * (D.badMass P : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ)
    (fun z => D.mhat_nonneg z) (D.vhat c) (D.xsq_vhat_le hc hPois)
    (D.blockQ_isHermitian c) (D.posIndex_blockQ_le P hc)
    (c := unionC) unionC_pos
  rw [← D.blockP_eq_Pmat hc] at hR
  exact hR.trans (D.kc_union_bookkeeping_le P)

/-- The union rank-trace bound in total/bad-mass form. -/
theorem union_rank_trace_Ncount (P : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    2 * unionC * rtrace (D.blockP c + D.blockQ c) -
        frobSq (D.blockP c + D.blockQ c)
      ≤ (2 * unionC - 1) * (D.Ncount : ℝ) -
        unionQ * (D.badMass P : ℝ) := by
  have hR := D.union_rank_trace P hc hPois
  have hpart : (D.Ncount : ℝ) =
      (D.unionMass P : ℝ) + (D.badMass P : ℝ) := by
    exact_mod_cast D.Ncount_eq_unionMass_add_badMass P
  rw [hpart]
  calc
    2 * unionC * rtrace (D.blockP c + D.blockQ c) -
          frobSq (D.blockP c + D.blockQ c)
        ≤ (2 * unionC - 1) * (D.unionMass P : ℝ) +
          unionQ * (D.badMass P : ℝ) := hR
    _ = (2 * unionC - 1) *
          ((D.unionMass P : ℝ) + (D.badMass P : ℝ)) -
          unionQ * (D.badMass P : ℝ) := by
      rw [union_coeff_eq_two_unionQ]
      ring

/-- If the normalized trace dominates total multiplicity, the sharp union lower bound. -/
theorem union_frobSq_ge (P : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (htrace : (D.Ncount : ℝ) ≤ rtrace (D.blockP c + D.blockQ c)) :
    (D.Ncount : ℝ) + unionQ * (D.badMass P : ℝ)
      ≤ frobSq (D.blockP c + D.blockQ c) := by
  have hR := D.union_rank_trace_Ncount P hc hPois
  have htrace' : 2 * unionC * (D.Ncount : ℝ) ≤
      2 * unionC * rtrace (D.blockP c + D.blockQ c) :=
    mul_le_mul_of_nonneg_left htrace
      (mul_nonneg (by norm_num) unionC_pos.le)
  nlinarith

end ZeroBlockData
end Block

section Inst

open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ)

/-- The direct union sum on the enlarged interval agrees with the block species split. -/
theorem NuIprime_eq_mk_unionMass {d : Type*} [Fintype d] [DecidableEq d]
    (v : ZI Z T → d → ℂ) (hv : ∀ z : ZI Z T,
      v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z)) :
    Z.NuIprime T =
      (mkData Z T v hv).unionMass (mkPairReps Z T v hv) := by
  classical
  let D := mkData Z T v hv
  let Pr := mkPairReps Z T v hv
  unfold ZeroConfig.NuIprime ZeroConfig.Nu
  change (∑ᶠ ρ ∈ Z.ZIprime T,
    if ρ.re = (2 : ℝ)⁻¹ ∨ Z.mult ρ = 1 then Z.mult ρ else 0) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprime_finite Z T), ← Finset.sum_coe_sort]
  change (∑ z : ZI Z T,
    if (z : ℂ).re = (2 : ℝ)⁻¹ ∨ D.m z = 1 then D.m z else 0) = D.unionMass Pr
  rw [D.sum_split Pr]
  unfold ZeroBlockData.unionMass ZeroBlockData.Non ZeroBlockData.simplePairs
  congr 1
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hline : (z : ℂ).re = (2 : ℝ)⁻¹ := by
      have hs : D.σ z = z := (D.mem_onLine).mp hz
      simpa only [one_div] using (mkData_σ_eq_iff Z T v hv z).mp hs
    simp [hline]
  · calc
      ∑ z ∈ Pr.R,
          ((if (z : ℂ).re = (2 : ℝ)⁻¹ ∨ D.m z = 1 then D.m z else 0) +
            if ((D.σ z : ZI Z T) : ℂ).re = (2 : ℝ)⁻¹ ∨ D.m (D.σ z) = 1
              then D.m (D.σ z) else 0) =
          ∑ z ∈ Pr.R, 2 * (if D.m z = 1 then 1 else 0) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        have hoff : (z : ℂ).re ≠ (2 : ℝ)⁻¹ := by
          intro hline
          exact Pr.off z hz
            ((mkData_σ_eq_iff Z T v hv z).mpr
              (by simpa only [one_div] using hline))
        have hoffσ : ((D.σ z : ZI Z T) : ℂ).re ≠ (2 : ℝ)⁻¹ := by
          intro hline
          have hfix : D.σ (D.σ z) = D.σ z :=
            (mkData_σ_eq_iff Z T v hv (D.σ z)).mpr
              (by simpa only [one_div] using hline)
          rw [D.σ_invol z] at hfix
          exact Pr.off z hz hfix.symm
        rw [D.m_σ]
        by_cases hm : D.m z = 1
        · simp [hoff, hoffσ, hm]
        · simp [hoff, hoffσ, hm]
      _ = 2 * #({z ∈ Pr.R | D.m z = 1}) := by
        rw [← Finset.mul_sum, Finset.sum_boole]
        norm_num

variable (P : Params)

/-- Concrete finite-compression union inequality for `Â_z`. -/
theorem hatAz_union (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) (hc : 0 < P.a T * P.L T ^ 2) :
    2 * unionC * rtrace (P.hat T (Z.Az P T)) -
        frobSq (P.hat T (Z.Az P T)) - unionQ * (Z.NIprime T : ℝ)
      ≤ unionQ * (Z.NuIprime T : ℝ) := by
  let D := blockData Z T P hconj
  let Pr := mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)
  have hblock := ZeroBlockData.union_rank_trace D Pr hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
  have hpart := D.Ncount_eq_unionMass_add_badMass Pr
  have hpartR : (D.Ncount : ℝ) = (D.unionMass Pr : ℝ) + (D.badMass Pr : ℝ) := by
    exact_mod_cast hpart
  rw [union_coeff_eq_two_unionQ] at hblock
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj,
    NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    NuIprime_eq_mk_unionMass Z T _ (evalVec_reflect hconj)]
  change 2 * unionC * rtrace (D.blockP (P.a T * P.L T ^ 2) +
      D.blockQ (P.a T * P.L T ^ 2)) -
      frobSq (D.blockP (P.a T * P.L T ^ 2) + D.blockQ (P.a T * P.L T ^ 2)) -
      unionQ * (D.Ncount : ℝ) ≤ unionQ * (D.unionMass Pr : ℝ)
  rw [hpartR]
  linarith

end Inst

end Zeta23.ZeroSide
