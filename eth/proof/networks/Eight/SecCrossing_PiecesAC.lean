/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_Blocks
import Mathlib.Tactic

/-! # The pieces A_0, …, A_t: Lemma 2 (a) and (c)

The pieces are the coefficients in ∏_s (R(x_s,y_s,u_s,v_s) + T·C(x_s,y_s,u_s,v_s)) = Σ_i A_i T^i
(`Eight.prodRC`, `Eight.A`; the blocks are numbered s = 0, …, t − 1). This file proves:
* the product has degree at most t (`natDegree_prodRC_le`);
* «A_i is the sum, over the sets Q ⊆ [t] with |Q| = i, of the product that takes C at the blocks s ∈
  Q and R at the others» (`A_eq_sum_subsets`);
* Lemma 2(a): «Set T = 1 and use R + C = 2[x = v][y = u]; the appended zeros agree» (`a_sum`), and
  «|A_i| ≤ C(t,i) ≤ 2^t» (`abs_A_le_choose`, `a_abs`);
* Lemma 2(c): `c_row`, `c_col`, `crow_add_ccol_le` (≤ 11t), `three_mul_tOf_le` (t ≤ (λ+2)/3),
  `c_sum`.
`a_sum`, `a_abs`, `c_row`, `c_col`, `c_sum` have the types of the fields of `Eight.LemPieces`. The
sign rule `Eight.Signs` is a hypothesis of `a_sum` only; it is proved in
`SecCrossing_Identity.lean`. -/

public section

namespace Eight

open Finset Polynomial

/-! ## A product of factors r_s + T·c_s -/

/-- A product of factors r_s + T·c_s over s ∈ S has degree at most |S|. -/
theorem natDegree_prod_linear_le (S : Finset ℕ) (r c : ℕ → ℤ) : (∏ s ∈ S, (C (r s) + X * C (c s))).natDegree ≤ #S := by
  refine (natDegree_prod_le S _).trans ?_
  have h : ∀ s ∈ S, (C (r s) + X * C (c s)).natDegree ≤ 1 := fun s _ => by compute_degree
  simpa using sum_le_card_nsmul S _ 1 h

/-- Multiplying out: ∏_{s ∈ S} (r_s + T·c_s) is the sum, over all Q ⊆ S, of T^|Q| times the product
that takes c_s for s ∈ Q and r_s for the other s. -/
theorem prod_linear_eq_sum (S : Finset ℕ) (r c : ℕ → ℤ) :
    ∏ s ∈ S, (C (r s) + X * C (c s)) = ∑ Q ∈ S.powerset, C (∏ s ∈ S, if s ∈ Q then c s else r s) * X ^ #Q := by
  simp_rw [add_comm (C (r _))]
  rw [Finset.prod_add]
  refine sum_congr rfl fun Q hQ => ?_
  have hQ' := mem_powerset.1 hQ
  rw [prod_ite, filter_mem_eq_inter, filter_notMem_eq_sdiff, inter_eq_right.2 hQ', prod_mul_distrib, prod_const, C_mul, map_prod, map_prod]
  ring

/-- The coefficient of T^i in ∏_{s ∈ S} (r_s + T·c_s): the sum over the Q ⊆ S with |Q| = i. -/
theorem coeff_prod_linear (S : Finset ℕ) (r c : ℕ → ℤ) (i : ℕ) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).coeff i = ∑ Q ∈ S.powersetCard i, ∏ s ∈ S, if s ∈ Q then c s else r s := by
  rw [prod_linear_eq_sum, finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun Q _ => ?_
  rw [coeff_C_mul_X_pow]
  simp only [eq_comm]

/-! ## The definition of the pieces -/

/-- «The t factors are polynomials in T of degree at most 1», so the product has degree at most t. -/
theorem natDegree_prodRC_le {lam : ℕ} (x y u v : Pieces.Bits lam) : (prodRC x y u v).natDegree ≤ tOf lam := by
  simpa [prodRC] using natDegree_prod_linear_le (range (tOf lam)) (fun s => Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s))
    (fun s => Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s))

/-- A sentence of the proof of Lemma 2(b): «A_i is the sum, over the sets Q ⊆ [t] with |Q| = i, of
the product that takes C at the blocks s ∈ Q and R at the others.» The statement is this sentence of
the paper. -/
theorem A_eq_sum_subsets (lam i : ℕ) (x y u v : Pieces.Bits lam) :
    A lam i x y u v = ∑ Q ∈ (Finset.range (tOf lam)).powersetCard i, ∏ s ∈ Finset.range (tOf lam),
      if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) :=
  coeff_prod_linear (range (tOf lam)) (fun s => Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s))
    (fun s => Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) i

/-! ## The appended zeros agree -/

/-- t ≤ (λ+2)/3, written without a division: 3t ≤ λ + 2. -/
theorem three_mul_tOf_le (lam : ℕ) : 3 * tOf lam ≤ lam + 2 := by unfold tOf; omega

/-- A bit of the string itself. -/
theorem bitAt_of_lt {lam : ℕ} (x : Pieces.Bits lam) (j : Fin lam) : bitAt x j = x j := by simp [bitAt]

/-- «The appended zeros agree»: two strings are equal exactly when their t blocks are equal. -/
theorem forall_blockAt_eq_iff {lam : ℕ} (x v : Pieces.Bits lam) : (∀ s ∈ range (tOf lam), blockAt x s = blockAt v s) ↔ x = v := by
  constructor
  · intro h
    funext j
    have hs : j.val / 3 ∈ range (tOf lam) := by
      have := j.isLt
      rw [mem_range]; unfold tOf; omega
    have hb := h _ hs
    simp only [blockAt, Prod.mk.injEq] at hb
    rw [← bitAt_of_lt x j, ← bitAt_of_lt v j]
    have h3 : j.val = 3 * (j.val / 3) ∨ j.val = 3 * (j.val / 3) + 1 ∨ j.val = 3 * (j.val / 3) + 2 := by omega
    rcases h3 with h3 | h3 | h3 <;> rw [h3]
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2
  · rintro rfl s _
    rfl

/-- ∏_s [x_s = v_s][y_s = u_s] = [x = v][y = u]. -/
theorem prod_cross_blocks {lam : ℕ} (x y u v : Pieces.Bits lam) :
    ∏ s ∈ range (tOf lam), (if blockAt x s = blockAt v s ∧ blockAt y s = blockAt u s then (1 : ℤ) else 0) = Pieces.cross x y u v := by
  rw [prod_ite_zero, prod_const_one, Pieces.cross]
  refine if_congr ?_ rfl rfl
  rw [← forall_blockAt_eq_iff x v, ← forall_blockAt_eq_iff y u]
  exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩, fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩

/-! ## Lemma 2 (a) -/

/-- «Set T = 1»: A_0 + … + A_t is the value of the product at T = 1, which is ∏_s (R + C). -/
theorem sum_A_eq_prod {lam : ℕ} (x y u v : Pieces.Bits lam) :
    ∑ i ∈ range (tOf lam + 1), A lam i x y u v =
      ∏ s ∈ range (tOf lam), (Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) + Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) := by
  have h := eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_prodRC_le x y u v)) (1 : ℤ)
  simp only [one_pow, mul_one] at h
  rw [show ∑ i ∈ range (tOf lam + 1), A lam i x y u v = ∑ i ∈ range (tOf lam + 1), (prodRC x y u v).coeff i from rfl, ← h, prodRC, eval_prod]
  simp

/-- **Lemma 2(a), first half**: A_0 + … + A_t = 2^t·[x = v][y = u]. «Set T = 1 and use R + C = 2[x =
v][y = u]; the appended zeros agree.» The proof is that of the paper. The hypothesis λ ≥ 1 is not
used. -/
theorem a_sum (hS : Signs) : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam,
    ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v := by
  intro lam _ x y u v
  rw [sum_A_eq_prod]
  simp_rw [Rb_add_Cb hS]
  rw [prod_mul_distrib, prod_const, card_range, prod_cross_blocks]

/-- «|A_i| ≤ C(t,i)»: each of the C(t,i) products in `A_eq_sum_subsets` is −1, 0 or 1. -/
theorem abs_A_le_choose (lam i : ℕ) (x y u v : Pieces.Bits lam) : |A lam i x y u v| ≤ ((tOf lam).choose i : ℤ) := by
  rw [A_eq_sum_subsets]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ Q ∈ (range (tOf lam)).powersetCard i, |∏ s ∈ range (tOf lam),
      if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)| ≤ 1 := by
    intro Q _
    rw [abs_prod]
    refine prod_le_one (fun _ _ => abs_nonneg _) fun s _ => ?_
    split_ifs
    · exact abs_Cb_le _ _ _ _
    · exact abs_Rb_le _ _ _ _
  simpa using sum_le_card_nsmul _ _ 1 h

/-- **Lemma 2(a), second half**: |A_i| ≤ 2^t, from «|A_i| ≤ C(t,i) ≤ 2^t». The proof is that of the
paper. The hypotheses λ ≥ 1 and i ≤ t are not used. -/
theorem a_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam := by
  intro lam i _ _ x y u v
  refine (abs_A_le_choose lam i x y u v).trans ?_
  exact_mod_cast Nat.choose_le_two_pow (tOf lam) i

/-! ## Lemma 2 (c) -/

/-- **Lemma 2(c)**: c_i^row ≤ 2λ. «The first two bounds hold by definition.» -/
theorem c_row : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → crow lam i ≤ 2 * lam := fun _ _ _ _ => min_le_left _ _

/-- **Lemma 2(c)**: c_i^col ≤ 2λ. «The first two bounds hold by definition.» -/
theorem c_col : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ccol lam i ≤ 2 * lam := fun _ _ _ _ => min_le_left _ _

/-- «c_i^row + c_i^col ≤ (4t + 3i) + (7t − 3i) = 11t», for i ≤ t. -/
theorem crow_add_ccol_le {lam i : ℕ} (hi : i ≤ tOf lam) : crow lam i + ccol lam i ≤ 11 * tOf lam := by
  have h1 : crow lam i ≤ 4 * tOf lam + 3 * i := min_le_right _ _
  have h2 : ccol lam i ≤ 7 * tOf lam - 3 * i := min_le_right _ _
  omega

/-- «t ≤ (λ+2)/3, so 11t ≤ 11λ/3 + 8 = 4ρλ + 8.» -/
theorem eleven_tOf_le (lam : ℕ) : (11 * tOf lam : ℝ) ≤ 11 * lam / 3 + 8 ∧ (11 * lam / 3 + 8 : ℝ) = 4 * rho * lam + 8 := by
  have h : (3 * tOf lam : ℝ) ≤ lam + 2 := by exact_mod_cast three_mul_tOf_le lam
  constructor
  · linarith
  · unfold rho; ring

/-- **Lemma 2(c)**: c_i^row + c_i^col ≤ 4ρλ + 8, where ρ = 11/12. The proof is that of the paper.
The hypothesis λ ≥ 1 is not used. -/
theorem c_sum : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 4 * rho * lam + 8 := by
  intro lam i _ hi
  have h1 : ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 11 * tOf lam := by exact_mod_cast crow_add_ccol_le hi
  have h2 := eleven_tOf_le lam
  linarith [h2.1, h2.2]

end Eight
