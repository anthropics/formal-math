/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide/TightMult.lean — Lemma R (Zeta23/ZeroSide/RankTraceMult.lean) is TIGHT, for every c > 0, on the configurations
"on-line atoms with integer multiplicities m_j ≤ c on orthonormal vectors ⊕ b pair-blocks Q = c·Π_b":
    2c·tr(P+Q) − ‖P+Q‖_F² = Σ_j k_c(m_j) + c²·b      (equality in rank_trace_mult_k / _k_le).
At c = 2 this says: simple zeros (m=1, k₂=3), DOUBLE zeros (m=2, k₂=4) and TIGHT PAIRS (a Q-block of eigenvalue 2, priced c²=4 per
pair) are all extremal simultaneously — the certificate (tr Ĝ, ‖Ĝ‖_F², integer atoms m_j on vectors of norm ≤ 1, n₊(Q) ≤ p) provably
cannot separate an on-line double zero from an off-line pair at depth → 0, and cannot be improved by any further inequality consuming
only these quantities.
-/
import Zeta23.ZeroSide.RankTraceMult
import Mathlib.LinearAlgebra.Matrix.Diagonal

noncomputable section
set_option linter.unusedSectionVars false

open Matrix RHLinalg Finset
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide.TightMult

open RankTraceMult

variable (r b : ℕ) (m : Fin r → ℕ) (c : ℝ)

abbrev idx := Fin r ⊕ Fin b

/-- orthonormal on-line vectors: the standard basis vectors of the first r slots. -/
def v : Fin r → idx r b → ℝ := fun j => Pi.single (Sum.inl j) 1

/-- real multiplicities. -/
def mR : Fin r → ℝ := fun j => (m j : ℝ)

/-- the pair blocks: c × (projection onto the last b slots). -/
def Q : Matrix (idx r b) (idx r b) ℝ := diagonal (Sum.elim (fun _ => 0) (fun _ => c))

lemma xsq_v (j : Fin r) : xsq (v r b) j = 1 := by
  unfold xsq v
  rw [Finset.sum_eq_single (Sum.inl j)]
  · simp
  · intro a _ ha; simp [Pi.single_apply, ha]
  · simp

lemma Pmat_eq_diagonal : Pmat (𝕜 := ℝ) (mR r m) (v r b) = diagonal (Sum.elim (fun j => (m j : ℝ)) (fun _ => 0)) := by
  ext a a'
  rw [Pmat_apply (fun j => by unfold mR; positivity), diagonal_apply]
  simp only [mR, v, RCLike.ofReal_real_eq_id, id_eq, starRingEnd_apply, star_trivial]
  rcases a with j | i
  · by_cases h : (Sum.inl j : idx r b) = a'
    · subst h
      rw [if_pos rfl, Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [Pi.single_apply, Sum.inl_injective.eq_iff, Ne.symm hk]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (Sum.inl k : idx r b) = a'
      · subst hk
        have : k ≠ j := fun e => h (by rw [e])
        simp [Pi.single_apply, Sum.inl_injective.eq_iff, Ne.symm this]
      · simp [Pi.single_apply, hk]
  · have : ∀ k : Fin r, (Pi.single (Sum.inl k) (1:ℝ) : idx r b → ℝ) (Sum.inr i) = 0 := fun k => by
      simp [Pi.single_apply]
    simp only [this, zero_mul, mul_zero, Finset.sum_const_zero, Sum.elim_inr]
    split_ifs <;> simp

lemma Q_posSemidef (hc : 0 ≤ c) : (Q r b c).PosSemidef := by
  rw [Q, posSemidef_diagonal_iff]
  rintro (i | i) <;> simp [hc]

lemma Q_isHermitian (hc : 0 ≤ c) : (Q r b c).IsHermitian := (Q_posSemidef r b c hc).1

lemma posIndex_Q (hc : 0 < c) : posIndex (Q_isHermitian r b c hc.le) = b := by
  rw [posIndex_eq_rank_of_posSemidef (Q_posSemidef r b c hc.le), Q, rank_diagonal, Fintype.card_subtype]
  have : (Finset.univ.filter fun i : idx r b => Sum.elim (fun _ => (0:ℝ)) (fun _ => c) i ≠ 0) = Finset.univ.image Sum.inr := by
    ext i; rcases i with i | i <;> simp [hc.ne']
  rw [this, Finset.card_image_of_injective _ Sum.inr_injective]; simp

lemma rtrace_PQ : rtrace (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b c) = (∑ j, (m j : ℝ)) + c * b := by
  rw [Pmat_eq_diagonal, Q, diagonal_add]
  simp [rtrace, trace_diagonal, Fintype.sum_sum_type]; ring

lemma frobSq_PQ : frobSq (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b c) = (∑ j, (m j : ℝ) ^ 2) + c ^ 2 * b := by
  rw [Pmat_eq_diagonal, Q, diagonal_add]
  simp [frobSq, diagonal_mul_diagonal, trace_diagonal, Fintype.sum_sum_type, sq]; ring

/-- **Lemma R is tight**: for on-line multiplicities 1 ≤ m_j ≤ c on orthonormal vectors and b pair-blocks of eigenvalue c,
   2c·tr(P+Q) − ‖P+Q‖² = Σ_j k_c(m_j) + c²b   — equality in rank_trace_mult_k. -/
theorem lemmaR_tight (hc : 0 < c) (hm : ∀ j, (m j : ℝ) ≤ c) :
    2 * c * rtrace (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b c) - frobSq (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b c)
      = (∑ j, kc c (mR r m j * xsq (v r b) j)) + c ^ 2 * b := by
  rw [rtrace_PQ, frobSq_PQ]
  have : ∀ j, kc c (mR r m j * xsq (v r b) j) = 2 * c * m j - (m j : ℝ) ^ 2 := by
    intro j; rw [xsq_v, mul_one]; unfold mR; rw [kc_of_le (hm j)]
  simp_rw [this]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- … with the hypotheses of Lemma R all met exactly (m_j ≥ 0, ‖v_j‖² = 1 ≤ 1, n₊(Q) = b). -/
theorem lemmaR_tight' (hc : 0 < c) (hm : ∀ j, (m j : ℝ) ≤ c) :
    (∀ j, 0 ≤ mR r m j) ∧ (∀ j, xsq (v r b) j ≤ 1) ∧ posIndex (Q_isHermitian r b c hc.le) = b ∧
    2 * c * rtrace (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b c) - frobSq (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b c)
      = (∑ j, kc c (mR r m j)) + c ^ 2 * b := by
  refine ⟨fun j => by unfold mR; positivity, fun j => by rw [xsq_v], posIndex_Q r b c hc, ?_⟩
  rw [lemmaR_tight r b m c hc hm]
  simp_rw [xsq_v, mul_one]

/-- c = 2: simples (m=1), doubles (m=2) and tight pairs are simultaneously extremal:
   4·tr − ‖·‖² = 3·#{m=1} + 4·#{m=2} + 4·b. -/
theorem lemmaR_tight_two (hm1 : ∀ j, 1 ≤ m j) (hm2 : ∀ j, m j ≤ 2) :
    2 * 2 * rtrace (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b 2) - frobSq (Pmat (𝕜 := ℝ) (mR r m) (v r b) + Q r b 2)
      = 3 * ((Finset.univ.filter (fun j => m j = 1)).card : ℝ) + 4 * ((Finset.univ.filter (fun j => 2 ≤ m j)).card : ℝ)
        + 2 ^ 2 * b := by
  rw [lemmaR_tight r b m 2 (by norm_num) (fun j => by exact_mod_cast hm2 j)]
  simp_rw [xsq_v, mul_one]
  unfold mR
  rw [sum_kc_two_nat m hm1]

end Zeta23.ZeroSide.TightMult
