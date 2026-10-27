/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Bridge
public import ClauseBound.Part.Rec
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The ring of Appendix B: binomial coefficients, partitions, the spaces V_E and the operators ∇_k

Statements of the paragraph "The ring and its operators" before display (47): Pascal's rule and
Vandermonde's identity for all integers (`GeneralPieces.binomRules`); the partitions of E and
p(E) ≤ p(E+1) (`GeneralPieces.ptnFacts`); V_E consists of the polynomials all of whose monomials t^μ
have |μ| = E (`GeneralPieces.Ring.mem_VE_iff`), V₀ = ℚ (`GeneralPieces.Ring.mem_VE_zero`) and V_E =
0 for E < 0 (`GeneralPieces.Ring.VE_neg`); ∇_k maps V_E to V_{E−k} (`GeneralPieces.Ring.nabla_mem`). -/

public section

namespace GeneralPieces.Ring

open AppHalfPieces MvPolynomial Finset

/-! ### Binomial coefficients -/

theorem binom_natCast (k : ℤ) (j : ℕ) : binom k (j : ℤ) = _root_.Ring.choose k j := by
  rw [binom, if_pos (by omega), Int.toNat_natCast]

theorem binom_neg (k : ℤ) {j : ℤ} (hj : j < 0) : binom k j = 0 := by rw [binom, if_neg (by omega)]

/-! ### Partitions -/

/-- Back from natural numbers to positive integers. -/
theorem map_toPNat'_toN (μ : Ptn) : (toN μ).map Nat.toPNat' = μ := by
  unfold toN
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id μ]
  exact Multiset.map_congr rfl fun k _ => PNat.coe_toPNat' k

/-- The parts of a partition, made positive integers and natural numbers again. -/
theorem toN_map_toPNat' {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) : toN (s.map Nat.toPNat') = s := by
  unfold toN
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl fun k hk => PNat.toPNat'_coe (hs k hk)

theorem mem_ptns (E : ℕ) (μ : Ptn) : μ ∈ ptns E ↔ wt μ = E := by
  unfold ptns
  rw [mem_image]
  constructor
  · rintro ⟨q, -, rfl⟩
    rw [← sum_toN, toN_map_toPNat' fun i hi => q.parts_pos hi, q.parts_sum]
  · intro h
    refine ⟨⟨toN μ, fun {i} hi => Nat.pos_of_ne_zero fun h0 => zero_notMem_toN μ (h0 ▸ hi), h⟩, mem_univ _, map_toPNat'_toN μ⟩

theorem card_ptns (E : ℕ) : #(ptns E) = Partitions.p E := by
  unfold ptns Partitions.p
  rw [card_image_of_injective _ fun q q' h => ?_, card_univ]
  have h' := congrArg toN h
  rw [toN_map_toPNat' fun i hi => q.parts_pos hi, toN_map_toPNat' fun i hi => q'.parts_pos hi] at h'
  exact Nat.Partition.ext h'

theorem mem_ptnsZ (E : ℤ) (μ : Ptn) : μ ∈ ptnsZ E ↔ (wt μ : ℤ) = E := by
  unfold ptnsZ
  split_ifs with h
  · rw [mem_ptns]; omega
  · simp only [notMem_empty, false_iff]; omega

/-! ### Weights -/

/-- The weight of the variables: t_k has weight k. -/
@[expose] def wgt : ℕ+ → ℕ := fun k => (k : ℕ)

/-- The weight of the monomial t^μ is |μ|. -/
theorem weight_toFinsupp (μ : Ptn) : Finsupp.weight wgt (Multiset.toFinsupp μ) = wt μ := by
  induction μ using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add, map_add, ih, Multiset.toFinsupp_singleton, Finsupp.weight_single]
    simp [wt, wgt]

theorem VE_natCast (E : ℕ) : VE (E : ℤ) = weightedHomogeneousSubmodule ℚ wgt E := by
  rw [VE, if_pos (by omega), Int.toNat_natCast]
  rfl

theorem VE_neg {E : ℤ} (hE : E < 0) : VE E = ⊥ := by rw [VE, if_neg (by omega)]

theorem mem_VE_natCast (E : ℕ) (f : V) : f ∈ VE (E : ℤ) ↔ IsWeightedHomogeneous wgt f E := by
  rw [VE_natCast, mem_weightedHomogeneousSubmodule]

/-- Two polynomials with the same coefficients are equal. -/
theorem ext_coef {f g : V} (h : ∀ π, coef π f = coef π g) : f = g := by
  ext d
  have := h (Finsupp.toMultiset d)
  unfold coef at this
  rwa [Finsupp.toMultiset_toFinsupp] at this

/-- f has weight E if and only if every monomial of f has weight E. -/
theorem mem_VE_iff (E : ℤ) (f : V) : f ∈ VE E ↔ ∀ μ, coef μ f ≠ 0 → (wt μ : ℤ) = E := by
  by_cases hE : 0 ≤ E
  · obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hE
    rw [mem_VE_natCast]
    constructor
    · intro h μ hμ
      have := h hμ
      rw [weight_toFinsupp] at this
      exact_mod_cast this
    · intro h d hd
      have := h (Finsupp.toMultiset d) (by unfold coef; rwa [Finsupp.toMultiset_toFinsupp])
      rw [← weight_toFinsupp, Finsupp.toMultiset_toFinsupp] at this
      exact_mod_cast this
  · rw [VE_neg (by omega), Submodule.mem_bot]
    constructor
    · rintro rfl μ hμ
      exact absurd (coeff_zero _) hμ
    · intro h
      refine ext_coef fun π => ?_
      by_contra hπ
      have h0 : coef π (0 : V) = 0 := coeff_zero _
      have := h π (by rwa [h0] at hπ)
      omega

theorem tpow_mem_VE (μ : Ptn) : tpow μ ∈ VE (wt μ : ℤ) := by
  rw [mem_VE_natCast]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_toFinsupp μ)

/-- A polynomial is the sum of its monomials. -/
theorem eq_sum_tpow (f : V) : f = ∑ d ∈ f.support, coeff d f • tpow (Finsupp.toMultiset d) := by
  conv_lhs => rw [f.as_sum]
  refine sum_congr rfl fun d _ => ?_
  unfold tpow
  rw [Finsupp.toMultiset_toFinsupp, smul_monomial, smul_eq_mul, mul_one]

theorem wt_eq_zero {μ : Ptn} (h : wt μ = 0) : μ = 0 := by
  rw [← sum_toN, Multiset.sum_eq_zero_iff] at h
  refine Multiset.eq_zero_of_forall_notMem fun k hk => ?_
  exact k.pos.ne' (h _ ((mem_toN μ k).2 hk))

theorem mem_VE_zero (f : V) : f ∈ VE 0 ↔ ∃ q : ℚ, f = C q := by
  constructor
  · intro hf
    refine ⟨coeff 0 f, ext_coef fun π => ?_⟩
    unfold coef
    rw [coeff_C]
    by_cases hπ : π = 0
    · subst hπ; simp
    · have h1 : (0 : ℕ+ →₀ ℕ) ≠ Multiset.toFinsupp π := fun h => hπ (Multiset.toFinsupp.injective (by rw [← h, map_zero]))
      rw [if_neg h1]
      by_contra h2
      have := (mem_VE_iff 0 f).1 hf π h2
      exact hπ (wt_eq_zero (by exact_mod_cast this))
  · rintro ⟨q, rfl⟩
    have : C q ∈ VE ((0 : ℕ) : ℤ) := (mem_VE_natCast 0 _).2 (isWeightedHomogeneous_C _ _)
    simpa using this

/-! ### The operators ∇_k -/

theorem nabla_add (k : ℤ) (f g : V) : nabla k (f + g) = nabla k f + nabla k g := by
  unfold nabla
  split_ifs
  · rw [mul_add]
  · rw [map_add, smul_add]
  · rw [add_zero]

theorem nabla_mem {k E : ℤ} {f : V} (hk : k ≠ 0) (hf : f ∈ VE E) : nabla k f ∈ VE (E - k) := by
  by_cases hE : 0 ≤ E
  · obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hE
    have hf' := (mem_VE_natCast e f).1 hf
    have hp := pn_coe hk
    rcases lt_or_gt_of_ne hk with hk' | hk'
    · have e1 : (e : ℤ) - k = ((wgt (pn k) + e : ℕ) : ℤ) := by unfold wgt; push_cast; omega
      rw [nabla_neg hk', e1, mem_VE_natCast]
      exact (isWeightedHomogeneous_X ℚ wgt (pn k)).mul hf'
    · rw [nabla_pos hk']
      refine Submodule.smul_mem _ _ ((mem_VE_iff _ _).2 fun μ hμ => ?_)
      unfold coef at hμ
      rw [coeff_pderiv] at hμ
      have h1 := hf' (left_ne_zero_of_mul hμ)
      rw [map_add, weight_toFinsupp, Finsupp.weight_single] at h1
      simp only [wgt, smul_eq_mul, one_mul] at h1
      omega
  · rw [VE_neg (by omega), Submodule.mem_bot] at hf
    rw [hf, nabla_zero_right]
    exact Submodule.zero_mem _

end GeneralPieces.Ring

namespace GeneralPieces

open AppHalfPieces Finset GeneralPieces.Ring

/-- "Pascal's rule and Vandermonde's identity hold for all integers k, k'." -/
theorem binomRules : BinomRules where
  pascal := fun k j => by
    rcases lt_trichotomy j (-1) with hj | rfl | hj
    · rw [binom_neg (k + 1) (by omega : j + 1 < 0), binom_neg k (by omega : j < 0), binom_neg k (by omega : j + 1 < 0), add_zero]
    · rw [binom_neg k (by omega : (-1 : ℤ) < 0)]
      have : (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) := by norm_num
      rw [this, binom_natCast, binom_natCast, Ring.choose_zero_right, Ring.choose_zero_right, zero_add]
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
      have : ((i : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [this, binom_natCast, binom_natCast, binom_natCast, Ring.choose_succ_succ]
  vandermonde := fun k k' i => by
    rw [binom_natCast, add_comm k k', Ring.add_choose_eq i (Commute.all k' k), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun j hj => ?_
    have hj' := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have : (i : ℤ) - j = ((i - j : ℕ) : ℤ) := by omega
    rw [this, binom_natCast, binom_natCast, mul_comm]

/-- The partitions of E are the multisets of positive integers with sum E, there are p(E) of them,
and "adding a part 1 shows p(E) ≤ p(E+1)" (`ClauseBound.Part.p_mono`). -/
theorem ptnFacts : PtnFacts where
  mem := mem_ptns
  card := card_ptns
  mono := fun E => ClauseBound.Part.p_mono (Nat.le_succ E)

end GeneralPieces
