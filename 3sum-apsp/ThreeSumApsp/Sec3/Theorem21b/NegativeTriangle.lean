/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Theorem 21(b): Negative Triangle reduces to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): one question about a negative triangle
becomes `O(log U)` questions about a zero triangle.  Shifting the weights turns "the triangle is
negative" into `x + y < v` for natural numbers (`S_neg_iff`).  Let the gap at level `ℓ` be
`⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` (`prefixGap`).  If `x + y < v`, the gap at level 0 is
`2(v - x - y) ≥ 2`, which is why the numbers are doubled; from one level to the next a gap of at
least 4 stays at least 2, and the gap is below 2 once `2^ℓ > v`.  So at some level the gap is
exactly 2 or exactly 3, and conversely a gap of at least 2 gives `x + y < v`
(`lt_iff_exists_prefixGap`).  "The gap is `e`" is an exact condition on a triangle (`negToExact`,
`negToExact_isZeroTriangle_iff`).  Together: `hasNegativeTriangle_iff` and
`theorem_21b_negative_to_exact`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem21

/-- The gap at level `ℓ`: the difference `⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` of the prefixes of `2v`,
`2x` and `2y`. -/
private def prefixGap (x y v ℓ : ℕ) : ℤ :=
  ((2 * v / 2 ^ ℓ : ℕ) : ℤ) - ((2 * x / 2 ^ ℓ : ℕ) : ℤ) - ((2 * y / 2 ^ ℓ : ℕ) : ℤ)

/-- A gap of at least 2 gives `x + y < v`: with `X`, `Y`, `V` for the three prefixes,
`2x + 2y < (X + Y + 2) 2^ℓ ≤ V 2^ℓ ≤ 2v`. -/
private theorem add_lt_of_two_le_prefixGap {x y v ℓ : ℕ} (h : 2 ≤ prefixGap x y v ℓ) :
    x + y < v := by
  unfold prefixGap at h
  have hpos : 0 < 2 ^ ℓ := Nat.pow_pos (by norm_num)
  have hV := Nat.mul_div_le (2 * v) (2 ^ ℓ)
  have hX := Nat.div_add_mod (2 * x) (2 ^ ℓ)
  have hXrem := Nat.mod_lt (2 * x) hpos
  have hY := Nat.div_add_mod (2 * y) (2 ^ ℓ)
  have hYrem := Nat.mod_lt (2 * y) hpos
  have hmul : 2 ^ ℓ * (2 * x / 2 ^ ℓ + 2 * y / 2 ^ ℓ + 2) ≤ 2 ^ ℓ * (2 * v / 2 ^ ℓ) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_add] at hmul
  omega

/-- A gap of at least 2 needs `2^ℓ ≤ v`: the prefix `V` of `2v` is at least 2, so
`2 · 2^ℓ ≤ V 2^ℓ ≤ 2v`. -/
private theorem pow_le_of_two_le_prefixGap {x y v ℓ : ℕ} (h : 2 ≤ prefixGap x y v ℓ) :
    2 ^ ℓ ≤ v := by
  unfold prefixGap at h
  have hX := Int.natCast_nonneg (2 * x / 2 ^ ℓ)
  have hY := Int.natCast_nonneg (2 * y / 2 ^ ℓ)
  have hV := Nat.mul_div_le (2 * v) (2 ^ ℓ)
  have hmul : 2 ^ ℓ * 2 ≤ 2 ^ ℓ * (2 * v / 2 ^ ℓ) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- A gap of at least 4 leaves a gap of at least 2 at the next level: a prefix at level `ℓ + 1` is
half the prefix at level `ℓ`, rounded down, so the new gap is at least `(4 - 1)/2`. -/
private theorem two_le_prefixGap_succ {x y v ℓ : ℕ} (h : 4 ≤ prefixGap x y v ℓ) :
    2 ≤ prefixGap x y v (ℓ + 1) := by
  unfold prefixGap at h ⊢
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  omega

/-- Climbing from a level at which the gap is at least 2, the first level at which the gap is below
4 has gap 2 or 3.  There is such a level, because a gap of at least 2 needs `2^ℓ ≤ v`. -/
private theorem exists_prefixGap_eq {x y v ℓ : ℕ} (h : 2 ≤ prefixGap x y v ℓ) :
    ∃ ℓ' : ℕ, prefixGap x y v ℓ' = 2 ∨ prefixGap x y v ℓ' = 3 := by
  induction hk : v + 1 - ℓ generalizing ℓ with
  | zero =>
    -- The level cannot be above `v`, since `ℓ < 2^ℓ ≤ v`.
    have hle := pow_le_of_two_le_prefixGap h
    have hlt : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    omega
  | succ k ih =>
    by_cases h4 : 4 ≤ prefixGap x y v ℓ
    · exact ih (two_le_prefixGap_succ h4) (by omega)
    · exact ⟨ℓ, by omega⟩

/-- For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.
One way to write this: for natural numbers with `v < 2^L`, `x + y < v` if and only if
at one of the levels `ℓ < L` the gap `⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` is exactly 2 or exactly 3.
(This form need not be literally the one of [VW13].) -/
private theorem lt_iff_exists_prefixGap {x y v L : ℕ} (hL : v < 2 ^ L) :
    x + y < v ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ prefixGap x y v ℓ = e := by
  constructor
  · intro h
    -- At level 0 the gap is `2(v - x - y) ≥ 2`.
    have hzero : 2 ≤ prefixGap x y v 0 := by
      simp only [prefixGap, pow_zero, Nat.div_one]
      omega
    obtain ⟨ℓ, hℓ⟩ := exists_prefixGap_eq hzero
    have hle : 2 ^ ℓ ≤ v := pow_le_of_two_le_prefixGap (x := x) (y := y) (by omega)
    exact ⟨ℓ, (Nat.pow_lt_pow_iff_right (by norm_num)).mp (hle.trans_lt hL), _, hℓ, rfl⟩
  · rintro ⟨ℓ, -, e, he, h⟩
    exact add_lt_of_two_le_prefixGap (ℓ := ℓ) (by omega)

/-- The Exact Triangle instance for the level `ℓ` and the exact value `e`.  The weights `w(a,b)`,
`w(b,c)` and `w(a,c)` in `[-U, U]` are first shifted to the natural numbers `x = w(a,b) + U`,
`y = w(b,c) + U` and `v = 2U - w(a,c)`, so that the triangle is negative exactly if `x + y < v`;
then `x` and `y` are replaced by the prefixes `⌊2x/2^ℓ⌋` and `⌊2y/2^ℓ⌋`, and `v` by `e - ⌊2v/2^ℓ⌋`.
-/
def negToExact (U ℓ : ℕ) (e : ℤ) : (ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ) :=
  (fun wAB => ((2 * (wAB + U).toNat / 2 ^ ℓ : ℕ) : ℤ),
    fun wBC => ((2 * (wBC + U).toNat / 2 ^ ℓ : ℕ) : ℤ),
    fun wAC => e - ((2 * (2 * U - wAC).toNat / 2 ^ ℓ : ℕ) : ℤ))

/-- The weights of these instances are at most `6U` in absolute value. -/
private theorem negToExact_bound (U ℓ : ℕ) (hU : 1 ≤ U) (e : ℤ) (he : e = 2 ∨ e = 3) (x : ℤ)
    (hx : |x| ≤ (U : ℤ)) :
    |(negToExact U ℓ e).1 x| ≤ 6 * (U : ℤ) ∧ |(negToExact U ℓ e).2.1 x| ≤ 6 * (U : ℤ) ∧
      |(negToExact U ℓ e).2.2 x| ≤ 6 * (U : ℤ) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  have hxy := Nat.div_le_self (2 * (x + U).toNat) (2 ^ ℓ)
  have hv := Nat.div_le_self (2 * (2 * U - x).toNat) (2 ^ ℓ)
  simp only [negToExact, abs_le]
  generalize 2 * (x + U).toNat / 2 ^ ℓ = q at hxy ⊢
  generalize 2 * (2 * U - x).toNat / 2 ^ ℓ = r at hv ⊢
  omega

/-- A triangle has weight zero in the instance for `ℓ` and `e` exactly if the gap at level `ℓ` is
`e`. -/
private theorem negToExact_isZeroTriangle_iff {n : ℕ} (T : TriangleInstance ℤ n) (U ℓ : ℕ) (e : ℤ)
    (a b c : Fin n) :
    (T.mapWeights (negToExact U ℓ e)).IsZeroTriangle a b c ↔
      prefixGap (T.wAB a b + U).toNat (T.wBC b c + U).toNat (2 * U - T.wAC a c).toNat ℓ = e := by
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleInstance.mapWeights,
    negToExact, prefixGap]
  constructor <;> intro h <;> linarith [h]

/-- A triangle is negative exactly if the shifted weights satisfy `x + y < v`. -/
private theorem S_neg_iff {n : ℕ} (T : TriangleInstance ℤ n) (U : ℕ)
    (hT : T.WeightsBoundedBy (U : ℤ)) (a b c : Fin n) :
    T.S a b c < 0 ↔
      (T.wAB a b + U).toNat + (T.wBC b c + U).toNat < (2 * U - T.wAC a c).toNat := by
  obtain ⟨hTAB, hTBC, hTAC⟩ := hT
  have hAB := abs_le.mp (hTAB a b)
  have hBC := abs_le.mp (hTBC b c)
  have hAC := abs_le.mp (hTAC a c)
  simp only [TriangleInstance.S]
  omega

/-- The reduction of [VW13, Theorem 3.3], for weights in `[-U, U]` with `3U < 2^L`: there is a
negative triangle if and only if, at one of the levels `ℓ < L` and for `e = 2` or `e = 3`, the
instance made of the prefixes has a zero triangle. -/
theorem hasNegativeTriangle_iff {n U L : ℕ} (T : TriangleInstance ℤ n)
    (hT : T.WeightsBoundedBy (U : ℤ)) (hL : 3 * U < 2 ^ L) :
    T.HasNegativeTriangle ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧
      (T.mapWeights (negToExact U ℓ e)).HasZeroTriangle := by
  have hv (a c : Fin n) : (2 * U - T.wAC a c).toNat < 2 ^ L := by
    obtain ⟨-, -, hTAC⟩ := hT
    have := abs_le.mp (hTAC a c)
    omega
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨ℓ, hℓ, e, he, hgap⟩ :=
      (lt_iff_exists_prefixGap (hv a c)).1 ((S_neg_iff T U hT a b c).1 h)
    exact ⟨ℓ, hℓ, e, he, a, b, c, (negToExact_isZeroTriangle_iff T U ℓ e a b c).2 hgap⟩
  · rintro ⟨ℓ, hℓ, e, he, a, b, c, h⟩
    exact ⟨a, b, c, (S_neg_iff T U hT a b c).2 ((lt_iff_exists_prefixGap (hv a c)).2
      ⟨ℓ, hℓ, e, he, (negToExact_isZeroTriangle_iff T U ℓ e a b c).1 h⟩)⟩

/-- The list of the instances for all levels `ℓ < L` and `e = 2` or `e = 3`. -/
private def negToExactList (U L : ℕ) : List ((ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ)) :=
  (List.range L).map (negToExact U · 2) ++ (List.range L).map (negToExact U · 3)

private theorem mem_negToExactList {U L : ℕ} {f : (ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ)} :
    f ∈ negToExactList U L ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ negToExact U ℓ e = f := by
  simp only [negToExactList, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩)
    exacts [⟨ℓ, hℓ, 2, .inl rfl, rfl⟩, ⟨ℓ, hℓ, 3, .inr rfl, rfl⟩]
  · rintro ⟨ℓ, hℓ, e, rfl | rfl, rfl⟩
    exacts [.inl ⟨ℓ, hℓ, rfl⟩, .inr ⟨ℓ, hℓ, rfl⟩]

end Theorem21

/-- The combinatorial content of [VW13, Theorem 3.3] in the form needed for **Theorem 21(b)**:
whether an instance with weights in `[−U, U]` has a negative triangle is decided by asking
`O(log U)` times whether there is a zero triangle, each time after changing the weights, edge by
edge, to numbers of absolute value `O(U)`.  The instances are obtained from the given one by
applying to each weight a function that depends only on `U`, on the number of the instance and on
which of the three parts' pairs the edge joins.  There are at most `2⌊log₂ U⌋ + 6` of them, and
their weights are at most `6U` in absolute value. -/
theorem theorem_21b_negative_to_exact (U : ℕ) (hU : 1 ≤ U) :
    ∃ L : List ((ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ)),
      L.length ≤ 2 * Nat.log 2 U + 6 ∧
      (∀ fAB fBC fAC, (fAB, fBC, fAC) ∈ L → ∀ x : ℤ, |x| ≤ (U : ℤ) →
        |fAB x| ≤ 6 * (U : ℤ) ∧ |fBC x| ≤ 6 * (U : ℤ) ∧ |fAC x| ≤ 6 * (U : ℤ)) ∧
      ∀ (n : ℕ) (T : TriangleInstance ℤ n), T.WeightsBoundedBy (U : ℤ) →
        (T.HasNegativeTriangle ↔ ∃ f ∈ L, (T.mapWeights f).HasZeroTriangle) := by
  -- The levels `ℓ < ⌊log₂ U⌋ + 3` are enough, because `3U < 4 · 2^{⌊log₂ U⌋ + 1}`.
  have hlevels : 3 * U < 2 ^ (Nat.log 2 U + 3) := by
    have hlog : U < 2 ^ (Nat.log 2 U + 1) := Nat.lt_pow_succ_log_self (by norm_num) U
    rw [pow_add] at hlog ⊢
    omega
  refine ⟨Theorem21.negToExactList U (Nat.log 2 U + 3), ?_, ?_, ?_⟩
  · simp only [Theorem21.negToExactList, List.length_append, List.length_map, List.length_range]
    omega
  · intro fAB fBC fAC hf x hx
    obtain ⟨ℓ, -, e, he, hfe⟩ := Theorem21.mem_negToExactList.1 hf
    have hbound := Theorem21.negToExact_bound U ℓ hU e he x hx
    rwa [hfe] at hbound
  · intro n T hT
    rw [Theorem21.hasNegativeTriangle_iff T hT hlevels]
    constructor
    · rintro ⟨ℓ, hℓ, e, he, h⟩
      exact ⟨_, Theorem21.mem_negToExactList.2 ⟨ℓ, hℓ, e, he, rfl⟩, h⟩
    · rintro ⟨f, hf, h⟩
      obtain ⟨ℓ, hℓ, e, he, rfl⟩ := Theorem21.mem_negToExactList.1 hf
      exact ⟨ℓ, hℓ, e, he, h⟩

end ThreeSumApsp
