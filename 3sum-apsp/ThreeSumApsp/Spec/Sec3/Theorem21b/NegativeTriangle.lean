/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21
public import ThreeSumApsp.Sec3.Theorem21b.NegativeTriangle
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.BinaryPrefixes

/-!
# Negative Triangle from Exact Triangle, on lists of integers

For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.

* The weights in `[-U, U]` are shifted to the natural numbers `x = w(a,b) + U`, `y = w(b,c) + U`,
  `v = 2U - w(a,c)`, so that a triangle is negative exactly if `x + y < v`.  The routine computes
  the prefixes `⌊z/2^ℓ⌋` (`prefQ`) of all the numbers `2x`, `2y`, `2v`, which are at most `6U`, at
  once (`negStart`, `bounds_of_mem_negStart`, `zipWith_shiftQ`, `map_shiftR`).
* For each level `ℓ` and for `e = 2` and `e = 3` the reduction makes the instance of Exact Triangle
  with the weights `⌊2x/2^ℓ⌋`, `⌊2y/2^ℓ⌋` and `e - ⌊2v/2^ℓ⌋` (`negThird`, `triOf_level`).  There is
  a negative triangle if and only if one of these instances, at a level `ℓ < L` where `3U < 2^L`,
  has a zero triangle (`hasNegativeTriangle_iff_exists_level`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The instances of the levels -/

/-- At the top level the prefixes are zero. -/
theorem map_prefQ_start {L : ℕ} {Z : List ℤ} (h : ∀ z ∈ Z, 0 ≤ z ∧ z < 2 ^ L) :
    Z.map (prefQ L) = affL 0 0 Z :=
  List.map_congr_left fun z hz => by simp [prefQ_start (h z hz).1 (h z hz).2]

/-- The shifted and doubled weights: `2x = 2 (w(a,b) + U)`, `2y = 2 (w(b,c) + U)`,
`2v = 2 (2U - w(a,c))`, one list after the other. -/
def negStart (U : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  affL 2 (2 * U) AB ++ (affL 2 (2 * U) BC ++ affL (-2) (4 * U) AC)

/-- The third list of the instance for the level `ℓ` and the number `e`: the weights
`e - ⌊2v/2^ℓ⌋`.  A zero triangle is a triple with `⌊2v/2^ℓ⌋ = ⌊2x/2^ℓ⌋ + ⌊2y/2^ℓ⌋ + e`. -/
def negThird (U ℓ : ℕ) (e : ℤ) (AC : List ℤ) : List ℤ :=
  affL (-1) e ((affL (-2) (4 * U) AC).map (prefQ ℓ))

section Bounded

variable {n U : ℕ} {AB BC AC : List ℤ}

/-- The numbers of the start are between 0 and `6U`. -/
theorem bounds_of_mem_negStart (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    ∀ z ∈ negStart U AB BC AC, 0 ≤ z ∧ z ≤ 6 * (U : ℤ) := by
  intro z hz
  simp only [negStart, affL, List.mem_append, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · have := abs_le.1 (hAB x hx); omega
  · have := abs_le.1 (hBC x hx); omega
  · have := abs_le.1 (hAC x hx); omega

/-- The numbers of the third list are at most `6U` in absolute value. -/
theorem abs_le_of_mem_negThird (hU : 1 ≤ U) (hAC : AbsLe AC U) (ℓ : ℕ) {e : ℤ}
    (he : e = 2 ∨ e = 3) : AbsLe (negThird U ℓ e AC) (6 * U) := by
  intro x hx
  simp only [negThird, affL, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hwU := abs_le.1 (hAC w hw)
  have hv : 0 ≤ -2 * w + 4 * (U : ℤ) := by omega
  have hlow := prefQ_nonneg hv ℓ
  have hhigh := prefQ_le hv ℓ
  rcases he with rfl | rfl <;> exact abs_le.2 ⟨by omega, by omega⟩

/-- The prefix of twice a natural number that is written as an integer. -/
private theorem prefQ_two_mul {x : ℤ} (hx : 0 ≤ x) (ℓ : ℕ) :
    prefQ ℓ (2 * x) = ((2 * x.toNat / 2 ^ ℓ : ℕ) : ℤ) := by
  rw [← prefQ_natCast, Nat.cast_mul, Int.toNat_of_nonneg hx, Nat.cast_ofNat]

/-- An entry of a matrix to whose entries a function has been applied. -/
private theorem getD_map_entry {l : List ℤ} (hl : l.length = n * n) (f : ℤ → ℤ) (a b : Fin n) :
    (l.map f).getD (a * n + b) 0 = f (l.getD (a * n + b) 0) :=
  List.getD_map_of_lt f (hl ▸ Nat.mul_add_lt_mul a.isLt b.isLt) 0 0

/-- The instance made of the lists of the level `ℓ` is the instance of the reduction. -/
theorem triOf_level (lAB : AB.length = n * n) (lBC : BC.length = n * n) (lAC : AC.length = n * n)
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) (ℓ : ℕ) (e : ℤ) :
    triOf n ((affL 2 (2 * U) AB).map (prefQ ℓ)) ((affL 2 (2 * U) BC).map (prefQ ℓ))
        (negThird U ℓ e AC) =
      (triOf n AB BC AC).mapWeights (Theorem21.negToExact U ℓ e) := by
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  simp only [triOf, TriangleInstance.mapWeights, Theorem21.negToExact, negThird, affL, List.map_map]
  congr 1 <;> funext a b
  · have hw := abs_le.1 (AbsLe.abs_getD_le hU hAB (a * n + b))
    rw [getD_map_entry lAB, Function.comp_apply, ← prefQ_two_mul (by omega)]
    exact congrArg _ (by ring)
  · have hw := abs_le.1 (AbsLe.abs_getD_le hU hBC (a * n + b))
    rw [getD_map_entry lBC, Function.comp_apply, ← prefQ_two_mul (by omega)]
    exact congrArg _ (by ring)
  · have hw := abs_le.1 (AbsLe.abs_getD_le hU hAC (a * n + b))
    rw [getD_map_entry lAC, ← prefQ_two_mul (by omega)]
    simp only [Function.comp_apply]
    rw [show -2 * AC.getD (a * n + b) 0 + 4 * (U : ℤ) = 2 * (2 * U - AC.getD (a * n + b) 0) by ring]
    ring

/-- **Negative Triangle by prefixes.**  If `3U < 2^L`, then there is a negative triangle if and only
if, at one of the levels `ℓ < L` and for `e = 2` or `e = 3`, the instance made of the prefixes has a
zero triangle. -/
theorem hasNegativeTriangle_iff_exists_level {L : ℕ} (lAB : AB.length = n * n)
    (lBC : BC.length = n * n) (lAC : AC.length = n * n) (hAB : AbsLe AB U) (hBC : AbsLe BC U)
    (hAC : AbsLe AC U) (hL : 3 * U < 2 ^ L) :
    (triOf n AB BC AC).HasNegativeTriangle ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧
      (triOf n ((affL 2 (2 * U) AB).map (prefQ ℓ)) ((affL 2 (2 * U) BC).map (prefQ ℓ))
        (negThird U ℓ e AC)).HasZeroTriangle := by
  simp only [triOf_level lAB lBC lAC hAB hBC hAC]
  exact Theorem21.hasNegativeTriangle_iff _ (triOf_bounded hAB hBC hAC) hL

end Bounded

end ThreeSumApsp.Spec
