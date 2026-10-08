/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Corollary39.Definitions
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle

/-!
# Max-Weight Triangle from Exact Triangle (proof of Corollary 39)

Proof of Corollary 39: "By [VW13, Theorem 3.3], finding a maximum weight triangle costs O(log² n)
times as much" as deciding whether there is a triangle of weight zero.  The weight W of a maximum
weight triangle is found by a search with decisions of the form: is there a triangle of weight at
least w?  These are instances of Negative Triangle (`neg_iff_atLeast`).  A triangle of weight
exactly W is then found by three searches with decisions of the form: is there a triangle of weight
W with a ≥ a₀, b ≥ b₀, c ≥ c₀?  These are instances of Exact Triangle with the same vertex sets, in
which the other vertices are switched off by a large weight (`zero_iff_exactFrom`).  What the four
searches find is a triangle of maximum weight (`isMax_of_searches`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open ThreeSumApsp.KClique

/-! ## Switching off rows and columns -/

/-- The matrix in the list l, with Big added to the entries in the rows below r₀ and in the columns
below c₀. -/
def maskL (n : ℕ) (r₀ c₀ Big : ℤ) (l : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    l.getD q 0 + if ((q / n : ℕ) : ℤ) < r₀ ∨ ((q % n : ℕ) : ℤ) < c₀ then Big else 0

/-- It has n² entries. -/
@[simp] theorem length_maskL (n : ℕ) (r₀ c₀ Big : ℤ) (l : List ℤ) :
    (maskL n r₀ c₀ Big l).length = n * n := by
  simp [maskL]

/-- The entry (i, j) of the matrix with rows and columns switched off. -/
theorem getD_maskL {n : ℕ} (r₀ c₀ Big : ℤ) (l : List ℤ) (i j : Fin n) :
    (maskL n r₀ c₀ Big l).getD (i.val * n + j.val) 0 =
      l.getD (i.val * n + j.val) 0 + if (i.val : ℤ) < r₀ ∨ (j.val : ℤ) < c₀ then Big else 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using Nat.mul_add_lt_mul i.isLt j.isLt)]
  simp only [maskL, List.getElem_map, List.getElem_range, Nat.mul_add_div_of_lt j.isLt,
    Nat.mul_add_mod_of_lt j.isLt]

/-- The entry (i, j) of the matrix of the numbers m y + c. -/
theorem getD_affL {n : ℕ} (m c : ℤ) {l : List ℤ} (hl : l.length = n * n) (i j : Fin n) :
    (affL m c l).getD (i.val * n + j.val) 0 = m * l.getD (i.val * n + j.val) 0 + c := by
  have h := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using h), List.getD_eq_getElem _ _ (hl ▸ h)]
  simp [affL]

/-! ## The two kinds of decisions -/

/-- Some triangle has weight at least W. -/
def AtLeast (n : ℕ) (AB BC AC : List ℤ) (W : ℤ) : Prop :=
  ∃ a b c : Fin n, W ≤ (triOf n AB BC AC).S a b c

/-- Some triangle with a ≥ a₀, b ≥ b₀, c ≥ c₀ has weight exactly W. -/
def ExactFrom (n : ℕ) (AB BC AC : List ℤ) (W a₀ b₀ c₀ : ℤ) : Prop :=
  ∃ a b c : Fin n, a₀ ≤ (a.val : ℤ) ∧ b₀ ≤ (b.val : ℤ) ∧ c₀ ≤ (c.val : ℤ) ∧
    (triOf n AB BC AC).S a b c = W

variable {n U : ℕ} {AB BC AC : List ℤ}

/-- The weight of a triangle, in terms of the three lists. -/
theorem S_triOf (a b c : Fin n) (AB BC AC : List ℤ) :
    (triOf n AB BC AC).S a b c = AB.getD (a.val * n + b.val) 0 + BC.getD (b.val * n + c.val) 0 +
      AC.getD (a.val * n + c.val) 0 :=
  rfl

/-- The weight of a triangle is between -3U and 3U. -/
theorem abs_S_le (hAB : ∀ x ∈ AB, |x| ≤ (U : ℤ)) (hBC : ∀ x ∈ BC, |x| ≤ (U : ℤ))
    (hAC : ∀ x ∈ AC, |x| ≤ (U : ℤ)) (a b c : Fin n) :
    -(3 * (U : ℤ)) ≤ (triOf n AB BC AC).S a b c ∧ (triOf n AB BC AC).S a b c ≤ 3 * (U : ℤ) := by
  have h1 := abs_le.1 (AbsLe.abs_getD_le (Int.natCast_nonneg U) hAB (a.val * n + b.val))
  have h2 := abs_le.1 (AbsLe.abs_getD_le (Int.natCast_nonneg U) hBC (b.val * n + c.val))
  have h3 := abs_le.1 (AbsLe.abs_getD_le (Int.natCast_nonneg U) hAC (a.val * n + c.val))
  rw [S_triOf]
  constructor <;> omega

/-- That some triangle has weight at least W, as an instance of Negative Triangle: the negated
weights, with W - 1 added to the third matrix. -/
theorem neg_iff_atLeast (lAB : AB.length = n * n) (lBC : BC.length = n * n)
    (lAC : AC.length = n * n) (W : ℤ) :
    (triOf n (affL (-1) 0 AB) (affL (-1) 0 BC) (affL (-1) (W - 1) AC)).HasNegativeTriangle ↔
      AtLeast n AB BC AC W := by
  unfold TriangleInstance.HasNegativeTriangle AtLeast
  refine exists_congr fun a => exists_congr fun b => exists_congr fun c => ?_
  rw [S_triOf, S_triOf, getD_affL _ _ lAB, getD_affL _ _ lBC, getD_affL _ _ lAC]
  constructor <;> intro h <;> omega

/-- That some triangle with a ≥ a₀, b ≥ b₀, c ≥ c₀ has weight W, as an instance of Exact Triangle:
a triangle with a vertex that is switched off has a weight above 0. -/
theorem zero_iff_exactFrom (lAC : AC.length = n * n) (hAB : ∀ x ∈ AB, |x| ≤ (U : ℤ))
    (hBC : ∀ x ∈ BC, |x| ≤ (U : ℤ)) (hAC : ∀ x ∈ AC, |x| ≤ (U : ℤ)) {W : ℤ}
    (hW : |W| ≤ 3 * (U : ℤ)) (a₀ b₀ c₀ : ℤ) :
    (triOf n (maskL n a₀ b₀ (6 * U + 1) AB) (maskL n 0 c₀ (6 * U + 1) BC)
      (affL 1 (-W) AC)).HasZeroTriangle ↔ ExactFrom n AB BC AC W a₀ b₀ c₀ := by
  unfold TriangleInstance.HasZeroTriangle TriangleInstance.IsZeroTriangle ExactFrom
  refine exists_congr fun a => exists_congr fun b => exists_congr fun c => ?_
  have h1 := abs_le.1 (AbsLe.abs_getD_le (Int.natCast_nonneg U) hAB (a.val * n + b.val))
  have h2 := abs_le.1 (AbsLe.abs_getD_le (Int.natCast_nonneg U) hBC (b.val * n + c.val))
  have h3 := abs_le.1 (AbsLe.abs_getD_le (Int.natCast_nonneg U) hAC (a.val * n + c.val))
  have h4 := abs_le.1 hW
  have hb0 : ¬ ((b.val : ℤ) < 0) := by omega
  rw [S_triOf, S_triOf, getD_maskL, getD_maskL, getD_affL _ _ lAC]
  simp only [hb0, false_or]
  split_ifs with hab hc hc <;> constructor <;> intro h <;> omega

/-- If the entries are at most U in absolute value, they are at most 7U + 1 after rows and columns
have been switched off. -/
theorem maskL_le (lAB : AB.length = n * n) (hAB : ∀ x ∈ AB, |x| ≤ (U : ℤ)) (r₀ c₀ : ℤ) :
    ∀ x ∈ maskL n r₀ c₀ (6 * U + 1) AB, |x| ≤ ((7 * U + 1 : ℕ) : ℤ) := by
  intro x hx
  simp only [maskL, List.mem_map, List.mem_range] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have h1 : |AB.getD q 0| ≤ (U : ℤ) := by
    rw [List.getD_eq_getElem _ _ (lAB ▸ hq)]
    exact hAB _ (List.getElem_mem _)
  have h2 := abs_le.1 h1
  push_cast
  split_ifs <;> exact abs_le.2 ⟨by omega, by omega⟩

/-! ## The end of the four searches -/

/-- What the four searches find is a triangle of maximum weight. -/
theorem isMax_of_searches {W a₀ b₀ c₀ : ℤ} (g2 : ¬ AtLeast n AB BC AC (W + 1))
    (a2 : ¬ ExactFrom n AB BC AC W (a₀ + 1) 0 0) (b2 : ¬ ExactFrom n AB BC AC W a₀ (b₀ + 1) 0)
    (c1 : ExactFrom n AB BC AC W a₀ b₀ c₀) (c2 : ¬ ExactFrom n AB BC AC W a₀ b₀ (c₀ + 1)) :
    ∃ a b c : Fin n, a₀ = a.val ∧ b₀ = b.val ∧ c₀ = c.val ∧
      IsMaxWeightTriangle (triOf n AB BC AC) a b c := by
  obtain ⟨a, b, c, ha, hb, hc, hS⟩ := c1
  have ea : a₀ = a.val := by
    by_contra hne
    exact a2 ⟨a, b, c, by omega, by omega, by omega, hS⟩
  have eb : b₀ = b.val := by
    by_contra hne
    exact b2 ⟨a, b, c, ha, by omega, by omega, hS⟩
  have ec : c₀ = c.val := by
    by_contra hne
    exact c2 ⟨a, b, c, ha, hb, by omega, hS⟩
  refine ⟨a, b, c, ea, eb, ec, fun a' b' c' => ?_⟩
  rw [hS]
  by_contra hlt
  exact g2 ⟨a', b', c', by omega⟩

/-- If some triangle has weight at least W and none has weight at least W + 1, some triangle has
weight exactly W. -/
theorem exactFrom_zero {W : ℤ} (g1 : AtLeast n AB BC AC W) (g2 : ¬ AtLeast n AB BC AC (W + 1)) :
    ExactFrom n AB BC AC W 0 0 0 := by
  obtain ⟨a, b, c, h⟩ := g1
  refine ⟨a, b, c, by omega, by omega, by omega, ?_⟩
  by_contra hne
  exact g2 ⟨a, b, c, by omega⟩

/-- No vertex has a number from n on. -/
theorem not_exactFrom {W a₀ b₀ c₀ : ℤ} (h : (n : ℤ) ≤ a₀ ∨ (n : ℤ) ≤ b₀ ∨ (n : ℤ) ≤ c₀) :
    ¬ ExactFrom n AB BC AC W a₀ b₀ c₀ := by
  rintro ⟨a, b, c, ha, hb, hc, -⟩
  have := a.isLt
  have := b.isLt
  have := c.isLt
  omega

end ThreeSumApsp.Spec
