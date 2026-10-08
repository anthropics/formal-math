/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Theorem 21(a): Convolution-3SUM reduces to Exact Triangle

[VW13, Theorem 4.3] in the form needed for Theorem 21(a): Convolution-3SUM on `N < t²`
numbers becomes `2t` instances of Exact Triangle on `t` vertices per part.  In instance `s` the
triangle `(a, b, c)` stands for the pair `i = at + b`, `j = ct + s - b` (`convTemplate`).  Every
solution is such a triangle (`exists_hasZeroTriangle`), and a zero triangle is a solution, because
an index out of range gives a weight so large that the sum is positive
(`convolution3SUM_of_isZeroTriangle`).  Together: `convolution3SUM_iff`, and with `t = ⌊√N⌋ + 1`,
`theorem_21a_convolution_to_exact`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem21

/-- Instance `s` of the reduction from Convolution-3SUM.  The triangle `(a, b, c)` stands for the
pair `i = a t + b`, `j = c t + s - b`, for which `i + j = (a + c) t + s`: the edge `(a, b)` carries
`x_i`, the edge `(b, c)` carries `x_j`, and the edge `(a, c)` carries `-x_{i+j}`.  An edge whose
index is out of range gets the filler weight. -/
def convTemplate (t N s : ℕ) : TriangleTemplate t N where
  eAB a b := if h : a.val * t + b.val < N then some (false, ⟨a.val * t + b.val, h⟩) else none
  eBC b c :=
    if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
      some (false, ⟨c.val * t + s - b.val, h.2⟩)
    else none
  eAC a c :=
    if h : (a.val + c.val) * t + s < N then some (true, ⟨(a.val + c.val) * t + s, h⟩) else none

/-- The weight of the edge `(a, b)`. -/
theorem convTemplate_AB {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (a b : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAB a b)
      = if h : a.val * t + b.val < N then x ⟨a.val * t + b.val, h⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- The weight of the edge `(b, c)`. -/
theorem convTemplate_BC {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (b c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eBC b c)
      = if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
          x ⟨c.val * t + s - b.val, h.2⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- The weight of the edge `(a, c)`. -/
theorem convTemplate_AC {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (a c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAC a c)
      = if h : (a.val + c.val) * t + s < N then -x ⟨(a.val + c.val) * t + s, h⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- A solution `(i, j)` is the triangle `(⌊i/t⌋, i mod t, ⌊j/t⌋)` of the instance
`s = (j mod t) + (i mod t)`. -/
private theorem exists_hasZeroTriangle {t N : ℕ} {x : Fin N → ℤ} {fill : ℤ} (hNt : N < t * t)
    {i j : Fin N} (hij : i.val + j.val < N) (h : x i + x j = x ⟨i.val + j.val, hij⟩) :
    ∃ s < 2 * t, ((convTemplate t N s).instantiate x fill).HasZeroTriangle := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hit := Nat.mod_lt i.val ht
  have hjt := Nat.mod_lt j.val ht
  have hj := Nat.div_add_mod' j.val t
  -- The three indices are `i`, `j` and `i + j`, so they are in range.
  have hAB : i.val / t * t + i.val % t = i.val := Nat.div_add_mod' i.val t
  have hBC : j.val / t * t + (j.val % t + i.val % t) - i.val % t = j.val := by omega
  have hAC : (i.val / t + j.val / t) * t + (j.val % t + i.val % t) = i.val + j.val := by
    rw [Nat.add_mul]
    omega
  refine ⟨j.val % t + i.val % t, by omega, ⟨i.val / t, Nat.div_lt_of_lt_mul (i.isLt.trans hNt)⟩,
    ⟨i.val % t, hit⟩, ⟨j.val / t, Nat.div_lt_of_lt_mul (j.isLt.trans hNt)⟩, ?_⟩
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate,
    convTemplate_AB, convTemplate_BC, convTemplate_AC]
  rw [dif_pos (hAB.trans_lt i.isLt), dif_pos ⟨by omega, hBC.trans_lt j.isLt⟩,
    dif_pos (hAC.trans_lt hij)]
  simp only [hAB, hBC, hAC, Fin.eta, h]
  ring

/-- With the filler `2U + 1`, every weight is at least `-U`. -/
private theorem neg_le_templateWeight {N : ℕ} {x : Fin N → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) (o : Option (Bool × Fin N)) : -U ≤ templateWeight x (2 * U + 1) o := by
  rcases o with _ | ⟨_ | _, i⟩ <;> simp only [templateWeight]
  · omega
  · exact (abs_le.mp (hx i)).1
  · exact neg_le_neg (abs_le.mp (hx i)).2

/-- A zero triangle of an instance with the filler `2U + 1` is a solution. -/
private theorem convolution3SUM_of_isZeroTriangle {t N s : ℕ} {x : Fin N → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) {a b c : Fin t}
    (h : ((convTemplate t N s).instantiate x (2 * U + 1)).IsZeroTriangle a b c) :
    Convolution3SUM x := by
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate] at h
  have hgeAB := neg_le_templateWeight hU hx ((convTemplate t N s).eAB a b)
  have hgeBC := neg_le_templateWeight hU hx ((convTemplate t N s).eBC b c)
  have hgeAC := neg_le_templateWeight hU hx ((convTemplate t N s).eAC a c)
  -- One filler `2U + 1` and two weights that are at least `-U` have a positive sum, so the three
  -- indices are in range.
  have hAB : a.val * t + b.val < N := by
    by_contra hout
    rw [convTemplate_AB, dif_neg hout] at h
    omega
  have hBC : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N := by
    by_contra hout
    rw [convTemplate_BC, dif_neg hout] at h
    omega
  have hAC : (a.val + c.val) * t + s < N := by
    by_contra hout
    rw [convTemplate_AC, dif_neg hout] at h
    omega
  rw [convTemplate_AB, convTemplate_BC, convTemplate_AC, dif_pos hAB, dif_pos hBC, dif_pos hAC] at h
  -- The triangle stands for `i = at + b` and `j = ct + s - b`, and `i + j = (a + c)t + s`.
  have hsum : a.val * t + b.val + (c.val * t + s - b.val) = (a.val + c.val) * t + s := by
    rw [Nat.add_mul]
    omega
  refine ⟨⟨a.val * t + b.val, hAB⟩, ⟨c.val * t + s - b.val, hBC.2⟩, hsum ▸ hAC, ?_⟩
  simp only [hsum]
  -- `h` says `x_i + x_j - x_{i+j} = 0`.
  linarith [h]

/-- The reduction of [VW13, Theorem 4.3], for `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the instances `s < 2t`, with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_iff {t N : ℕ} {x : Fin N → ℤ} {U : ℤ} (hN : 1 ≤ N) (hNt : N < t * t)
    (hx : ∀ i, |x i| ≤ U) :
    Convolution3SUM x ↔
      ∃ s < 2 * t, ((convTemplate t N s).instantiate x (2 * U + 1)).HasZeroTriangle := by
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact exists_hasZeroTriangle hNt hij h
  · rintro ⟨s, -, a, b, c, h⟩
    exact convolution3SUM_of_isZeroTriangle ((abs_nonneg _).trans (hx ⟨0, hN⟩)) hx h

end Theorem21

/-- The combinatorial content of [VW13, Theorem 4.3] in the form needed for **Theorem 21(a)**:
whether an array of `N` integers is a yes-instance of Convolution-3SUM is decided by asking `O(√N)`
times whether there is a zero triangle, each time in an instance with `O(√N)` vertices in each part
whose weights are entries of the array, up to sign, or a filler.  There are at most `2t` instances,
each with `t ≤ √N + 1` vertices in every part.  Each of their weights is a copy of some `±x_i`, at a
position `i` that does not depend on the numbers, or the filler `2U + 1`, where `U` bounds the
`|x_i|`. -/
theorem theorem_21a_convolution_to_exact (N : ℕ) (hN : 1 ≤ N) :
    ∃ (t : ℕ) (L : List (TriangleTemplate t N)),
      (t : ℝ) ≤ Real.sqrt N + 1 ∧
      L.length ≤ 2 * t ∧
      ∀ (x : Fin N → ℤ) (U : ℤ), (∀ i, |x i| ≤ U) →
        (Convolution3SUM x ↔ ∃ τ ∈ L, (τ.instantiate x (2 * U + 1)).HasZeroTriangle) := by
  refine ⟨Nat.sqrt N + 1,
    (List.range (2 * (Nat.sqrt N + 1))).map (Theorem21.convTemplate (Nat.sqrt N + 1) N), ?_,
    by rw [List.length_map, List.length_range], fun x U hx => ?_⟩
  · push_cast
    linarith [Real.nat_sqrt_le_real_sqrt (a := N)]
  · rw [Theorem21.convolution3SUM_iff hN (Nat.lt_succ_sqrt N) hx]
    simp only [List.mem_map, List.mem_range, exists_exists_and_eq_and]

end ThreeSumApsp
