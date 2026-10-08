/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21
public import ThreeSumApsp.Sec3.Theorem21a.Convolution
public import ThreeSumApsp.Spec.Sec3.Problems

/-!
# Convolution-3SUM reduces to Exact Triangle, on lists

Theorem 21(a), after [VW13, Theorem 4.3]: from `N < t²` numbers the reduction makes `2t` instances
of Exact Triangle, each on `t` vertices per part (`Theorem21.convTemplate`).  Here
the instances are lists of integers, row by row, in the form in which a routine fills them
(`convAB`, `convBC`, `convAC`): every weight is a cell of the input, or minus a cell of the input,
at an index that is computed from the two vertices, or a filler if this index is out of range
(`cellOr`).

The three lists are the instance of the template (`triOf_conv`).  So there are `i`, `j` with
`x_i + x_j = x_{i+j}` if and only if one of the `2t` instances has a zero triangle
(`convolution3SUM_vecOf_iff`), and the weights are bounded by a bound for the numbers and the filler
(`abs_convAB_le`, `abs_convBC_le`, `abs_convAC_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- Cell number `z` of a list of `N` numbers, or the filler `F` if `z` is not one of
`0, …, N - 1`. -/
def cellOr (N : ℕ) (F : ℤ) (X : List ℤ) (z : ℤ) : ℤ := if 0 ≤ z ∧ z < N then X.getD z.toNat 0 else F

/-- The weights `w(a,b) = x_{a t + b}`. -/
def convAB (t N : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ => cellOr N F X (q : ℤ)

/-- The weights `w(b,c) = x_{c t + s - b}` of instance number `s`. -/
def convBC (t N s : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ => cellOr N F X (((q % t : ℕ) : ℤ) * t + s - ((q / t : ℕ) : ℤ))

/-- The weights `w(a,c) = -x_{(a + c) t + s}` of instance number `s`.  The filler `-F` inside the
minus sign gives the weight `F`. -/
def convAC (t N s : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ =>
    -cellOr N (-F) X ((((q / t : ℕ) : ℤ) + ((q % t : ℕ) : ℤ)) * t + s)

/-- The first list has `t²` entries. -/
@[simp] theorem length_convAB (t N : ℕ) (F : ℤ) (X : List ℤ) : (convAB t N F X).length = t * t := by
  simp [convAB]

/-- The second list has `t²` entries. -/
@[simp] theorem length_convBC (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    (convBC t N s F X).length = t * t := by
  simp [convBC]

/-- The third list has `t²` entries. -/
@[simp] theorem length_convAC (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    (convAC t N s F X).length = t * t := by
  simp [convAC]

/-- At an index in range `cellOr` reads the cell. -/
theorem cellOr_of_lt {N : ℕ} {F : ℤ} {X : List ℤ} {z : ℤ} {i : ℕ} (hz : z = i) (hi : i < N) :
    cellOr N F X z = X.getD i 0 := by
  subst hz
  rw [cellOr, if_pos ⟨Int.natCast_nonneg i, Int.ofNat_lt.2 hi⟩, Int.toNat_natCast]

/-- At an index out of range `cellOr` returns the filler. -/
theorem cellOr_of_not {N : ℕ} {F : ℤ} {X : List ℤ} {z : ℤ} (hz : ¬ (0 ≤ z ∧ z < N)) :
    cellOr N F X z = F :=
  if_neg hz

/-- A bound for the list and the filler is a bound for `cellOr`. -/
theorem abs_cellOr_le {N : ℕ} {F V : ℤ} {X : List ℤ} (hX : AbsLe X V) (hF : |F| ≤ V) (z : ℤ) :
    |cellOr N F X z| ≤ V := by
  unfold cellOr
  split_ifs
  · exact AbsLe.abs_getD_le ((abs_nonneg F).trans hF) hX _
  · exact hF

/-- The three lists are the instance that the template of the reduction produces. -/
theorem triOf_conv (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    triOf t (convAB t N F X) (convBC t N s F X) (convAC t N s F X) =
      (Theorem21.convTemplate t N s).instantiate (vecOf N X) F := by
  unfold triOf TriangleTemplate.instantiate
  congr 1
  · funext a b
    rw [convAB, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt b.isLt), Theorem21.convTemplate_AB]
    split_ifs with h
    · exact cellOr_of_lt rfl h
    · exact cellOr_of_not fun h' => h (by exact_mod_cast h'.2)
  · funext b c
    rw [convBC, List.getD_map_range _ (Nat.mul_add_lt_mul b.isLt c.isLt),
      Nat.mul_add_div_of_lt c.isLt,
      Nat.mul_add_mod_of_lt c.isLt, Theorem21.convTemplate_BC]
    split_ifs with h
    · exact cellOr_of_lt (by push_cast [h.1]; ring) h.2
    · exact cellOr_of_not fun h' => h (by omega)
  · funext a c
    rw [convAC, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt c.isLt),
      Nat.mul_add_div_of_lt c.isLt,
      Nat.mul_add_mod_of_lt c.isLt, Theorem21.convTemplate_AC]
    split_ifs with h
    · exact congrArg Neg.neg (cellOr_of_lt (by push_cast; ring) h)
    · rw [cellOr_of_not fun h' => h (by exact_mod_cast h'.2), neg_neg]

section Bounds

variable {t N s : ℕ} {F V : ℤ} {X : List ℤ}

/-- The weights `w(a,b)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convAB_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convAB t N F X) V :=
  List.forall_mem_map.2 fun _ _ => abs_cellOr_le hX hF _

/-- The weights `w(b,c)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convBC_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convBC t N s F X) V :=
  List.forall_mem_map.2 fun _ _ => abs_cellOr_le hX hF _

/-- The weights `w(a,c)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convAC_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convAC t N s F X) V :=
  List.forall_mem_map.2 fun _ _ => (abs_neg _).trans_le (abs_cellOr_le hX (by rwa [abs_neg]) _)

end Bounds

/-- **The reduction on lists.**  For a list of `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the `2t` instances, filled with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_vecOf_iff {t N : ℕ} (hN : 1 ≤ N) (hNt : N < t * t) {X : List ℤ} {U : ℤ}
    (hU : 0 ≤ U) (hX : AbsLe X U) :
    Convolution3SUM (vecOf N X) ↔
      ∃ s < 2 * t, (triOf t (convAB t N (2 * U + 1) X) (convBC t N s (2 * U + 1) X)
        (convAC t N s (2 * U + 1) X)).HasZeroTriangle := by
  simp only [triOf_conv]
  exact Theorem21.convolution3SUM_iff hN hNt fun i => AbsLe.abs_getD_le hU hX _

end ThreeSumApsp.Spec
