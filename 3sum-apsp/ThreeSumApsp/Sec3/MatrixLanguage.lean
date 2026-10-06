/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 3.1: the lopsided problem in matrix language, and footnote 8

Section 3.1: "The counting version #Lop-AE-SparseTri(n,D) is also equivalent, up to polylogarithmic
factors, to [...] computing the wanted entries (XY)[I,J], (I,J) ∈ W, of a thin matrix product".
This file proves the two directions, without running times.  Of its lemmas, the programs for
Corollaries 15 and 16 use `LopInstance.numTriangles_ne_zero_iff` and `Footnote8.zero_one`; nothing
rests on the others.

* **From an instance to matrices.**  Number the at most `D` middle vertices of an instance by column
  indices (`LopInstance.MiddleAtMost.nonempty_embedding`), and let `X` and `Y` be its biadjacency
  matrices.  The Boolean product of `X` and `Y` has a 1 at `(a, b)` exactly if the pair lies in a
  triangle (`LopInstance.boolProduct_eq_one_iff_inTriangle`), and `(XY)[a,b]` is the number of
  common neighbors of `a` and `b` (`LopInstance.matX_mul_matY_apply`), which is nonzero exactly if
  the pair lies in a triangle (`LopInstance.matX_mul_matY_apply_ne_zero_iff`).  So an instance of
  #Lop-AE-SparseTri asks for the wanted entries of a thin matrix product
  (`LopInstance.isCountingAnswer_iff_isWantedEntries`), and its answer also answers Lop-AE-SparseTri
  (`LopInstance.isDetectionAnswer_of_isCountingAnswer`).
* **Footnote 8**, the converse.  The entries of a product of two 0/1 matrices are the triangle
  counts of an instance (`Footnote8.zero_one`).  The entries of a product of integer matrices with
  `β`-bit entries are combinations of the triangle counts of `4β²` instances
  (`Footnote8.entries_from_counts`): split into positive and negative parts (`Footnote8.parts`),
  write the entries in binary (`Footnote8.binary`), and multiply out (`Footnote8.product`).  Entries
  of absolute value `n^{O(1)}` have `O(log n)` bits (`Footnote8.bits`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ### The two tasks -/

/-- **Definition 14**, the task: "for every edge (a, b) ∈ W we ask for the number of triangles it
lies in".  `ans` is a correct answer to the instance `I` of #Lop-AE-SparseTri; its values outside
`W` are not constrained. -/
def LopInstance.IsCountingAnswer {n : ℕ} (I : LopInstance n) (ans : Fin n × Fin n → ℕ) : Prop :=
  ∀ q ∈ I.W, ans q = I.numTriangles q.1 q.2

/-- Section 3.1 and Theorem 5: "computing the wanted entries (XY)[I,J], (I,J) ∈ W, of a thin
matrix product".  `ans` gives the wanted entries of `XY`; its values outside `W` are not
constrained. -/
def IsWantedEntries {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) (ans : Fin n × Fin n → ℤ) : Prop :=
  ∀ q ∈ W, ans q = (X * Y) q.1 q.2

/-! ### From an instance to matrices -/

open Classical in
/-- Section 3.1: "let X ∈ {0,1}^{n×D} [...] be the biadjacency [matrix] of the edges between A and M
[...], that is, X[a,v] = 1 if and only if a ∈ A and v ∈ M are adjacent [...] (padded with zeros if M
has fewer than D vertices)".  The paper leaves the numbering of the middle vertices by column
indices implicit; here it is an arbitrary injection `e` of `M` into the `D` column indices, and the
columns outside its range are the padding. -/
noncomputable def LopInstance.matX {n D : ℕ} (I : LopInstance n) (e : I.M ↪ Fin D) :
    Matrix (Fin n) (Fin D) ℤ :=
  Matrix.of fun a j => if ∃ v : I.M, e v = j ∧ I.adjA a v then 1 else 0

open Classical in
/-- Section 3.1: "Y ∈ {0,1}^{D×n} [...], Y[v,b] = 1 if and only if v ∈ M and b ∈ B are adjacent
(padded with zeros if M has fewer than D vertices)".  See `LopInstance.matX` for `e`. -/
noncomputable def LopInstance.matY {n D : ℕ} (I : LopInstance n) (e : I.M ↪ Fin D) :
    Matrix (Fin D) (Fin n) ℤ :=
  Matrix.of fun j b => if ∃ v : I.M, e v = j ∧ I.adjB v b then 1 else 0

/-- Section 3.1: "the Boolean product of X and Y", for matrices with entries 0 and 1: the entry at
`(a, b)` is 1 if `X[a,j] = Y[j,b] = 1` for some `j`, and 0 otherwise. -/
def boolProduct {n D m : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin m) ℤ) :
    Matrix (Fin n) (Fin m) ℤ :=
  Matrix.of fun a b => if ∃ j : Fin D, X a j = 1 ∧ Y j b = 1 then 1 else 0

namespace LopInstance

variable {n D : ℕ} (I : LopInstance n) (e : I.M ↪ Fin D)

/-- Section 3.1, "(padded with zeros if M has fewer than D vertices)": a middle part of at most `D`
vertices can be numbered by column indices.  The lemmas below hold for every such numbering `e`. -/
theorem MiddleAtMost.nonempty_embedding {I : LopInstance n} (h : I.MiddleAtMost D) :
    Nonempty (I.M ↪ Fin D) :=
  Function.Embedding.nonempty_of_card_le (by simpa [MiddleAtMost] using h)

open Classical in
/-- Section 3.1: "X[a,v] = 1 if and only if a ∈ A and v ∈ M are adjacent".  The entry of `X` in the
column `e v` of the middle vertex `v`. -/
theorem matX_apply_emb (a : Fin n) (v : I.M) :
    I.matX e a (e v) = if I.adjA a v then 1 else 0 := by
  simp [matX]

open Classical in
/-- Section 3.1: "Y[v,b] = 1 if and only if v ∈ M and b ∈ B are adjacent".  The entry of `Y` in the
row `e v` of the middle vertex `v`. -/
theorem matY_apply_emb (v : I.M) (b : Fin n) :
    I.matY e (e v) b = if I.adjB v b then 1 else 0 := by
  simp [matY]

/-- Section 3.1, "(padded with zeros if M has fewer than D vertices)": a column of `X` that belongs
to no middle vertex is zero. -/
theorem matX_apply_of_notMem_range (a : Fin n) {j : Fin D} (hj : j ∉ Set.range e) :
    I.matX e a j = 0 :=
  if_neg fun ⟨v, hv, _⟩ => hj ⟨v, hv⟩

open Classical in
/-- The number of triangles through a pair, as the number of elements of a finite set. -/
theorem numTriangles_eq_card (a b : Fin n) :
    I.numTriangles a b = (Finset.univ.filter fun v : I.M => I.adjA a v ∧ I.adjB v b).card := by
  rw [numTriangles, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [commonNeighbors]

/-- A pair lies in a triangle exactly if its number of triangles is not zero. -/
theorem numTriangles_ne_zero_iff (a b : Fin n) : I.numTriangles a b ≠ 0 ↔ I.InTriangle a b := by
  classical
  rw [numTriangles_eq_card, Finset.card_ne_zero, Finset.filter_nonempty_iff]
  simp [InTriangle]

/-- Section 3.1: "Lop-AE-SparseTri(n,D) asks for the entries of the Boolean product of X and Y at
the positions in W".  The entry at `(a, b)` is 1 exactly if the pair lies in a triangle. -/
theorem boolProduct_eq_one_iff_inTriangle (a b : Fin n) :
    boolProduct (I.matX e) (I.matY e) a b = 1 ↔ I.InTriangle a b := by
  classical
  simp only [boolProduct, Matrix.of_apply, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  constructor
  · rintro ⟨j, hX, hY⟩
    -- A column in which `X` has an entry 1 belongs to a middle vertex.
    obtain ⟨v, rfl⟩ : j ∈ Set.range e := by
      by_contra hj
      simp [I.matX_apply_of_notMem_range e a hj] at hX
    exact ⟨v, by simpa [I.matX_apply_emb] using hX, by simpa [I.matY_apply_emb] using hY⟩
  · rintro ⟨v, hA, hB⟩
    exact ⟨e v, by simp [I.matX_apply_emb, hA], by simp [I.matY_apply_emb, hB]⟩

/-- Section 3.1: "#Lop-AE-SparseTri(n,D) asks for the corresponding entries of the product of X and
Y over the integers"; proof of Corollary 15: "the entries (XY)[a,b] [...] are the numbers of common
neighbors". -/
theorem matX_mul_matY_apply (a b : Fin n) :
    (I.matX e * I.matY e) a b = (I.numTriangles a b : ℤ) := by
  classical
  rw [Matrix.mul_apply, I.numTriangles_eq_card, Finset.card_filter, Nat.cast_sum]
  -- Only the columns of the middle vertices matter.
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) fun j _ hj => by
    rw [I.matX_apply_of_notMem_range e a (by simpa using hj), zero_mul], Finset.sum_map]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [I.matX_apply_emb, I.matY_apply_emb]
  by_cases hA : I.adjA a v <;> by_cases hB : I.adjB v b <;> simp [hA, hB]

/-- Proof of Corollary 15: "and they are nonzero exactly for the query pairs that lie in a
triangle". -/
theorem matX_mul_matY_apply_ne_zero_iff (a b : Fin n) :
    (I.matX e * I.matY e) a b ≠ 0 ↔ I.InTriangle a b := by
  rw [LopInstance.matX_mul_matY_apply, Ne, Nat.cast_eq_zero]
  exact I.numTriangles_ne_zero_iff a b

/-- Section 3.1, "In the language of Section 2, W is the set of wanted positions": the correct
answers to an instance of #Lop-AE-SparseTri are exactly the wanted entries of the thin product of
its two biadjacency matrices. -/
theorem isCountingAnswer_iff_isWantedEntries (ans : Fin n × Fin n → ℕ) :
    I.IsCountingAnswer ans ↔ IsWantedEntries (I.matX e) (I.matY e) I.W (fun q => (ans q : ℤ)) := by
  simp only [LopInstance.IsCountingAnswer, IsWantedEntries, LopInstance.matX_mul_matY_apply,
    Nat.cast_inj]

/-- Proof of Corollary 15: a correct answer to the counting problem gives a correct answer to the
detection problem (Corollaries 15 and 16 solve both at once). -/
theorem isDetectionAnswer_of_isCountingAnswer (ans : Fin n × Fin n → ℕ)
    (h : I.IsCountingAnswer ans) :
    I.IsDetectionAnswer (fun q => decide (ans q ≠ 0)) := by
  intro q hq
  rw [decide_eq_true_iff, h q hq]
  exact I.numTriangles_ne_zero_iff q.1 q.2

end LopInstance

/-! ### Footnote 8 -/

/-- Footnote 8: the positive part of an integer matrix, entry by entry `max(x, 0)`. -/
def matPos {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) : Matrix (Fin n) (Fin m) ℤ :=
  Matrix.of fun i j => max (X i j) 0

/-- Footnote 8: the negative part of an integer matrix, entry by entry `max(-x, 0)`, so that
`X = matPos X - matNeg X`. -/
def matNeg {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) : Matrix (Fin n) (Fin m) ℤ :=
  Matrix.of fun i j => max (-(X i j)) 0

/-- Footnote 8: "write their entries in binary, X = ∑_i 2^i X_i [...] with 0/1 matrices X_i".
`matBit X i` is `X_i`: its entries are the binary digits of weight `2^i` of the entries of `X` (used
for matrices with entries `≥ 0`). -/
def matBit {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) (i : ℕ) : Matrix (Fin n) (Fin m) ℤ :=
  Matrix.of fun a j => X a j / 2 ^ i % 2

/-- The instance that two matrices describe has the `D` column indices as its middle part. -/
theorem LopInstance.ofMatrices_middleAtMost {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) :
    (LopInstance.ofMatrices X Y W).MiddleAtMost D :=
  (Fintype.card_fin D).le

/-- Footnote 8, first sentence: "An instance of #Lop-AE-SparseTri(n,D) asks for the wanted entries
of a thin matrix product of two 0/1 matrices."  Conversely to `LopInstance.matX_mul_matY_apply`: the
entries of a product of two 0/1 matrices are the triangle counts of the instance `ofMatrices X Y W`,
whatever `W` is. -/
theorem Footnote8.zero_one {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) (hX : ∀ a j, X a j = 0 ∨ X a j = 1)
    (hY : ∀ j b, Y j b = 0 ∨ Y j b = 1) (a b : Fin n) :
    (X * Y) a b = ((LopInstance.ofMatrices X Y W).numTriangles a b : ℤ) := by
  classical
  rw [Matrix.mul_apply, LopInstance.numTriangles_eq_card, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hX a j with hx | hx <;> rcases hY j b with hy | hy <;>
    simp [LopInstance.ofMatrices, hx, hy]

/-- Footnote 8: "split each matrix into its positive and negative parts". -/
theorem Footnote8.parts {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) :
    X = matPos X - matNeg X := by
  ext i j
  simp only [matPos, matNeg, Matrix.sub_apply, Matrix.of_apply]
  omega

/-- `x mod 2^β` is the sum of the last `β` binary digits of `x`, with their weights. -/
private theorem emod_two_pow_eq_sum_digits (x : ℤ) (β : ℕ) :
    x % 2 ^ β = ∑ i ∈ Finset.range β, 2 ^ i * (x / 2 ^ i % 2) := by
  induction β with
  | zero => simp
  | succ β ih =>
    have h : x / (2 ^ β * 2) = x / 2 ^ β / 2 := (Int.ediv_ediv_of_nonneg (by positivity)).symm
    rw [Finset.sum_range_succ, ← ih, pow_succ, Int.emod_def, Int.emod_def x (2 ^ β),
      Int.emod_def (x / 2 ^ β), h]
    ring

/-- Footnote 8: "write their entries in binary, X = ∑_i 2^i X_i", for a matrix with entries in
`[0, 2^β)`. -/
theorem Footnote8.binary {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) (β : ℕ)
    (hX : ∀ a j, 0 ≤ X a j ∧ X a j < 2 ^ β) :
    X = ∑ i ∈ Finset.range β, (2 : ℤ) ^ i • matBit X i := by
  ext a j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, matBit, Matrix.of_apply, smul_eq_mul]
  rw [← emod_two_pow_eq_sum_digits, Int.emod_eq_of_lt (hX a j).1 (hX a j).2]

/-- Footnote 8: "with 0/1 matrices X_i". -/
theorem matBit_eq_zero_or_one {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) (i : ℕ) (a : Fin n)
    (j : Fin m) : matBit X i a j = 0 ∨ matBit X i a j = 1 := by
  simp only [matBit, Matrix.of_apply]
  omega

/-- Footnote 8: "Then XY = ∑_{i,j} 2^{i+j} X_i Y_j", for matrices with entries in `[0, 2^β)`. -/
theorem Footnote8.product {n D m : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin m) ℤ)
    (β : ℕ) (hX : ∀ a j, 0 ≤ X a j ∧ X a j < 2 ^ β) (hY : ∀ j b, 0 ≤ Y j b ∧ Y j b < 2 ^ β) :
    X * Y = ∑ i ∈ Finset.range β, ∑ j ∈ Finset.range β,
      (2 : ℤ) ^ (i + j) • (matBit X i * matBit Y j) := by
  conv_lhs => rw [Footnote8.binary X β hX, Footnote8.binary Y β hY]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_add]

/-- Footnote 8 for matrices with entries in `[0, 2^β)`: every entry of the product is a combination
of the triangle counts of the `β²` instances given by a binary digit of `X` and one of `Y`. -/
private theorem mul_apply_eq_sum_numTriangles {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) (β : ℕ)
    (hX : ∀ a j, 0 ≤ X a j ∧ X a j < 2 ^ β) (hY : ∀ j b, 0 ≤ Y j b ∧ Y j b < 2 ^ β) (a b : Fin n) :
    (X * Y) a b = ∑ i ∈ Finset.range β, ∑ j ∈ Finset.range β, (2 : ℤ) ^ (i + j) *
      ((LopInstance.ofMatrices (matBit X i) (matBit Y j) W).numTriangles a b : ℤ) := by
  rw [Footnote8.product X Y β hX hY, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Footnote8.zero_one _ _ W (matBit_eq_zero_or_one X i)
    (matBit_eq_zero_or_one Y j)]

/-- The two parts of a matrix with entries of absolute value less than `2^β` have entries in
`[0, 2^β)`. -/
private theorem matPos_matNeg_lt {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) {β : ℕ}
    (hX : ∀ a j, |X a j| < 2 ^ β) :
    (∀ a j, 0 ≤ matPos X a j ∧ matPos X a j < 2 ^ β) ∧
      ∀ a j, 0 ≤ matNeg X a j ∧ matNeg X a j < 2 ^ β := by
  have hpow : (0 : ℤ) < 2 ^ β := by positivity
  exact ⟨fun a j => ⟨le_max_right _ _, max_lt ((le_abs_self _).trans_lt (hX a j)) hpow⟩,
    fun a j => ⟨le_max_right _ _, max_lt ((neg_le_abs _).trans_lt (hX a j)) hpow⟩⟩

/-- Footnote 8, conclusion: "so a product with b-bit entries costs O(b²) instances
of #Lop-AE-SparseTri(n,D) with the same query pairs W".  (The paper's `b` is `β` here.)  For
matrices with entries of absolute value less than `2^β`, every entry of `XY` is the sum, with
weights `2^{i+j}` and signs +, −, −, +, of the triangle counts of the `4β²` instances given by a
binary digit of the positive or negative part of `X` and one of `Y`, all with the same `W`. -/
theorem Footnote8.entries_from_counts {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) (β : ℕ)
    (hX : ∀ a j, |X a j| < 2 ^ β) (hY : ∀ j b, |Y j b| < 2 ^ β) (a b : Fin n) :
    (X * Y) a b = ∑ i ∈ Finset.range β, ∑ j ∈ Finset.range β, (2 : ℤ) ^ (i + j) *
      (((LopInstance.ofMatrices (matBit (matPos X) i) (matBit (matPos Y) j) W).numTriangles
          a b : ℤ)
        - ((LopInstance.ofMatrices (matBit (matPos X) i) (matBit (matNeg Y) j) W).numTriangles
            a b : ℤ)
        - ((LopInstance.ofMatrices (matBit (matNeg X) i) (matBit (matPos Y) j) W).numTriangles
            a b : ℤ)
        + ((LopInstance.ofMatrices (matBit (matNeg X) i) (matBit (matNeg Y) j) W).numTriangles
            a b : ℤ)) := by
  obtain ⟨hXpos, hXneg⟩ := matPos_matNeg_lt X hX
  obtain ⟨hYpos, hYneg⟩ := matPos_matNeg_lt Y hY
  -- `XY` is a signed sum of the four products of a part of `X` and a part of `Y`.
  conv_lhs => rw [Footnote8.parts X, Footnote8.parts Y]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.sub_apply]
  rw [mul_apply_eq_sum_numTriangles _ _ W β hXpos hYpos,
    mul_apply_eq_sum_numTriangles _ _ W β hXpos hYneg,
    mul_apply_eq_sum_numTriangles _ _ W β hXneg hYpos,
    mul_apply_eq_sum_numTriangles _ _ W β hXneg hYneg]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Footnote 8 with the sentence it belongs to, "matrices [...] whose entries have absolute value
n^{O(1)}": an integer of absolute value at most `n^c` has `β = ⌊c log₂ n⌋ + 1` bits, that is,
`O(log n)`, so that "O(b²) instances" is a polylogarithmic number. -/
theorem Footnote8.bits {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (x : ℤ)
    (hx : ((|x| : ℤ) : ℝ) ≤ (n : ℝ) ^ c) :
    |x| < 2 ^ (⌊c * Real.logb 2 n⌋₊ + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : ((|x| : ℤ) : ℝ) < (2 : ℝ) ^ (⌊c * Real.logb 2 n⌋₊ + 1) :=
    calc ((|x| : ℤ) : ℝ) ≤ (n : ℝ) ^ c := hx
      _ = (2 : ℝ) ^ (c * Real.logb 2 n) := by
          rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
      _ < (2 : ℝ) ^ ((⌊c * Real.logb 2 n⌋₊ + 1 : ℕ) : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by exact_mod_cast Nat.lt_floor_add_one _)
      _ = (2 : ℝ) ^ (⌊c * Real.logb 2 n⌋₊ + 1) := Real.rpow_natCast _ _
  exact_mod_cast hlt

end ThreeSumApsp
