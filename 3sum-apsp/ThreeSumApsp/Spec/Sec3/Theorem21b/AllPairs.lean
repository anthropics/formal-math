/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Util.Flag

/-!
# All pairs with a witness, by marking

The middle step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
Given three `n × n` matrices `X`, `Y`, `V`, the task is to mark all pairs `(i, j)` for which some
`k` has `X[i,k] + Y[k,j] < V[i,j]` (`Witness`, `PairHit`).  The three ranges are cut into blocks of
`s` indices.

* The last block of a range is moved back so that it ends at `n`; blocks may overlap, and there are
  no padding vertices (`blockOff`, `blockCount`, `exists_block`).
* For a triple of blocks, the `s × s × s` instance `blockTri` has the weights `X[i,k]`, `Y[k,j]` and
  `-V[i,j]`; a pair that is already marked gets the weight `F = 2U + 1` instead of `-V[i,j]`
  (`maskNeg`), which is too large for a negative triangle.
* So every negative triangle that is found is an unmarked pair with a witness (`unmarked_of_neg`),
  marking it keeps the marks right (`Marks.set`) and lowers the number of unmarked pairs
  (`count_set_one`).  If the instance of a triple has no negative triangle, then every pair of the
  triple with a witness in the middle block is marked (`BlockDone`, `blockDone_of_not`), and this
  stays so when more pairs are marked (`BlockDone.set`).
* When all triples are done, the marks are the answer (`Marks.complete`).
* `tripleIdx p I K J` is the position of a triple in the order in which the triples are visited.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Blocks -/

/-- The offset of block number `I`: `I s`, or `n - s` if the block would otherwise go beyond `n`. -/
def blockOff (n s I : ℕ) : ℕ := if I * s + s ≤ n then I * s else n - s

/-- The number of blocks: `⌈n/s⌉`. -/
def blockCount (n s : ℕ) : ℕ := (n + s - 1) / s

/-- A block ends at `n` or before. -/
theorem blockOff_add_le {n s : ℕ} (hs : s ≤ n) (I : ℕ) : blockOff n s I + s ≤ n := by
  unfold blockOff
  split_ifs <;> omega

/-- `i` blocks do not cover the range exactly if `i` is less than the number of blocks. -/
theorem lt_blockCount_iff {n s : ℕ} (hs : 1 ≤ s) (i : ℕ) : i < blockCount n s ↔ i * s < n :=
  Nat.lt_ceilDiv_iff hs

/-- The blocks overshoot the range by less than one block. -/
theorem blockCount_mul_lt {n s : ℕ} (hs : 1 ≤ s) : blockCount n s * s < n + s :=
  Nat.ceilDiv_mul_lt hs

/-- The blocks cover the range. -/
theorem le_blockCount_mul {n s : ℕ} (hs : 1 ≤ s) : n ≤ blockCount n s * s :=
  Nat.le_ceilDiv_mul hs

/-- A range that is not empty has a block. -/
theorem blockCount_pos {n s : ℕ} (hs : 1 ≤ s) (hn : 1 ≤ n) : 1 ≤ blockCount n s :=
  (lt_blockCount_iff hs 0).2 (by omega)

/-- There are at most `n` blocks. -/
theorem blockCount_le {n s : ℕ} (hs : 1 ≤ s) : blockCount n s ≤ n :=
  (Nat.ceilDiv_le_iff hs).2 (Nat.le_mul_of_pos_right n hs)

/-- Every index lies in a block. -/
theorem exists_block {n s i : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ n) (hi : i < n) :
    ∃ I < blockCount n s, ∃ a < s, i = blockOff n s I + a := by
  have hdiv : i / s * s + i % s = i := Nat.div_add_mod' i s
  have hmod : i % s < s := Nat.mod_lt _ hs1
  refine ⟨i / s, (lt_blockCount_iff hs1 _).2 (by omega), ?_⟩
  unfold blockOff
  split_ifs with h
  · exact ⟨i % s, hmod, hdiv.symm⟩
  · exact ⟨i - (n - s), by omega, by omega⟩

/-! ## The order of the triples -/

/-- The position of the triple `(I, K, J)` of numbers below `p` in the lexicographic order. -/
def tripleIdx (p I K J : ℕ) : ℕ := (I * p + K) * p + J

/-- The position determines the triple. -/
theorem tripleIdx_inj {p I K J I' K' J' : ℕ} (hK : K < p) (hJ : J < p) (hK' : K' < p)
    (hJ' : J' < p) (h : tripleIdx p I K J = tripleIdx p I' K' J') : I = I' ∧ K = K' ∧ J = J' := by
  obtain ⟨hIK, hJJ⟩ := Nat.mul_add_inj_of_lt hJ hJ' h
  obtain ⟨hII, hKK⟩ := Nat.mul_add_inj_of_lt hK hK' hIK
  exact ⟨hII, hKK, hJJ⟩

/-- The positions are below `p³`. -/
theorem tripleIdx_lt {p I K J : ℕ} (hI : I < p) (hK : K < p) (hJ : J < p) :
    tripleIdx p I K J < p * p * p :=
  Nat.mul_add_lt_mul (Nat.mul_add_lt_mul hI hK) hJ

/-- The next triple, when only `J` moves. -/
theorem tripleIdx_succ_J (p I K J : ℕ) : tripleIdx p I K (J + 1) = tripleIdx p I K J + 1 := rfl

/-- The next triple, when `J` starts again and `K` moves. -/
theorem tripleIdx_succ_K (p I K : ℕ) :
    tripleIdx (p + 1) I (K + 1) 0 = tripleIdx (p + 1) I K p + 1 := by
  unfold tripleIdx
  ring

/-- The next triple, when `J` and `K` start again and `I` moves. -/
theorem tripleIdx_succ_I (p I : ℕ) :
    tripleIdx (p + 1) (I + 1) 0 0 = tripleIdx (p + 1) I p p + 1 := by
  unfold tripleIdx
  ring

/-- The position after the last triple. -/
theorem tripleIdx_top (p : ℕ) : tripleIdx p p 0 0 = p * p * p := by
  simp [tripleIdx]

/-! ## The third matrix of a block instance -/

/-- The weights of the pairs `(a, c)`: `F` for a marked pair, and `-V` otherwise. -/
def maskNeg (F : ℤ) (O V : List ℤ) : List ℤ := List.zipWith (fun o v => if o = 1 then F else -v) O V

/-- The third matrix is as long as the shorter of the two lists. -/
@[simp] theorem length_maskNeg (F : ℤ) (O V : List ℤ) :
    (maskNeg F O V).length = min O.length V.length := by
  simp [maskNeg]

/-- An entry of the third matrix. -/
theorem getElem_maskNeg {F : ℤ} {O V : List ℤ} {i : ℕ} (hO : i < O.length) (hV : i < V.length)
    (h : i < (maskNeg F O V).length) : (maskNeg F O V)[i] = if O[i] = 1 then F else -V[i] := by
  simp [maskNeg]

/-- An entry of the third matrix, read with a default. -/
theorem getD_maskNeg {F : ℤ} {O V : List ℤ} {i : ℕ} (hO : i < O.length) (hV : i < V.length) :
    (maskNeg F O V).getD i 0 = if O.getD i 0 = 1 then F else -V.getD i 0 := by
  have h : i < (maskNeg F O V).length := by
    rw [length_maskNeg]
    omega
  rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ hO, List.getD_eq_getElem _ _ hV,
    getElem_maskNeg hO hV]

/-- A bound on `F` and on the entries of `V` is a bound on the entries of the third matrix. -/
theorem abs_le_of_mem_maskNeg {F U : ℤ} {O V : List ℤ} (hF : |F| ≤ U) (hV : AbsLe V U) :
    AbsLe (maskNeg F O V) U := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < O.length ∧ i < V.length := by simpa using hi
  rw [getElem_maskNeg hi'.1 hi'.2]
  split_ifs
  · exact hF
  · rw [abs_neg]
    exact hV _ (List.getElem_mem _)

/-! ## Marks -/

/-- The index `k` is a witness for the pair `(i, j)`: `X[i,k] + Y[k,j] < V[i,j]`. -/
def Witness (n : ℕ) (X Y V : List ℤ) (i k j : ℕ) : Prop :=
  entry n X i k + entry n Y k j < entry n V i j

/-- The pair `(i, j)` has a witness `k < n`. -/
def PairHit (n : ℕ) (X Y V : List ℤ) (i j : ℕ) : Prop := ∃ k < n, Witness n X Y V i k j

/-- The list `O` of `n²` marks is right as far as it goes: every entry is 0 or 1, and every pair
marked 1 has a witness. -/
structure Marks (n : ℕ) (X Y V O : List ℤ) : Prop where
  len : O.length = n * n
  sound : ∀ i < n, ∀ j < n, entry n O i j = 0 ∨ (entry n O i j = 1 ∧ PairHit n X Y V i j)

/-- The triple of blocks at the offsets `oI`, `oK`, `oJ` is done: every pair of the first and the
third block that has a witness in the middle block is marked. -/
def BlockDone (n s : ℕ) (X Y V O : List ℤ) (oI oK oJ : ℕ) : Prop :=
  ∀ a < s, ∀ b < s, ∀ c < s,
    Witness n X Y V (oI + a) (oK + b) (oJ + c) → entry n O (oI + a) (oJ + c) = 1

/-- The instance for a triple of blocks. -/
def blockTri (n s : ℕ) (F : ℤ) (X Y V O : List ℤ) (oI oK oJ : ℕ) : TriangleInstance ℤ s :=
  triOf s (subMat n s oI oK X) (subMat n s oK oJ Y)
    (maskNeg F (subMat n s oI oJ O) (subMat n s oI oJ V))

/-- The weight of a triangle of the instance for a triple of blocks. -/
theorem blockTri_S (n s : ℕ) (F : ℤ) (X Y V O : List ℤ) (oI oK oJ : ℕ) (a b c : Fin s) :
    (blockTri n s F X Y V O oI oK oJ).S a b c =
      entry n X (oI + a) (oK + b) + entry n Y (oK + b) (oJ + c) +
        if entry n O (oI + a) (oJ + c) = 1 then F else -entry n V (oI + a) (oJ + c) := by
  have h : a.val * s + c.val < s * s := Nat.mul_add_lt_mul a.2 c.2
  simp only [blockTri, TriangleInstance.S, triOf, entry_subMat a.2 b.2, entry_subMat b.2 c.2,
    getD_maskNeg (O := subMat n s oI oJ O) (V := subMat n s oI oJ V) (by simpa using h)
      (by simpa using h), entry_subMat a.2 c.2]

/-- If the instance of a triple of blocks has no negative triangle, then the triple is done. -/
theorem blockDone_of_not {n s : ℕ} {F : ℤ} {X Y V O : List ℤ} {oI oK oJ : ℕ}
    (h : ¬ (blockTri n s F X Y V O oI oK oJ).HasNegativeTriangle) :
    BlockDone n s X Y V O oI oK oJ := by
  intro a ha b hb c hc hlt
  by_contra hO
  refine h ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ?_⟩
  rw [blockTri_S, if_neg hO]
  exact Int.sub_neg_of_lt hlt

/-- A negative triangle of the instance of a triple of blocks is an unmarked pair with a
witness. -/
theorem unmarked_of_neg {n s : ℕ} {U : ℕ} {X Y V O : List ℤ} {oI oK oJ : ℕ}
    (hX : AbsLe X U) (hY : AbsLe Y U) {a b c : Fin s}
    (h : (blockTri n s (2 * U + 1) X Y V O oI oK oJ).S a b c < 0) :
    entry n O (oI + a) (oJ + c) ≠ 1 ∧ Witness n X Y V (oI + a) (oK + b) (oJ + c) := by
  have hx := abs_le.1 (abs_entry_le n (Int.natCast_nonneg U) hX (oI + a) (oK + b))
  have hy := abs_le.1 (abs_entry_le n (Int.natCast_nonneg U) hY (oK + b) (oJ + c))
  rw [blockTri_S] at h
  split_ifs at h with hO
  · -- a marked pair: `X + Y ≥ -2U` and `F = 2U + 1`, so the weight would be positive
    omega
  · -- an unmarked pair: the weight is `X + Y - V < 0`
    exact ⟨hO, by unfold Witness; omega⟩

/-- Marking a pair that has a witness keeps the marks right. -/
theorem Marks.set {n : ℕ} {X Y V O : List ℤ} (h : Marks n X Y V O) {i j : ℕ} (hi : i < n)
    (hj : j < n) (hit : PairHit n X Y V i j) : Marks n X Y V (O.set (i * n + j) 1) := by
  refine ⟨by simp [h.len], fun i' hi' j' hj' => ?_⟩
  rw [entry, List.getD_set_of_lt (h.len ▸ Nat.mul_add_lt_mul hi hj)]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := Nat.mul_add_inj_of_lt hj' hj e
    exact Or.inr ⟨rfl, hit⟩
  · exact h.sound i' hi' j' hj'

/-- Marking an unmarked pair makes the number of unmarked pairs smaller. -/
theorem count_set_one {O : List ℤ} {q : ℕ} (hq : q < O.length) (h0 : O.getD q 0 = 0) :
    (O.set q 1).count 0 + 1 = O.count 0 := by
  rw [List.getD_eq_getElem _ _ hq] at h0
  have hpos : 0 < O.count 0 := List.count_pos_iff.2 (h0 ▸ List.getElem_mem hq)
  rw [List.count_set hq, h0, if_pos (by decide), if_neg (by decide)]
  omega

/-- A triple of blocks that is done stays so when another pair is marked. -/
theorem BlockDone.set {n s : ℕ} {X Y V O : List ℤ} {oI oK oJ : ℕ}
    (h : BlockDone n s X Y V O oI oK oJ) {q : ℕ} (hq : q < O.length) :
    BlockDone n s X Y V (O.set q 1) oI oK oJ := by
  intro a ha b hb c hc hlt
  rw [entry, List.getD_set_of_lt hq]
  split_ifs
  · rfl
  · exact h a ha b hb c hc hlt

/-- **When all triples of blocks are done, the marks are the answer.** -/
theorem Marks.complete {n s : ℕ} {X Y V O : List ℤ} (h : Marks n X Y V O) (hs1 : 1 ≤ s)
    (hs : s ≤ n)
    (hdone : ∀ I < blockCount n s, ∀ K < blockCount n s, ∀ J < blockCount n s,
      BlockDone n s X Y V O (blockOff n s I) (blockOff n s K) (blockOff n s J))
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n O i j = flag (PairHit n X Y V i j) := by
  by_cases hit : PairHit n X Y V i j
  · rw [flag_of hit]
    obtain ⟨k, hk, hlt⟩ := hit
    obtain ⟨I, hI, a, ha, rfl⟩ := exists_block hs1 hs hi
    obtain ⟨K, hK, b, hb, rfl⟩ := exists_block hs1 hs hk
    obtain ⟨J, hJ, c, hc, rfl⟩ := exists_block hs1 hs hj
    exact hdone I hI K hK J hJ a ha b hb c hc hlt
  · rw [flag_of_not hit]
    exact (h.sound i hi j hj).resolve_right fun hmark => hit hmark.2

/-- At the beginning no pair is marked. -/
theorem marks_replicate (n : ℕ) (X Y V : List ℤ) : Marks n X Y V (List.replicate (n * n) 0) :=
  ⟨List.length_replicate, fun _ _ _ _ => Or.inl (by simp)⟩

end ThreeSumApsp.Spec
