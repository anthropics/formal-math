/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Corollary39.Definitions

/-!
# Corollary 39: from weighted k-Clique to triangles

Corollary 39 decides Zero-Weight k-Clique, and finds a k-clique of minimum or maximum weight, in
`O(n^{k-ε_T⌊k/3⌋})` time, by the reduction of Nešetřil and Poljak.  Fix one vertex in each of the
first `t = k - 3⌊k/3⌋` parts, split the other parts into three groups of `⌊k/3⌋` parts, and let `H`
be the complete tripartite graph whose vertices are the choices of one vertex in each part of a
group.  Running times are not defined here; this file proves that the reduction is correct, in the
paper's order:
* the fixed parts and the three groups are all the `k` parts (`partEquiv`), so a `k`-clique is a
  choice of the fixed vertices and a triangle of `H` (`bijective_fixedOf_groupOf`);
* "every edge of a k-clique is counted exactly once over the three edges of its triangle"
  (`sum_pairs_eq_sum_edgeSum`), so a triangle and its `k`-clique have the same weight
  (`S_graphH_eq_cliqueWeight`);
* `(k choose 2) n^ν ≤ N^{2ν}` for `n ≥ k²` (`choose_mul_rpow_le`; nothing else rests on it);
* hence the answers agree: weight zero (`hasZeroClique_iff`), maximum (`isMaxWeightClique_iff`),
  minimum (`isMinWeightClique_iff`), where a minimum weight triangle is a maximum weight triangle
  for the negated weights (`isMinWeightTriangle_iff_negate`).
-/

@[expose] public section

namespace ThreeSumApsp.Corollary39

open Finset KClique

/-! ### The `k` parts -/

/-- The `k` parts, listed: the `t` fixed parts, then the parts of the three groups. -/
private def partEquiv (k : ℕ) : Fin (numFixed k) ⊕ (Fin 3 × Fin (width k)) ≃ Fin k :=
  ((Equiv.refl _).sumCongr finProdFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (three_width_add k)))

private theorem partEquiv_inl {k : ℕ} (a : Fin (numFixed k)) :
    partEquiv k (.inl a) = fixedPart a :=
  rfl

private theorem partEquiv_inr {k : ℕ} (i : Fin 3) (j : Fin (width k)) :
    partEquiv k (.inr (i, j)) = groupPart i j :=
  Fin.ext <| by
    change numFixed k + (j.1 + width k * i.1) = numFixed k + i.1 * width k + j.1
    rw [Nat.mul_comm]
    omega

/-- A sum over the `k` parts is a sum over the fixed parts plus a sum over the parts of the three
groups. -/
private theorem sum_parts {k : ℕ} (F : Fin k → ℤ) :
    ∑ p, F p = ∑ a, F (fixedPart a) + ∑ i, ∑ j, F (groupPart i j) := by
  rw [← (partEquiv k).sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [partEquiv_inl, partEquiv_inr]

/-- Proof of Corollary 39: "The triangles of H correspond bijectively to the k-cliques of the
original graph with one vertex in each part", and when k is not divisible by 3, "the triangles of H
correspond to the k-cliques through the t fixed vertices".  A k-clique is the same thing as a choice
of the t fixed vertices together with a triangle of H (one vertex of H in each part). -/
theorem bijective_fixedOf_groupOf (k n : ℕ) :
    Function.Bijective
      (fun v : Fin k → Fin n => ((fixedOf v, groupOf v) :
        (Fin (numFixed k) → Fin n) × (Fin 3 → Fin (width k) → Fin n))) := by
  constructor
  · intro v v' h
    funext p
    obtain ⟨a | ⟨i, j⟩, rfl⟩ := (partEquiv k).surjective p
    · exact congrFun (congrArg Prod.fst h) a
    · rw [partEquiv_inr]
      exact congrFun (congrFun (congrArg Prod.snd h) i) j
  · rintro ⟨f, g⟩
    refine ⟨fun p => Sum.elim f (fun ij => g ij.1 ij.2) ((partEquiv k).symm p),
      Prod.ext (funext fun a => ?_) (funext fun i => funext fun j => ?_)⟩
    · simp [fixedOf, ← partEquiv_inl]
    · simp [groupOf, ← partEquiv_inr]

/-! ### The order of the parts -/

/-- The order of the fixed parts is the order of their indices. -/
private theorem fixedPart_lt_fixedPart {k : ℕ} (a a' : Fin (numFixed k)) :
    fixedPart a < fixedPart a' ↔ a < a' :=
  Iff.rfl

/-- Every fixed part comes before every part of a group. -/
private theorem fixedPart_lt_groupPart {k : ℕ} (a : Fin (numFixed k)) (i : Fin 3)
    (j : Fin (width k)) : fixedPart a < groupPart i j := by
  have ha := a.2
  change (a : ℕ) < numFixed k + i.1 * width k + j.1
  omega

/-- The parts of the groups are ordered by group, and inside a group by their index. -/
private theorem groupPart_lt_groupPart {k : ℕ} (i i' : Fin 3) (j j' : Fin (width k)) :
    groupPart i j < groupPart i' j' ↔ i < i' ∨ (i = i' ∧ j < j') := by
  have hj := j.2
  have hj' := j'.2
  simp only [groupPart, Fin.lt_def, Fin.ext_iff]
  rcases Nat.lt_trichotomy i.1 i'.1 with h | h | h
  · have hmul : (i.1 + 1) * width k ≤ i'.1 * width k := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  · rw [h]
    omega
  · have hmul : (i'.1 + 1) * width k ≤ i.1 * width k := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

/-! ### A triangle and its `k`-clique have the same weight -/

/-- The sum of the four contributions to the weight of an edge of `H` from part `i` to part `i + 1`
(proof of Corollary 39), for a table `W` of the weights of the edges of a `k`-clique: `W p q` is the
weight of its edge between the parts `p` and `q`. -/
private def edgeSum {k : ℕ} (W : Fin k → Fin k → ℤ) (i : Fin 3) : ℤ :=
  (∑ j, ∑ j', W (groupPart i j) (groupPart (i + 1) j'))
  + (∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'), W (groupPart i j) (groupPart i j'))
  + (∑ a, ∑ j, W (fixedPart a) (groupPart i j))
  + (if i = 0 then ∑ a, ∑ a' ∈ univ.filter (fun a' => a < a'), W (fixedPart a) (fixedPart a')
    else 0)

/-- Proof of Corollary 39: "every edge of a k-clique is counted exactly once over the three edges of
its triangle".  Both sides are split into sums over the fixed parts and the three groups; the edges
between the groups 0 and 2 are counted from group 2. -/
private theorem sum_pairs_eq_sum_edgeSum {k : ℕ} (W : Fin k → Fin k → ℤ)
    (hW : ∀ p q, W p q = W q p) :
    ∑ p, ∑ q ∈ univ.filter (fun q => p < q), W p q = ∑ i, edgeSum W i := by
  have h02 : ∑ j, ∑ j', W (groupPart 0 j) (groupPart 2 j')
      = ∑ j, ∑ j', W (groupPart 2 j) (groupPart 0 j') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => hW _ _
  -- write `p < q` as a condition inside the sums
  simp only [Finset.sum_filter, edgeSum]
  -- split every sum over the parts, and decide the order of two parts
  simp only [sum_parts (k := k), fixedPart_lt_fixedPart,
    fixedPart_lt_groupPart, (fixedPart_lt_groupPart _ _ _).not_gt,
    groupPart_lt_groupPart, if_true, if_false, Finset.sum_const_zero, zero_add,
    Fin.sum_univ_three]
  -- decide `i < i'` for the nine pairs of groups
  simp (decide := true) only [true_and, false_and, or_false, false_or, if_true, if_false,
    Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib,
    show ((1 : Fin 3) + 1) = 2 from rfl, show ((2 : Fin 3) + 1) = 0 from rfl]
  -- what remains are the same terms, with the groups 0 and 2 exchanged
  rw [h02]
  ring

/-- The weight of the edge of `H` between the vertices that the `k`-clique `v` defines in the parts
`i` and `i + 1`, in terms of the table of the weights of the edges of `v`. -/
private theorem weightH_eq_edgeSum {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n)
    (i : Fin 3) :
    weightH G (fixedOf v) i (groupOf v i) (groupOf v (i + 1))
      = edgeSum (fun p q => G.w p (v p) q (v q)) i :=
  rfl

/-- Proof of Corollary 39: "We give H edge weights so that a triangle and its k-clique have the same
weight. ... In this way every edge of a k-clique is counted exactly once over the three edges of its
triangle, so there is no double-counting and the weights agree." -/
theorem S_graphH_eq_cliqueWeight {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) :
    (graphH G (fixedOf v)).S (finFunctionFinEquiv (groupOf v 0)) (finFunctionFinEquiv (groupOf v 1))
        (finFunctionFinEquiv (groupOf v 2)) = G.cliqueWeight v := by
  refine Eq.trans ?_ (sum_pairs_eq_sum_edgeSum _ fun p q => G.symm p (v p) q (v q)).symm
  simp only [TriangleInstance.S, graphH, Equiv.symm_apply_apply, Fin.sum_univ_three,
    ← weightH_eq_edgeSum]
  -- the edge between the parts C and A is the edge from part 2 to part 2 + 1 = 0
  rfl

/-! ### The size of the weights of `H` -/

/-- Proof of Corollary 39: "(k choose 2) n^ν ≤ N^{2ν} for n ≥ k²", because `(k choose 2) ≤ k² ≤ n`,
`n ≤ n^ν` for ν ≥ 1, and `n ≤ N`.  `κ` is the paper's ν. -/
theorem choose_mul_rpow_le {k n : ℕ} (hk : 3 ≤ k) {κ : ℝ} (hκ : 1 ≤ κ) (hkn : k ^ 2 ≤ n) :
    (k.choose 2 : ℝ) * (n : ℝ) ^ κ ≤ ((n ^ width k : ℕ) : ℝ) ^ (2 * κ) := by
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 ((Nat.one_le_pow _ _ (by omega)).trans hkn)
  have hwidth : width k ≠ 0 := by
    unfold width
    omega
  have hchoose : (k.choose 2 : ℝ) ≤ n := by
    refine Nat.cast_le.2 (le_trans ?_ hkn)
    rw [Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  calc (k.choose 2 : ℝ) * (n : ℝ) ^ κ ≤ (n : ℝ) ^ κ * (n : ℝ) ^ κ := by
        gcongr
        exact hchoose.trans (Real.self_le_rpow_of_one_le hn hκ)
    _ = (n : ℝ) ^ (2 * κ) := by rw [← Real.rpow_add (by linarith), two_mul]
    _ ≤ ((n ^ width k : ℕ) : ℝ) ^ (2 * κ) := by
        rw [Nat.cast_pow]
        exact Real.rpow_le_rpow (by linarith) (le_self_pow₀ hn hwidth) (by linarith)

/-! ### The answers agree -/

/-- Every triangle of every graph `H` is the triangle of a `k`-clique, which has the same weight. -/
private theorem exists_cliqueWeight_eq {k n : ℕ} (G : KPartiteGraph k n)
    (f : Fin (numFixed k) → Fin n) (a b c : Fin (n ^ width k)) :
    ∃ v : Fin k → Fin n, G.cliqueWeight v = (graphH G f).S a b c := by
  obtain ⟨v, hv⟩ := (bijective_fixedOf_groupOf k n).2
    (f, ![finFunctionFinEquiv.symm a, finFunctionFinEquiv.symm b, finFunctionFinEquiv.symm c])
  simp only [Prod.mk.injEq] at hv
  refine ⟨v, ?_⟩
  rw [← S_graphH_eq_cliqueWeight G v, hv.1, hv.2]
  simp

/-- Corollary 39, Zero-Weight k-Clique, correctness of the reduction: some k-clique has
total weight zero if and only if, for one of the n^t choices of the fixed vertices, H has a triangle
of weight zero. -/
theorem hasZeroClique_iff {k n : ℕ} (G : KPartiteGraph k n) :
    G.HasZeroClique ↔ ∃ f : Fin (numFixed k) → Fin n, (graphH G f).HasZeroTriangle := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨fixedOf v, _, _, _, (S_graphH_eq_cliqueWeight G v).trans hv⟩
  · rintro ⟨f, a, b, c, h⟩
    obtain ⟨v, hv⟩ := exists_cliqueWeight_eq G f a b c
    exact ⟨v, hv.trans h⟩

/-- Corollary 39, Max-Weight k-Clique, correctness of the reduction: a k-clique has maximum weight
if and only if no triangle of any of the n^t graphs H is heavier. -/
theorem isMaxWeightClique_iff {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) :
    G.IsMaxWeightClique v ↔ ∀ f a b c, (graphH G f).S a b c ≤ G.cliqueWeight v := by
  refine ⟨fun h f a b c => ?_, fun h v' => ?_⟩
  · obtain ⟨v', hv'⟩ := exists_cliqueWeight_eq G f a b c
    exact hv'.symm.trans_le (h v')
  · exact (S_graphH_eq_cliqueWeight G v').symm.trans_le (h _ _ _ _)

/-- Corollary 39, Min-Weight k-Clique, correctness of the reduction: a k-clique has minimum weight
if and only if no triangle of any of the n^t graphs H is lighter. -/
theorem isMinWeightClique_iff {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) :
    G.IsMinWeightClique v ↔ ∀ f a b c, G.cliqueWeight v ≤ (graphH G f).S a b c := by
  refine ⟨fun h f a b c => ?_, fun h v' => ?_⟩
  · obtain ⟨v', hv'⟩ := exists_cliqueWeight_eq G f a b c
    exact (h v').trans_eq hv'
  · exact (h _ _ _ _).trans_eq (S_graphH_eq_cliqueWeight G v')

/-- Proof of Corollary 39: "a minimum weight triangle is a maximum weight triangle for the negated
weights". -/
theorem isMinWeightTriangle_iff_negate {N : ℕ} (T : TriangleInstance ℤ N) (a b c : Fin N) :
    IsMinWeightTriangle T a b c ↔ IsMaxWeightTriangle (negate T) a b c := by
  have hS (a b c) : (negate T).S a b c = -T.S a b c := by
    simp only [TriangleInstance.S, negate]
    ring
  simp only [IsMinWeightTriangle, IsMaxWeightTriangle, hS, neg_le_neg_iff]

end ThreeSumApsp.Corollary39
