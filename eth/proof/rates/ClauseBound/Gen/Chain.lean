/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs
public import ClauseBound.Gen.PartA

/-! # The general recursion: the smaller total of one level

For pieces with parameters (ρ, c) (Definition 7) and a pattern, that is, a choice of one piece for
every rectangle of the grid, the two prices (the bits that the rectangles contribute to the total of
the row network and to that of the column network) add up to at most twice the number of rectangles
times the largest sum of the two caps of a piece (its numbers of bits row-wise and column-wise). So
on a g×g grid the cheaper of the row network and the column network costs at most the average of the
two,
which is at most g(g−1)gλ plus the number of rectangles times that largest sum, as in the bound on
the smaller total in the proofs of Proposition 3 and Theorem A. -/

public section

namespace ClauseBound.Gen.Chain

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Levels.Gen

/-- The sum of the two prices of a pattern is at most twice the number of rectangles times the
largest sum of the two caps of a piece. -/
theorem price_add_le (P : PiecesF) (p d h lam y : ℕ) (hc : 1 ≤ P.cnt h lam) :
    priceG P p d false h lam y + priceG P p d true h lam y ≤ 2 * (nRectG p d * capSum P h lam) := by
  unfold priceG
  rw [← Nat.mul_add, ← Finset.sum_add_distrib]
  refine Nat.mul_le_mul_left 2 ?_
  calc ∑ q ∈ Finset.range (nRectG p d), (P.cap false h lam (digit (P.cnt h lam - 1) y q) + P.cap true h lam (digit (P.cnt h lam - 1) y q))
      ≤ ∑ _q ∈ Finset.range (nRectG p d), capSum P h lam := by
        refine Finset.sum_le_sum fun q _ => ?_
        have hd : digit (P.cnt h lam - 1) y q ∈ Finset.range (P.cnt h lam) := by
          have := digit_le (P.cnt h lam - 1) y q
          rw [Finset.mem_range]; omega
        exact Finset.le_sup (f := fun i => P.cap false h lam i + P.cap true h lam i) hd
    _ = nRectG p d * capSum P h lam := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- On a square grid the cheaper of the two networks of a pattern costs at most the average. -/
theorem total_min_le (P : PiecesF) (g h lam y : ℕ) (hc : 1 ≤ P.cnt h lam) :
    totalG P g g (decide (totalG P g g true h lam y < totalG P g g false h lam y)) h lam y ≤
      g * (g - 1) * g * lam + nRectG g g * capSum P h lam := by
  have hs := price_add_le P g g h lam y hc
  have ht : totalG P g g true h lam y = g * (g - 1) * g * lam + priceG P g g true h lam y := by
    simp [totalG, nParts, nMemb]
  have hf : totalG P g g false h lam y = g * (g - 1) * g * lam + priceG P g g false h lam y := by
    simp [totalG, nParts, nMemb]
  by_cases hlt : totalG P g g true h lam y < totalG P g g false h lam y
  · rw [decide_eq_true hlt]; omega
  · rw [decide_eq_false hlt]; omega

end ClauseBound.Gen.Chain
