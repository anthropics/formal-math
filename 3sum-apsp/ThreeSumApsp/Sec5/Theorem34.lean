/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Asymptotics.Powers

/-!
# Theorem 34: directed unweighted APSP

By Theorem 33 it is enough to compute the (min,+)-product of an `n × n^μ` matrix by an `n^μ × n`
matrix, with entries of absolute value `Õ(n^{1-μ})`, in `O(n^{2+μ-ε₁})` time.  Running times are not
defined here; this file checks the steps of the paper's proof, in which `ε' = 0.00175` is the
constant of Theorems 19 and 22:
* the product consists of the products of the blocks of `n^μ` rows with the blocks of `n^μ` columns
  (`theorem_34_blocks`);
* their entries are small enough for Theorem 22, since `μ ≥ 1/2` (`theorem_34_entries`);
* the `n^{2-2μ}` products cost `Õ(n^{2+μ-με'/3})` in all (`theorem_34_total`), which is
  `O(n^{2+μ-ε₁})` for every `ε₁ < με'/3` (`theorem_34_absorb`).
-/

public section

namespace ThreeSumApsp

open Finset Asymptotics Filter

/-- Proof of Theorem 34: "Cut the n × n^μ matrix into n^{1-μ} blocks of n^μ
consecutive rows, and the n^μ × n matrix into n^{1-μ} blocks of n^μ consecutive columns.  The
(min,+)-product then consists of n^{2-2μ} products of two n^μ × n^μ matrices, one for each pair of
blocks."  Here m = n^μ and b = n^{1-μ}, so that n = b * m. -/
theorem theorem_34_blocks {b m : ℕ} (A : Matrix (Fin (b * m)) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin (b * m)) ℤ) (C : Matrix (Fin (b * m)) (Fin (b * m)) ℤ) :
    IsMinPlusProduct A B C ↔
      ∀ p q : Fin b,
        IsMinPlusProduct (blockOfRows A p) (blockOfCols B q)
          (fun i j => C (finProdFinEquiv (p, i)) (finProdFinEquiv (q, j))) := by
  refine ⟨fun h p q i j => h _ _, fun h i j => ?_⟩
  -- every row is row `i'` of some block `p`, and every column is column `j'` of some block `q`
  obtain ⟨⟨p, i'⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨q, j'⟩, rfl⟩ := finProdFinEquiv.surjective j
  exact h p q i' j'

/-- Proof of Theorem 34: "Their entries have absolute value Õ(n^{1-μ}) ≤ Õ(n^μ), because μ ≥ 1/2".
Stated is the inequality between the two powers, which is what `μ ≥ 1/2` gives; the logarithmic
factors are the same on both sides.  How Theorem 22 is applied to entries of this size is said at
the library's lemma `conditional_theorem_34`. -/
theorem theorem_34_entries (n μ : ℝ) (hn : 1 ≤ n) (hμ : 1 / 2 ≤ μ) : n ^ (1 - μ) ≤ n ^ μ :=
  Real.rpow_le_rpow_of_exponent_le hn (by linarith)

/-- Proof of Theorem 34: "Theorem 22 computes each of them in Õ((n^μ)^{3-ε'/3}) time, and
all of them in Õ(n^{2+μ-με'/3}) time", with ε' = 0.00175. -/
theorem theorem_34_total (n μ : ℝ) (hn : 0 < n) :
    n ^ (2 - 2 * μ) * (n ^ μ) ^ (3 - 0.00175 / 3 : ℝ) = n ^ (2 + μ - μ * 0.00175 / 3) := by
  rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
  congr 1
  ring

/-- Proof of Theorem 34: "This is O(n^{2+μ-ε₁}) for any constant ε₁ < με'/3". -/
theorem theorem_34_absorb (μ ε₁ : ℝ) (hε₁ : ε₁ < μ * 0.00175 / 3) (c : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ (2 + μ - μ * 0.00175 / 3) * Real.log n ^ c) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 + μ - ε₁)) :=
  isBigO_rpow_mul_log_pow_rpow (by linarith) c

end ThreeSumApsp
