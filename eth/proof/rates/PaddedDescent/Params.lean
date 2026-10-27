/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Ring.Nat

/-! # The parameters of this folder's algorithm for 3-SAT (definitions only)

This file defines the numbers that the single algorithm for 3-SAT computes from the number of
variables `n`. It proves nothing beyond the two
defining equations of `kseq`. In the recursion of this folder one level takes K_j nodes to
(K_j·L_j)² nodes with a small factor L_j, where the paper's
recursion of Section 5 takes K nodes to g² = 9K¹⁶ nodes with g = 3K⁸. These numbers are also not
those of Theorem A in Appendix A. -/

@[expose] public section

namespace PaddedDescent

/-- The colouring of a network on g nodes with K colours is allowed the relative error 1/Dcol. -/
def Dcol : ℕ := 2 ^ 18

/-- The logarithm of the number of nodes at level `j`: k₀ = 8 and k_{j+1} = 2·(k_j + 47 + j). -/
def kseq : ℕ → ℕ
  | 0 => 8
  | j + 1 => 2 * (kseq j + 47 + j)

/-- k₀ = 8. -/
theorem kseq_zero : kseq 0 = 8 := by rw [kseq]

/-- k_{j+1} = 2·(k_j + 47 + j). -/
theorem kseq_succ (j : ℕ) : kseq (j + 1) = 2 * (kseq j + 47 + j) := by rw [kseq]

/- From here on Lean's tactics do not unfold the recursion by themselves; they use the two lemmas
above. This changes nothing in the
meaning. Without it, tactics that meet `kseq (19 * s / 3 + 700)` peel off 700 levels and run into
the recursion limit. -/
attribute [irreducible] kseq

/-- The number of nodes at level `j`: K_j = 2^(k_j), so K₀ = 256. -/
def Kseq (j : ℕ) : ℕ := 2 ^ kseq j

/-- The factor between the number of colours and the side of the grid at level `j`: L_j = 2^(47+j). -/
def Lseq (j : ℕ) : ℕ := 2 ^ (47 + j)

/-- The side of the grid at level `j`: g_j = K_j·L_j, so that K_{j+1} = g_j². -/
def gseq (j : ℕ) : ℕ := Kseq j * Lseq j

/-- The precision that the algorithm picks from the number of variables `n`: the exponent of the
time will be about n / 2^(sOf n).
(Subtraction of natural numbers stops at 0; the product with 3 is taken first, and then the division
by 19 rounds down.) -/
def sOf (n : ℕ) : ℕ := 3 * (Nat.log2 (Nat.log2 n) - 911) / 19

/-- The threshold of the sparsification for precision `s`. It does not depend on the width k of the
clauses: for every k it is large enough as soon as s is
large enough (`s0K k` below). -/
def tauOf (s : ℕ) : ℕ := 2 ^ (4 * s + 17)

/-- The marks of the clauses are coded in blocks of 2^(betaOf s) bits. The number 2^(betaOf s) is at
least the number of clauses per variable of a
sparsified formula of width k, as soon as s ≥ `s0K k`: that number is a power of τ whose exponent
depends on k only, and betaOf grows faster than any multiple of s. -/
def betaOf (s : ℕ) : ℕ := (s + 7) ^ 2

/-- The number of times that the set of clauses of a sparsified formula is divided into a layer and
a rest. -/
def layersOf (s : ℕ) : ℕ := 2 * betaOf s + 4

/-- The cap of the cut-off sums: an assignment that satisfies the later layers violates fewer than
capOf n clauses of a layer. -/
def capOf (n : ℕ) : ℕ := n + 2

/-- The number of levels for precision `s`: 19/3 levels for each unit of s (the division rounds
down), and 700 more. -/
def depthOf (s : ℕ) : ℕ := 19 * s / 3 + 700

/-- For clauses of width k the parameters above are large enough as soon as the precision s is at
least s0K k. For smaller s the machine uses exhaustive search. -/
def s0K (k : ℕ) : ℕ := 2 ^ (k + 4)

/-- The constant in the exponent of the length of the pad, 2^(C0K k·(⌊n/2^s⌋ + 1)), for width k. It
is so large that the pad suffices for exhaustive search while s < s0K k. -/
def C0K (k : ℕ) : ℕ := 8 * 2 ^ s0K k

/-- The number of nodes at the top level for precision `s`. -/
def Ktop (s : ℕ) : ℕ := Kseq (depthOf s)

/-- The number of nodes of the network of a formula, which is rebalanced to K_t nodes at the top:
3·K_t⁸. -/
def gtop (s : ℕ) : ℕ := 3 * Ktop s ^ 8

/-- Y = gtop². The overheads for precision `s` are bounded in terms of it
(`PaddedDescent.Threshold`). -/
def Ytop (s : ℕ) : ℕ := gtop s ^ 2

end PaddedDescent
