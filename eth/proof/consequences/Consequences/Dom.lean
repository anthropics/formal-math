/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Consequences.Defs
import Consequences.Sets
import SplitCount.Sizes
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Cert
import GraphProblems.DomTree
import CountKSat.Walk
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Bounds for counting dominating sets (Corollary 7)

Three bounds on counts and sizes that belong to the proof of Corollary 7, in which the clauses are
shortened by a tree, Corollary 6 is applied at each leaf, and the counts are added up.
`cntS_le` bounds the number of satisfying assignments with s true variables by 2^n. `size_dnode_le`
bounds the size of a node of the tree of proof/consequences/GraphProblems/ that shortens the clauses
(`GraphProblems.stShortens`). `dom_size` bounds the sizes of the states of the walk over that tree
that adds up the counts at its leaves (`CountKSat.stWalkSum`). -/

public section

namespace Consequences

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper SplitCount

/-- There are at most 2^n satisfying assignments with s true variables. -/
theorem cntS_le (n s : ℕ) (ψ : Fml) : cntS n s ψ ≤ 2 ^ n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- A node of the tree that shortens the clauses, for s ≤ n, at most n neighborhood clauses of at
most n variables below n, and at most 2n further clauses of width at most w on variables below n,
has size at most (4w + 12)·(n + 2)^3. -/
theorem size_dnode_le {w n s : ℕ} {x : DNode} (hs : s ≤ n) (h1 : x.1 = (List.replicate n (), s)) (h2 : x.2.1.length ≤ n)
    (h3 : ∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) (h4 : x.2.2.length ≤ 2 * n) (h5 : Shaped w n x.2.2) :
    size x ≤ (4 * w + 12) * (n + 2) ^ 3 := by
  have s1 : size (List.replicate n ()) ≤ n * 2 + 1 := size_unary n
  have s2 : size s ≤ n + 2 :=
    size_nat_le (lt_of_le_of_lt hs (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))))
  have s3 : size x.2.1 ≤ n * (n * (n + 1 + 1) + 1 + 1) + 1 :=
    size_list_le h2 fun D hD => size_list_le (h3 D hD).1 fun u hu => size_nat_le (((h3 D hD).2 u hu).trans Nat.lt_two_pow_self)
  have s4 : size x.2.2 ≤ 2 * n * (w * (n + 2 + 1) + 1 + 1) + 1 := size_fml_le h4 h5
  have sx : size x = size (List.replicate n ()) + size s + (size x.2.1 + size x.2.2) := by
    rw [size_prod, size_prod, h1]
    rfl
  rw [sx]
  have e1 : n * (n * (n + 1 + 1) + 1 + 1) ≤ (n + 2) ^ 3 := by nlinarith
  have e2 : 2 * n * (w * (n + 2 + 1) + 1 + 1) ≤ (4 * w + 4) * (n + 2) ^ 3 := by
    have : (n + 2) ^ 2 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6 : 2 * n * (w * (n + 2 + 1) + 1 + 1) ≤ (4 * w + 4) * (n + 2) ^ 2 := by nlinarith
    exact h6.trans (Nat.mul_le_mul_left _ this)
  have e3 : n + 2 ≤ (n + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have e4 : (4 * w + 12) * (n + 2) ^ 3 = (4 * w + 4) * (n + 2) ^ 3 + 8 * (n + 2) ^ 3 := by ring
  omega

/-- The bound on the sizes of the states of the walk that `CountKSat.stWalkSum` gives, with X = n +
2 and K = 8w + 40 + c·4^c, is at most (K + c + 4)·X^(K + c + 4). -/
theorem dom_size {w c n X : ℕ} (hX : X = n + 2) :
    (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (X + (c * (4 * X) ^ c + 1)) + 1 ≤ (8 * w + 40 + c * 4 ^ c + c + 4) * X ^ (8 * w + 40 + c * 4 ^ c + c + 4) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 8 * w + 40 + c * 4 ^ c := ⟨_, rfl⟩
  rw [← hK]
  have hX1 : 1 ≤ X := by omega
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ (c + 4) := ⟨_, rfl⟩
  have hP1 : X ≤ P := by rw [hP]; exact Nat.le_self_pow (by omega) X
  have hP4 : X ^ 4 ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
  have hPc : X ^ c ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
  have a1 : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (8 * w + 26) * P := by
    have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
    calc (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (2 * X) * ((4 * w + 13) * X ^ 3) := by
          refine Nat.mul_le_mul (by omega) ?_
          have : (4 * w + 13) * X ^ 3 = (4 * w + 12) * X ^ 3 + X ^ 3 := by ring
          omega
      _ = (8 * w + 26) * X ^ 4 := by ring
      _ ≤ (8 * w + 26) * P := Nat.mul_le_mul_left _ hP4
  have a2 : c * (4 * X) ^ c ≤ c * 4 ^ c * P := by
    rw [mul_pow, ← mul_assoc]
    exact Nat.mul_le_mul_left _ hPc
  have total : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (X + (c * (4 * X) ^ c + 1)) + 1 ≤ K * P := by
    have eK : K * P = (8 * w + 26) * P + c * 4 ^ c * P + 14 * P := by rw [hK]; ring
    omega
  refine total.trans ?_
  rw [hP]
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hX1 (by omega))

end Consequences
