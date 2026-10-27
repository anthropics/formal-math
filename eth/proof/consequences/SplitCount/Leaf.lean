/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import SplitCount.Sizes
import SplitCount.Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Proof of Corollary 6: one leaf, and the stack
`leaf_runs` (the width reduction of the proof of Corollary 6, `stStepThree`, then a procedure D that
counts for 3-CNFs): at a leaf with at most Bl·n clauses of at most max(k, 2) literals on x₀ … xₙ₋₁,
this returns the number of satisfying assignments of the leaf on n variables, within A·2^{(δ/3)n}
steps if δ'·(1 + 3(max(k,3) − 3))·(Bl + 1) ≤ δ/3:
«The constants in O(n) depend on k and ε, so choosing ε = δ/3 first and then applying Theorem 2 with
a small enough value in place of δ gives time O(2^{δn}).»
`stack_size`: the stack of the walk has size polynomial in a number M that bounds n and the number
of clauses of the input. -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ

/-- The constant in the bound on the states of D at a leaf. -/
def leafConst (k Bl : ℕ) : ℕ :=
  (1 + (max k 3 - 3) * Bl) + (1 + 3 * (max k 3 - 3)) * Bl * (3 * (1 + (max k 3 - 3) * Bl) + 11) + 2

/-- The size of the input of D at a leaf: from n₃ ≤ n + q·m, m₃ ≤ m + 3q·m, m ≤ Bl·n and n ≤ M. -/
theorem leaf_size {q Bl n M m n₃ : ℕ} {Ψ₃ : Fml} (hn : n ≤ M) (h1 : 1 ≤ M) (hm : m ≤ Bl * n) (g1 : ∀ C ∈ Ψ₃, C.length ≤ 3) (g2 : Below n₃ Ψ₃)
    (g4 : n₃ ≤ n + q * m) (g5 : Ψ₃.length ≤ m + 3 * (q * m)) :
    n₃ + size Ψ₃ + 1 ≤ ((1 + q * Bl) + (1 + 3 * q) * Bl * (3 * (1 + q * Bl) + 11) + 2) * M ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a = 1 + q * Bl := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (1 + 3 * q) * Bl := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hmM : m ≤ Bl * M := hm.trans (Nat.mul_le_mul_left _ hn)
  have hqm : q * m ≤ q * (Bl * M) := Nat.mul_le_mul_left _ hmM
  have e1 : n₃ ≤ a * M := by
    have : a * M = M + q * (Bl * M) := by rw [ha]; ring
    omega
  have e2 : Ψ₃.length ≤ b * M := by
    have : b * M = Bl * M + 3 * (q * (Bl * M)) := by rw [hb]; ring
    omega
  have e3 : 3 * (n₃ + 2 + 1) + 1 + 1 ≤ (3 * a + 11) * M := by
    have : (3 * a + 11) * M = 3 * (a * M) + 11 * M := by ring
    omega
  have e4 : size Ψ₃ ≤ b * M * ((3 * a + 11) * M) + 1 :=
    (size_fml_le (k := 3) e2 fun C hC => ⟨g1 C hC, g2 C hC⟩).trans (Nat.succ_le_succ (Nat.mul_le_mul_left _ e3))
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have h1M2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ h1
  have e5 : a * M ≤ a * M ^ 2 := Nat.mul_le_mul_left _ hM2
  have e6 : b * M * ((3 * a + 11) * M) = b * (3 * a + 11) * M ^ 2 := by ring
  have e7 : (a + b * (3 * a + 11) + 2) * M ^ 2 = a * M ^ 2 + b * (3 * a + 11) * M ^ 2 + 2 * M ^ 2 := by ring
  omega

/-- **One leaf.** Let D count for 3-CNFs (proof of Corollary 6, first sentence) with exponent δ' ≥ 0
and constant A, let δ'·(1 + 3(max(k,3) − 3))·(Bl + 1) ≤ δ/3, and let the node x carry n in unary and
have at most Bl·n clauses
of at most max(k, 2) literals on x₀ … xₙ₋₁. Then the width reduction followed by D returns its
number of satisfying assignments on n variables within ⌊A·2^{(δ/3)n}⌋ steps, on states of size ≤
A·(`leafConst k Bl`·M²)^A, for all M ≥ 1 with n ≤ M. -/
theorem leaf_runs {k Bl A : ℕ} {D : StepMachine (List Unit × Fml) ℕ} {δ δ' : ℝ} (hδ' : 0 ≤ δ')
    (hδB : δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3) (hD : CountsThree D δ' A) {n M : ℕ} (hn : n ≤ M) (h1 : 1 ≤ M) {x : NNode}
    (hx1 : x.1 = List.replicate n ()) (hxl : (leafF x.2).length ≤ Bl * n) (hxc : ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) :
    (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)).Runs x ⌊(A : ℝ) * (2 : ℝ) ^ (δ / 3 * n)⌋₊ (A * (leafConst k Bl * M ^ 2) ^ A) (cntN n (leafF x.2)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = leafF x.2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = max k 3 := ⟨_, rfl⟩
  rw [← hΨ] at hxl hxc ⊢
  have hw3 : 3 ≤ w := hw ▸ le_max_right _ _
  have hkw : max k 2 ≤ w := by rw [hw]; omega
  -- the width reduction («Second, …» in the proof of Corollary 6)
  obtain ⟨g1, g2, -, g4, g5, g6⟩ := stStepThree w n Ψ (fun C hC => (hxc C hC).1.trans hkw) fun C hC => (hxc C hC).2
  obtain ⟨p, hp⟩ : ∃ p, p = widthP (List.replicate n (), Ψ) := ⟨_, rfl⟩
  rw [← hp] at g1 g2 g4 g5 g6
  have hp2 : (List.replicate p.1.length (), p.2) = p := by rw [hp]; simp [widthP]
  -- counting for the 3-CNF (the first sentence of the proof of Corollary 6)
  obtain ⟨T, r, hT⟩ := hD p.1.length p.2 g1 g2
  rw [hp2, g6] at r
  have hx : widthP (leafPlain x) = p := by rw [hp, leafPlain, hx1, hΨ]
  refine (Stepped.mapIn_runs (Stepped.mapIn_runs (by rw [hx]; exact r))).mono (Nat.le_floor (hT.trans ?_)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ A))
  · -- «with a small enough value in place of δ»
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (Nat.cast_nonneg A)
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((w - 3 : ℕ) : ℝ) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := hq ▸ Nat.cast_nonneg _
    have c1 : ((max k 3 : ℕ) : ℝ) - 3 = q := by rw [hq, ← hw, Nat.cast_sub hw3]; norm_num
    rw [c1] at hδB
    have c2 : (p.2.length : ℝ) ≤ (Ψ.length : ℝ) + 3 * (q * (Ψ.length : ℝ)) := by rw [hq]; exact_mod_cast g5
    have c3 : (Ψ.length : ℝ) ≤ (Bl : ℝ) * n := by exact_mod_cast hxl
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have c4 : (Ψ.length : ℝ) ≤ ((Bl : ℝ) + 1) * n := by linarith
    have c5 : (1 + 3 * q) * (Ψ.length : ℝ) ≤ (1 + 3 * q) * (((Bl : ℝ) + 1) * n) := mul_le_mul_of_nonneg_left c4 (by positivity)
    calc δ' * (p.2.length : ℝ) ≤ δ' * ((1 + 3 * q) * (((Bl : ℝ) + 1) * n)) := mul_le_mul_of_nonneg_left (by linarith) hδ'
      _ = δ' * ((1 + 3 * q) * ((Bl : ℝ) + 1)) * n := by ring
      _ ≤ δ / 3 * n := mul_le_mul_of_nonneg_right hδB hn0
  · rw [leafConst, ← hw]
    exact leaf_size hn h1 hxl g1 g2 g4 g5

/-- The constant in the bound on the size of the stack. -/
def stackConst (k Dd Sk : ℕ) : ℕ := (Dd + 1) * (4 * (Sk * (4 * max k 2 + 2)) + 6) + 1

/-- A clause of at most w literals on variables below n ≤ M: the bound of `size_fml_le` for one
clause is at most (4w + 2)·M. -/
theorem clause_bound {w n M : ℕ} (hn : n ≤ M) (h1 : 1 ≤ M) : w * (n + 2 + 1) + 1 + 1 ≤ (4 * w + 2) * M := by
  have a1 : w * (n + 2 + 1) ≤ w * (4 * M) := Nat.mul_le_mul_left _ (by omega)
  have a2 : (4 * w + 2) * M = w * (4 * M) + 2 * M := by ring
  omega

/-- **The stack.** A stack of at most Dd·n + 1 nodes, each of which carries n in unary and has at
most (m + n)·Sk clauses of at most max(k, 2) literals on x₀ … xₙ₋₁, has size at most
`stackConst k Dd Sk`·M³, for every M ≥ 1 with n ≤ M and m ≤ M. -/
theorem stack_size {k Dd Sk n m M : ℕ} {st : List NNode} (hn : n ≤ M) (hm : m ≤ M) (h1 : 1 ≤ M) (s1 : st.length ≤ Dd * n + 1)
    (s2 : ∀ x ∈ st, x.1 = List.replicate n () ∧ (leafF x.2).length ≤ (m + n) * Sk ∧ ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) :
    size st ≤ stackConst k Dd Sk * M ^ 3 := by
  obtain ⟨w, hw⟩ : ∃ w, w = max k 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * w + 2 := ⟨_, rfl⟩
  rw [stackConst, ← hw, ← hQ]
  rw [← hw] at s2
  have hq : w * (n + 2 + 1) + 1 + 1 ≤ Q * M := hQ ▸ clause_bound hn h1
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have h1M2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ h1
  have h1M3 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ h1
  have hf : ∀ x ∈ st, size x ≤ (4 * (Sk * Q) + 5) * M ^ 2 := by
    intro x hx
    obtain ⟨x1, x2, x3⟩ := s2 x hx
    have b1 : size x.1 ≤ n * 2 + 1 := x1 ▸ size_unary n
    have b2 := size_node_le x2 x3
    have b3 : (m + n) * Sk * (w * (n + 2 + 1) + 1 + 1) ≤ 2 * (Sk * Q) * M ^ 2 := by
      calc (m + n) * Sk * (w * (n + 2 + 1) + 1 + 1) ≤ (2 * M) * Sk * (Q * M) := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hq
        _ = 2 * (Sk * Q) * M ^ 2 := by ring
    have e2 : (4 * (Sk * Q) + 5) * M ^ 2 = 2 * (2 * (Sk * Q) * M ^ 2) + 5 * M ^ 2 := by ring
    rw [size_prod]
    omega
  refine (size_list_le s1 hf).trans ?_
  have hp : Dd * n + 1 ≤ (Dd + 1) * M := by
    have a1 : Dd * n ≤ Dd * M := Nat.mul_le_mul_left _ hn
    have a3 : (Dd + 1) * M = Dd * M + M := by ring
    omega
  have hp2 : (4 * (Sk * Q) + 5) * M ^ 2 + 1 ≤ (4 * (Sk * Q) + 6) * M ^ 2 := by
    have a3 : (4 * (Sk * Q) + 6) * M ^ 2 = (4 * (Sk * Q) + 5) * M ^ 2 + M ^ 2 := by ring
    omega
  calc (Dd * n + 1) * ((4 * (Sk * Q) + 5) * M ^ 2 + 1) + 1 ≤ (Dd + 1) * M * ((4 * (Sk * Q) + 6) * M ^ 2) + 1 := Nat.succ_le_succ (Nat.mul_le_mul hp hp2)
    _ = (Dd + 1) * (4 * (Sk * Q) + 6) * M ^ 3 + 1 := by ring
    _ ≤ (Dd + 1) * (4 * (Sk * Q) + 6) * M ^ 3 + M ^ 3 := Nat.add_le_add_left h1M3 _
    _ = ((Dd + 1) * (4 * (Sk * Q) + 6) + 1) * M ^ 3 := by ring

end SplitCount
