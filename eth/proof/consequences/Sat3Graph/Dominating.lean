/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import Sat3Graph.Ask
import SplitSat.Sizes
import GraphProblems.Sets
import GraphProblems.Read
import Mathlib.Tactic

/-! # Section 7, Corollary 7, «In particular, they decide … Dominating Set»

Proof of `StDominating` of proof/consequences/Sat3Graph/Defs.lean.

The machine `DOM w gates D` walks the tree of the proof of Corollary 7 that shortens the clauses to
w literals, and asks at each leaf (`askSized`). A leaf has at most 3n clauses of at most w literals
(`GraphProblems.ShortensD`), so `stAskSized` applies with B = 3·(w − 3), and a leaf costs at most
c₁·2^{(δ/2)n} steps. There are at most 2^{(δ/2)n} leaves. The machine `Stepped.walk` answers «yes»
exactly if some leaf does (`Stepped.walk_runs`); the numbers `cntS` of the leaves add up to that of
the formula for dominating sets (`GraphProblems.ShortensD`), which is the number of dominating sets
of size s (`GraphProblems.stDom`), and a sum of natural numbers is not 0 exactly if one of them is
not 0. -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat

/-- A sum of natural numbers is not 0 exactly if one of them is not 0. -/
theorem sum_ne_zero_iff {α : Type} (f : α → ℕ) : ∀ L : List α, (L.map f).sum ≠ 0 ↔ ∃ x ∈ L, f x ≠ 0
  | [] => by simp
  | x :: L => by
    have ih := sum_ne_zero_iff f L
    simp only [List.map_cons, List.sum_cons, List.mem_cons, exists_eq_or_imp]
    rw [← ih]
    omega

/-- The size of a node of the tree for Dominating Set: at most (4w + 12)·(n+2)³. -/
theorem size_dnode_le {w n s : ℕ} {x : DNode} (hs : s ≤ n) (h1 : x.1 = (List.replicate n (), s)) (h2 : x.2.1.length ≤ n)
    (h3 : ∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) (h4 : x.2.2.length ≤ 2 * n) (h5 : Shaped w n x.2.2) :
    size x ≤ (4 * w + 12) * (n + 2) ^ 3 := by
  have s1 := size_unary_le n
  have s2 : size s ≤ n + 2 := by
    have : s.size ≤ n + 1 := Nat.size_le.2 (lt_of_le_of_lt hs (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))))
    rw [size_nat]
    omega
  have s3 : size x.2.1 ≤ n * (n * (n + 1 + 1) + 1 + 1) + 1 :=
    size_list_le h2 fun D hD => size_list_le (h3 D hD).1 fun u hu => by
      have : u.size ≤ n := Nat.size_le.2 (((h3 D hD).2 u hu).trans Nat.lt_two_pow_self)
      rw [size_nat]
      omega
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

/-- **`StDominating`.** Let the tree for w have at most 2^{δn/2} leaves
(`GraphProblems.ShortensD w (δ/2)`) and let D decide 3-SAT with an exponent δ₃ ≥ 0 such that δ₃·(a +
1 + 3·(w − 3)) ≤ δ/2. Then `DOM w gates D` decides Dominating Set within c'·2^{δn} steps, on states
of size at most c'·(n+2)^{c'}. -/
theorem stDominating : StDominating := by
  intro gates a hT w δ δ₃ hδ h0 hsh hle D c hD
  obtain ⟨c₁, hA⟩ := stAskSized gates a hT w (3 * (w - 3)) (δ / 2) δ₃ (by positivity) h0 (by push_cast; exact hle) D c hD
  refine ⟨8 * w + c₁ + 34, fun n G s hs => ?_⟩
  obtain ⟨t1, t2, t3, t4⟩ := hsh n s (matrix G)
  obtain ⟨x0, hx0⟩ : ∃ x0 : List Unit × ℕ × List Bool, x0 = (List.replicate n (), s, matrix G) := ⟨_, rfl⟩
  rw [← hx0] at t1 t2 t3 t4
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepD w) (2 * n) (rootD x0) := ⟨_, rfl⟩
  rw [← hL] at t1 t2 t3
  have hleaf : ∀ x ∈ leaves (stepD w) (2 * n) (rootD x0), (Stepped.mapIn leafD (askSized gates D)).Runs x ⌊(c₁ : ℝ) * E⌋₊ (c₁ * X ^ c₁)
      (decide (cntS n s (leafD x).2.2 ≠ 0)) := by
    intro x hx
    rw [← hL] at hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    have hB : (w - 3) * (leafD x).2.2.length ≤ 3 * (w - 3) * (n + 1) := by
      generalize w - 3 = u
      calc u * (leafD x).2.2.length ≤ u * (3 * n) := Nat.mul_le_mul_left _ h3
        _ ≤ 3 * u * (n + 1) := by nlinarith [Nat.zero_le u]
    obtain ⟨T, b, hr, hb, hTle⟩ := hA n s (leafD x).2.2 hs h2 hB
    have e : leafD x = (List.replicate n (), s, (leafD x).2.2) := by simp [leafD, h1]
    have eb : decide (cntS n s (leafD x).2.2 ≠ 0) = b := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact hb.symm
    rw [eb]
    rw [← e] at hr
    exact (Stepped.mapIn_runs hr).mono (Nat.le_floor (hE ▸ hTle)) (le_of_eq (by rw [hX]))
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootD x0], [])).1 ≤ (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      exact hX ▸ size_dnode_le hs h1 h2 h3 h4 h5
  have wr := Stepped.walk_runs (stepD w) (root := rootD) (T := Stepped.mapIn leafD (askSized gates D)) (2 * n) x0
    (fun x hx => (t2 x (hL ▸ hx)).1) (fun x => decide (cntS n s (leafD x).2.2 ≠ 0)) ⌊(c₁ : ℝ) * E⌋₊ (c₁ * X ^ c₁) _ hleaf hstack
  rw [← hL] at wr
  have hread : read2 (codeWith G s) = x0 := by rw [stRead2 n G s, hx0]
  have wr' : (Stepped.walk (stepD w) rootD (Stepped.mapIn leafD (askSized gates D))).Runs (read2 (codeWith G s)) (L.length * (⌊(c₁ : ℝ) * E⌋₊ + 2))
      ((2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (1 + (c₁ * X ^ c₁ + 1)) + 1) (L.any fun x => decide (cntS n s (leafD x).2.2 ≠ 0)) := by
    rw [hread]
    exact wr
  refine ⟨_, _, (Stepped.mapIn_runs wr').mono le_rfl ?_, ?_, ?_⟩
  · -- sizes
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    obtain ⟨P, hP⟩ : ∃ P, P = X ^ (c₁ + 4) := ⟨_, rfl⟩
    have hP0 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ hX1
    have hP4 : X ^ 4 ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
    have hPc : X ^ c₁ ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
    have a1 : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (8 * w + 26) * P := by
      have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
      calc (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (2 * X) * ((4 * w + 13) * X ^ 3) := by
            refine Nat.mul_le_mul (by omega) ?_
            have : (4 * w + 13) * X ^ 3 = (4 * w + 12) * X ^ 3 + X ^ 3 := by ring
            omega
        _ = (8 * w + 26) * X ^ 4 := by ring
        _ ≤ (8 * w + 26) * P := Nat.mul_le_mul_left _ hP4
    have a2 : c₁ * X ^ c₁ ≤ c₁ * P := Nat.mul_le_mul_left _ hPc
    have total : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (1 + (c₁ * X ^ c₁ + 1)) + 1 ≤ (8 * w + c₁ + 34) * P := by
      have eK : (8 * w + c₁ + 34) * P = (8 * w + 26) * P + c₁ * P + 8 * P := by ring
      omega
    refine total.trans ?_
    rw [hP]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  · -- the answer
    rw [List.any_eq_true]
    simp only [decide_eq_true_eq]
    rw [← sum_ne_zero_iff (fun x => cntS n s (leafD x).2.2) L, ← t3, stDom n G s]
    exact (stDecide n G s hs).2.2.2.symm
  · -- steps
    have hfl : ((⌊(c₁ : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c₁ : ℝ) * E := Nat.floor_le (by positivity)
    have hLE : (L.length : ℝ) ≤ E := hE ▸ t1
    have hEE : E * E = (2 : ℝ) ^ (δ * n) := by
      rw [hE, ← Real.rpow_add two_pos]
      congr 1
      ring
    have hE0 : 0 ≤ E := by linarith
    push_cast
    calc (L.length : ℝ) * (((⌊(c₁ : ℝ) * E⌋₊ : ℕ) : ℝ) + 2)
        ≤ E * ((c₁ : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
      _ = ((c₁ : ℝ) + 2) * (E * E) := by ring
      _ = ((c₁ : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := by rw [hEE]
      _ ≤ (8 * (w : ℝ) + c₁ + 34) * (2 : ℝ) ^ (δ * n) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
        linarith

end Sat3Graph
