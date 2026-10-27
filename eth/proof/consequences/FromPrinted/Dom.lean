/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.GraphDefs
import FromPrinted.Sets
import Consequences.Dom
import SplitCount.Sizes
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Cert
import GraphProblems.DomTree
import CountKSat.Walk
import Mathlib.Tactic

/-! # Proof of Corollary 7 on the machines of proof/threesat/Printed/: dominating sets, with the machine named

«Choose w so large that the number of leaves is at most 2^{δn/2}, apply Corollary 6 to each leaf,
and add up.»
The machine at a leaf is `FromPrinted.Consequences.SIZED w ℓ τ` (`SIZED_counts`, with δ/2). The tree
is that of proof/consequences/GraphProblems/ (`GraphProblems.stShortens`); the walk that adds up is
`CountKSat.walkSum` (`CountKSat.stWalkSum`); the bounds on sizes, which name no machine, are
`Consequences.cntS_le`, `Consequences.size_dnode_le`, `Consequences.dom_size`. -/

public section

open Consequences SplitCount

namespace FromPrinted.Consequences

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper

/-- **Dominating sets of size s, with the machine named.** For every δ > 0 there are w, ℓ, τ, c such
that the tree that shortens the clauses to w literals has at most 2^{(δ/2)n} leaves
(`ShortensD w (δ/2)`), and `DOMcount w ℓ τ` has polynomial-time steps and returns, on the code of
(G, s), s ≤ n, the number of dominating sets of size s within c·2^{δn} steps, on states of size at
most c·(n+2)^c. -/
theorem stDominatingCounted : StDominatingCounted := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  -- «Choose w so large that the number of leaves is at most 2^{δn/2}»
  obtain ⟨w, -, hsh⟩ := stShortens (δ / 2) hδ2
  -- «apply Corollary 6 to each leaf»
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := SIZED_counts w hδ2
  refine ⟨w, ℓ, τ, 8 * w + 40 + c * 4 ^ c + c + 4, hsh, ?_, fun n G s hs => ?_⟩
  · have := IsPolyT.mapIn (M := SIZED w ℓ τ) stCertDom.2.2
    have := isPolyT_walkSum (T := Stepped.mapIn leafD (SIZED w ℓ τ)) (stCertDom.1 w) stCertDom.2.1
    exact ⟨IsPolyT.mapIn (M := walkSum (stepD w) rootD (Stepped.mapIn leafD (SIZED w ℓ τ))) stCertRead.2⟩
  obtain ⟨t1, t2, t3, t4⟩ := hsh n s (matrix G)
  obtain ⟨a, ha⟩ : ∃ a : List Unit × ℕ × List Bool, a = (List.replicate n (), s, matrix G) := ⟨_, rfl⟩
  rw [← ha] at t1 t2 t3 t4
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hleaf : ∀ x ∈ leaves (stepD w) (2 * n) (rootD a), (Stepped.mapIn leafD (SIZED w ℓ τ)).Runs x ⌊(c : ℝ) * E⌋₊ (c * (4 * X) ^ c) (cntS n s (leafD x).2.2) := by
    intro x hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    obtain ⟨T, hr, hTle⟩ := hc n s (leafD x).2.2 hs h2
    have e : leafD x = (List.replicate n (), s, (leafD x).2.2) := by simp [leafD, h1]
    rw [← e] at hr
    exact (Stepped.mapIn_runs hr).mono (Nat.le_floor (hE ▸ hTle)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c))
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootD a], [])).1 ≤ (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      exact hX ▸ size_dnode_le hs h1 h2 h3 h4 h5
  have hlt : ((leaves (stepD w) (2 * n) (rootD a)).map fun x => cntS n s (leafD x).2.2).sum < 2 ^ (n + 1) := by
    rw [← t3]
    exact lt_of_le_of_lt (cntS_le _ _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  -- «and add up»
  have wr := stWalkSum _ _ (stepD w) rootD (Stepped.mapIn leafD (SIZED w ℓ τ)) (2 * n) a (fun x hx => (t2 x hx).1)
    (fun x => cntS n s (leafD x).2.2) ⌊(c : ℝ) * E⌋₊ (c * (4 * X) ^ c) _ (n + 1) hleaf hstack hlt
  rw [← t3, stDom n G s] at wr
  have hread : read2 (codeWith G s) = a := by rw [stRead2 n G s, ha]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) (2 * n) (rootD a)).length := ⟨_, rfl⟩
  rw [← hL] at wr t1
  rw [← hread] at wr
  refine ⟨_, (Stepped.mapIn_runs wr).mono le_rfl (by rw [← hX]; exact dom_size hX), ?_⟩
  have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
  have hLE : (L : ℝ) ≤ E := hE ▸ t1
  have hEE : E * E = (2 : ℝ) ^ (δ * n) := by
    rw [hE, ← Real.rpow_add two_pos]
    congr 1
    ring
  have hE0 : 0 ≤ E := by linarith
  have hcK : (c : ℝ) + 2 ≤ ((8 * w + 40 + c * 4 ^ c + c + 4 : ℕ) : ℝ) := by
    have : c + 2 ≤ 8 * w + 40 + c * 4 ^ c + c + 4 := by omega
    exact_mod_cast this
  calc ((L * (⌊(c : ℝ) * E⌋₊ + 2) : ℕ) : ℝ) = (L : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) := by push_cast; ring
    _ ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
    _ = ((c : ℝ) + 2) * (E * E) := by ring
    _ = ((c : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := by rw [hEE]
    _ ≤ ((8 * w + 40 + c * 4 ^ c + c + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hcK (by positivity)

end FromPrinted.Consequences
