/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Geo.Defs
public import WidthK.Top.Sat
import SparsificationLemma.Geo.Thr
import SparsificationLemma.Geo.Tau
import SparsificationLemma.Geo.Eps
import SparsificationLemma.Iface
import SparsificationLemma.Gen
import SparsificationLemma.Side
import UniformInK.Spars.Thresholds
import SparsifyWidthK.Thresholds
import SparsifyWidthK.Refine

/-! # Lemma 4 for a machine that walks the tree and tests every leaf

The machine of proof/consequences/WidthK/Top/Sat.lean decides k-SAT by a depth-first walk of a
sparsification tree. All it asks of the tree is the property `Sparsifies` defined there: few leaves,
few clauses in a leaf, ψ is
satisfied by an assignment exactly if some leaf is, and a small stack. This file proves `Sparsifies`
for the procedure `stepK (thetaU τ) k` with the thresholds θ 0 = 1, θ i = 4·τ^(2i−1), for every ε >
0 and a suitable τ
(`lemSparsification_walk_k`; for k = 3, `lemSparsification_walk`), and that no leaf has an empty
clause.
The walk tests at a leaf the formula ψ there, without the set 𝒩 of one-literal clauses that the
changed algorithm of Appendix C carries along. This is the
Sparsification Lemma in its original form: the formula is satisfiable exactly if one of the formulas
at the leaves is.
The proof applies `WidthK.ProgMain.sparsify_prog_of`
(proof/sparsification/SparsifyWidthK/ProgMain.lean), which holds for all thresholds and bounds that
satisfy `Iface`, to `stIfaceC`. The number of leaves is bounded as in
proof/sparsification/SparsificationLemma/Geo/Tau.lean; τ = ⌈(8k/ε')³⌉ for a rational ε' with 0 < ε'
< min(ε, 1) is large enough by `stTauE`. -/

public section

namespace SparsificationLemma.TreeWalk

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)

variable {k τ : ℕ}

/-- What the walk needs to know about the rule on finite sets, for the thresholds `thetaU τ` with 1
≤ k and 8k ≤ τ, and depth τ^(2k)·n. -/
theorem iface (hk : 1 ≤ k) (hτ : 8 * k ≤ τ) (n : ℕ) :
    Iface (thetaU τ) k (bsumU τ k * n) ((k - 1) * n) τ ((2 * ∑ j ∈ range k, thetaU τ j) * n) (ProgMain.Ok k n)
      (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU (thetaU τ) k τ F₀ F p t) :=
  stIfaceC k τ n (bsumU τ k * n) (thetaU τ) (betaSU τ) (stThrGeo k τ hk hτ) (Nat.mul_le_mul_right _ (stBetaSumU τ k (by omega)))

/-- `Sparsifies` for any τ ≥ 8k with (k/τ)·log₂(e·τ·τ^(2k)) ≤ ε. -/
theorem sparsifies_tau {ε : ℝ} (hk : 1 ≤ k) (hτ : 8 * k ≤ τ)
    (hε : ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ k : ℝ)) ≤ ε) :
    Sparsifies k ε (stepK (thetaU τ) k) rootP (bsumU τ k) (leafCU τ k) (2 ^ k) := by
  intro n ψ hψ
  have hT : (k - 1) * n < ((k - 1) * n / τ + 1) * τ := by
    calc (k - 1) * n < τ * ((k - 1) * n / τ + 1) := Nat.lt_mul_div_succ _ (by omega : 0 < τ)
      _ = ((k - 1) * n / τ + 1) * τ := Nat.mul_comm _ _
  obtain ⟨c1, c2, c3, c4⟩ := ProgMain.sparsify_prog_of (iface hk hτ n) (Refine.stRefines _ k (stThrGeo k τ hk hτ).pos) hT ψ (Gen.ok_of hψ)
    fun C hC => (hψ C hC).2
  refine ⟨?_, c2, c3, c4⟩
  have h1 : ∑ j ∈ range ((k - 1) * n / τ + 1), (bsumU τ k * n).choose j ≤ ∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j :=
    sum_le_sum_of_subset (range_mono (Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le k 1)))))
  calc ((leaves (stepK (thetaU τ) k) (bsumU τ k * n) (rootP ψ)).length : ℝ)
      ≤ ((∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j : ℕ) : ℝ) := by exact_mod_cast c1.trans h1
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := Thresholds.sum_choose_le_two_rpow (by omega) (le_bsumU (by omega)) hε n

/-- No leaf of the tree of a k-CNF has an empty clause. -/
theorem leaf_ne_nil (hk : 1 ≤ k) (hτ : 8 * k ≤ τ) {n : ℕ} {ψ : PFml} (hψ : IsKCNF k n ψ) (D : ℕ) :
    ∀ x ∈ leaves (stepK (thetaU τ) k) D (rootP ψ), ∀ C ∈ x, C ≠ [] := by
  intro x hx C hC
  have hI := iface hk hτ n
  have hR := Refine.stRefines _ k (stThrGeo k τ hk hτ).pos
  obtain ⟨p, t, hx'⟩ := exists_of_mem_leaves (ProgMain.G_step hI hR ψ) D (rootP ψ) 0 0
    ⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ (Gen.ok_of hψ)⟩ x hx
  obtain ⟨C', hC', -, hne⟩ := hx'.2.2.1 _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
  exact (List.toFinset_nonempty_iff C).1 (hne (hx'.2.1 C' hC').2.1)

/-- Lemma 4 for the walk, at every width k ≥ 1: for every ε > 0 there is a τ ≥ 8k for which the
procedure sparsifies width k with at most 2^(εn) leaves, each with at most 2·(θ 0 + … + θ (k−1))·n
clauses, none of them empty. -/
theorem lemSparsification_walk_k (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, 8 * k ≤ τ ∧ Sparsifies k ε (stepK (thetaU τ) k) rootP (bsumU τ k) (leafCU τ k) (2 ^ k) ∧
      ∀ (n : ℕ) (ψ : PFml), IsKCNF k n ψ → ∀ x ∈ leaves (stepK (thetaU τ) k) (bsumU τ k * n) (rootP ψ), ∀ C ∈ x, C ≠ [] := by
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have h0 : 0 < q := by exact_mod_cast hq0
  have h1 : q ≤ 1 := by exact_mod_cast (hq1.trans_le (min_le_right _ _)).le
  obtain ⟨a, b, -⟩ := stTauE k q hk h0 h1
  exact ⟨tauE k q, a, sparsifies_tau hk a (b.trans (hq1.trans_le (min_le_left _ _)).le), fun n ψ hψ => leaf_ne_nil hk a hψ _⟩

/-- Lemma 4 for the walk, at width 3. -/
theorem lemSparsification_walk {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, 24 ≤ τ ∧ Sparsifies 3 ε (stepK (thetaU τ) 3) rootP (bsumU τ 3) (leafCU τ 3) 8 ∧
      ∀ (n : ℕ) (ψ : PFml), IsKCNF 3 n ψ → ∀ x ∈ leaves (stepK (thetaU τ) 3) (bsumU τ 3 * n) (rootP ψ), ∀ C ∈ x, C ≠ [] :=
  lemSparsification_walk_k (le_of_lt (by norm_num : 1 < 3)) hε

end SparsificationLemma.TreeWalk
