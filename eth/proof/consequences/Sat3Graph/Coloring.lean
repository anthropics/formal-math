/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import Sat3Graph.Split
import SplitSat.Leaf
import GraphProblems.Color
import GraphProblems.Read
import Mathlib.Tactic

/-! # Section 7, Corollary 7, «In particular»: deciding k-Coloring

Proof of `StColoring` of proof/consequences/Sat3Graph/Defs.lean. The k-CNF on kn variables of the
proof of Corollary 7 (in the paper: «a k-CNF on kn variables, which says that each vertex has
exactly one color and that the ends of each edge have different colors») has n clauses of k
literals; all its other clauses have 2 literals. Splitting the n long clauses takes (k − 3)·n new
variables, so the 3-CNF has at most (2k − 3)·n variables. It is satisfiable exactly if the k-CNF is,
that is if the number of proper colorings is not 0 (`GraphProblems.stColor`, a statement on
numbers), that is if the graph can be colored (`GraphProblems.stDecideColor`). -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SplitSat

/-- Clauses of at most 3 literals written behind a formula need no new variable. -/
theorem numFresh_append_le {x y : Fml} {m : ℕ} (hx : numFresh x ≤ m) (hy : ∀ C ∈ y, C.length ≤ 3) : numFresh (x ++ y) ≤ m := by
  rw [numFresh_append, numFresh_eq_zero hy]
  exact hx

/-- The formula of the colorings needs at most (k − 3)·n new variables. -/
theorem numFresh_colorF (k n : ℕ) (m : List Bool) : numFresh (colorF k n m) ≤ (k - 3) * n := by
  unfold colorF
  refine numFresh_append_le (numFresh_append_le ?_ ?_) ?_
  · refine (Eight.Width.numFresh_le k _ fun C hC => ?_).trans ?_
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hC
      simp
    · simp
  · intro C hC
    obtain ⟨v, -, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hC
    simp
  · intro C hC
    obtain ⟨p, -, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hC
    simp

/-- **`StColoring`.** For k ≥ 3 and every procedure D for 3-SAT with an exponent δ₃ ≥ 0 such that
δ₃·(2k − 3) ≤ δ, the machine `COLOR k D` says on the code of a graph G on n vertices, within
c'·2^{δn} steps and on states of size at most c'·(n+2)^{c'}, whether G can be colored with k colors. -/
theorem stColoring : StColoring := by
  intro k hk δ δ₃ _ h0 hle D c hD
  obtain ⟨c', hc'⟩ := exists_bounds (δ := δ) (2 * k - 3) c h0 (by rw [Nat.cast_sub (by omega)]; push_cast; exact hle)
  refine ⟨c', fun n G => ?_⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (colorF k n (matrix G)).dedup := ⟨_, rfl⟩
  have hvars : ∀ C ∈ φ, ∀ l ∈ C, l.1 < n * k := by
    intro C hC
    rw [hφ] at hC
    exact (stShapeColor k n _ C (List.mem_dedup.1 hC)).2
  have hfresh : numFresh φ ≤ (k - 3) * n := by
    rw [hφ]
    exact (numFresh_dedup_le _).trans (numFresh_colorF k n _)
  have hN : n * k + numFresh φ ≤ (2 * k - 3) * (n + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have e1 : 2 * (j + 3) - 3 = 2 * j + 3 := by omega
    have e2 : j + 3 - 3 = j := by omega
    rw [e2] at hfresh
    rw [e1]
    have e3 : (2 * j + 3) * (n + 1) = n * (j + 3) + j * n + (2 * j + 3) := by ring
    omega
  obtain ⟨h3, hnd, hsat⟩ := splitN_spec hvars
  obtain ⟨T, b, hr, hb, hTle⟩ := hD (n * k + numFresh φ) (splitN (n * k) φ) h3 hnd
  have hin : widthP (readC k (code G)) = (List.replicate (n * k + numFresh φ) (), splitN (n * k) φ) := by
    have e : readC k (code G) = (List.replicate (n * k) (), φ) := by
      rw [hφ]
      simp [readC, stRead1 n G]
    rw [e, widthP_replicate]
  obtain ⟨k1, k2⟩ := hc' n _ T hN hTle
  rw [← hin] at hr
  refine ⟨T, b, (Stepped.mapIn_runs (f := fun x => widthP (readC k x)) (a := code G) hr).mono le_rfl k1, ?_, k2⟩
  rw [hb, hsat, sat_iff_cntN hvars, hφ, cntN_of_dedup, stColor stAdj k n G]
  exact (stDecideColor k n G).symm

end Sat3Graph
