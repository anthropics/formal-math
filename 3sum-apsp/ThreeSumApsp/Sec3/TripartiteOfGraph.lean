/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Section 3.2: from an arbitrary graph to a tripartite one

"an instance on an arbitrary n-vertex graph reduces to this form by taking three copies of the
vertex set and giving every missing edge the weight 3n^ν + 1, which lies in no zero triangle (this
replaces ν by ν + 1)".  The instance is `tripartiteOfGraph`.  A triangle with a missing edge does
not have weight zero (`not_isZeroTriangle_tripartiteOfGraph`), so the instance has a zero triangle
exactly if the graph has one (`hasZeroTriangle_tripartiteOfGraph_iff`).  Its weights are at most
`n^{ν+1}` in absolute value (`weightsBoundedBy_tripartiteOfGraph`; nothing else rests on this last
lemma).
-/

@[expose] public section

namespace ThreeSumApsp

open Classical in
/-- Section 3.2: "taking three copies of the vertex set and giving every
missing edge the weight 3n^ν + 1".  `U` stands for the bound `n^ν` on the weights of the given
graph. -/
noncomputable def tripartiteOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → Fin n → ℤ)
    (U : ℤ) : TriangleInstance ℤ n where
  wAB a b := if G.Adj a b then w a b else 3 * U + 1
  wBC b c := if G.Adj b c then w b c else 3 * U + 1
  wAC a c := if G.Adj a c then w a c else 3 * U + 1

/-- Section 3.2: "the weight 3n^ν + 1, which lies in no zero triangle". -/
theorem not_isZeroTriangle_tripartiteOfGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → Fin n → ℤ) (U : ℤ) (hw : ∀ u v, G.Adj u v → |w u v| ≤ U) (a b c : Fin n)
    (h : ¬ G.Adj a b ∨ ¬ G.Adj b c ∨ ¬ G.Adj a c) :
    ¬ (tripartiteOfGraph G w U).IsZeroTriangle a b c := by
  intro hz
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, tripartiteOfGraph] at hz
  -- An edge of the graph has a weight in `[-U, U]` and a missing edge the weight `3U + 1`, too
  -- large to be cancelled by the other two, whichever of the three edges are missing.  (If all
  -- three are missing, the sum is `9U + 3`, which is not zero for an integer `U`.)
  have hab : G.Adj a b → -U ≤ w a b ∧ w a b ≤ U := fun hadj => abs_le.mp (hw a b hadj)
  have hbc : G.Adj b c → -U ≤ w b c ∧ w b c ≤ U := fun hadj => abs_le.mp (hw b c hadj)
  have hac : G.Adj a c → -U ≤ w a c ∧ w a c ≤ U := fun hadj => abs_le.mp (hw a c hadj)
  by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj b c <;> by_cases h3 : G.Adj a c <;>
    simp only [h1, h2, h3, if_true, if_false, true_implies, false_implies, not_true_eq_false,
      not_false_eq_true, or_self, or_true, true_or] at h hz hab hbc hac <;>
    omega

/-- Section 3.2: "an instance on an arbitrary n-vertex graph reduces to this
form by taking three copies of the vertex set and giving every missing edge the weight 3n^ν + 1,
which lies in no zero triangle".

NOTE.  An integer `U`, a bound on the absolute values of the weights of the edges of `G`, stands for
the paper's `n^ν`, which need not be an integer. -/
theorem hasZeroTriangle_tripartiteOfGraph_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → Fin n → ℤ) (U : ℤ) (hw : ∀ u v, G.Adj u v → |w u v| ≤ U) :
    (tripartiteOfGraph G w U).HasZeroTriangle ↔ GraphHasZeroTriangle G w := by
  constructor
  · rintro ⟨a, b, c, h⟩
    -- None of the three edges is missing, so the weights are those of the graph.
    obtain ⟨hab, hbc, hac⟩ : G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
      by_contra hmissing
      exact not_isZeroTriangle_tripartiteOfGraph G w U hw a b c (by tauto) h
    simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, tripartiteOfGraph, hab, hbc,
      hac, if_true] at h
    exact ⟨a, b, c, hab, hbc, hac, h⟩
  · rintro ⟨u, v, x, huv, hvx, hux, h⟩
    refine ⟨u, v, x, ?_⟩
    simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, tripartiteOfGraph, huv, hvx,
      hux, if_true]
    exact h

/-- Section 3.2: "(this replaces ν by ν + 1)".

NOTE.  Stated for a natural number `κ`, so that `3n^κ + 1` is an integer, and for `n ≥ 4`: for
`n ≤ 3` the weight `3n^κ + 1` exceeds `n^{κ+1}`. -/
theorem weightsBoundedBy_tripartiteOfGraph {n κ : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (w : Fin n → Fin n → ℤ) (hw : ∀ u v, G.Adj u v → |w u v| ≤ (n : ℤ) ^ κ) :
    (tripartiteOfGraph G w ((n : ℤ) ^ κ)).WeightsBoundedBy ((n : ℤ) ^ (κ + 1)) := by
  have hn4 : (4 : ℤ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℤ) ≤ (n : ℤ) ^ κ := one_le_pow₀ (by linarith)
  have hbig : 4 * (n : ℤ) ^ κ ≤ (n : ℤ) ^ (κ + 1) := by
    rw [pow_succ, mul_comm]
    gcongr
  classical
  -- Both kinds of weight are at most `4n^κ ≤ n^(κ+1)` in absolute value.
  have habs : ∀ u v : Fin n,
      |if G.Adj u v then w u v else 3 * (n : ℤ) ^ κ + 1| ≤ (n : ℤ) ^ (κ + 1) := by
    intro u v
    split_ifs with h
    · exact (hw u v h).trans (by linarith)
    · rw [abs_of_nonneg (by linarith)]; linarith
  exact ⟨fun a b => habs a b, fun b c => habs b c, fun a c => habs a c⟩

end ThreeSumApsp
