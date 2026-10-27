/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Complement.Defs
import GraphProblems.Read
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: «The cliques of size s are the independent sets of size s of the complement graph, and the vertex covers of size s are the complements of the independent sets of size n − s.»

* `stCliques`: the first half, for sets and for their numbers; it is Mathlib's
  `SimpleGraph.isNIndepSet_compl`.
* `stCovers`: the second half, for s ≤ n; from Mathlib's
  `SimpleGraph.isIndepSet_compl_iff_isVertexCover` and `Finset.card_compl`. The numbers agree
  because S ↦ Sᶜ is one-to-one.
* `stComplMatrix`: `complMatrix` turns the adjacency matrix of G into that of the complement graph. -/

public section

namespace Complement

open Groundwork Groundwork.Prog CountKSat GraphProblems

/-- «The cliques of size s are the independent sets of size s of the complement graph»: the same
sets, hence the same number. -/
theorem stCliques : StCliques := fun n G s => by
  have h : ∀ S : Finset (Fin n), G.IsNClique s S ↔ Gᶜ.IsNIndepSet s S := fun S => by rw [SimpleGraph.isNIndepSet_compl]
  refine ⟨h, ?_⟩
  unfold numCliques numIndepSets
  congr 1
  ext S
  exact h S

/-- «the vertex covers of size s are the complements of the independent sets of size n − s», for s ≤
n: S is a vertex cover of size s exactly if Sᶜ is an independent set of size n − s; hence the same
number. -/
theorem stCovers : StCovers := fun n G s hs => by
  have h : ∀ S : Finset (Fin n), (G.IsVertexCover (S : Set (Fin n)) ∧ S.card = s) ↔ G.IsNIndepSet (n - s) Sᶜ := fun S => by
    have h1 : S.card ≤ n := by simpa using S.card_le_univ
    rw [SimpleGraph.isNIndepSet_iff, Finset.coe_compl, SimpleGraph.isIndepSet_compl_iff_isVertexCover, Finset.card_compl, Fintype.card_fin]
    refine and_congr_right fun _ => ?_
    omega
  refine ⟨h, ?_⟩
  unfold numVertexCovers numIndepSets
  have e : {T : Finset (Fin n) | G.IsNIndepSet (n - s) T} = compl '' {S : Finset (Fin n) | G.IsVertexCover (S : Set (Fin n)) ∧ S.card = s} := by
    ext T
    constructor
    · intro hT
      exact ⟨Tᶜ, (h Tᶜ).2 (by rwa [compl_compl]), compl_compl T⟩
    · rintro ⟨S, hS, rfl⟩
      exact (h S).1 hS
  rw [e, Set.ncard_image_of_injective _ compl_injective]

/-- `pairs n` is the list of the pairs (u, v) of vertices u, v : Fin n, as numbers, with u in the
outer and v in the inner loop, both in increasing order. -/
theorem pairs_eq (n : ℕ) : pairs n = (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u.val, v.val) := by
  have hr : List.range n = (List.finRange n).map fun i : Fin n => i.val := List.map_coe_finRange_eq_range.symm
  change (List.range n).flatMap (fun a => (List.range n).map (Prod.mk a)) = _
  rw [hr, List.flatMap_map]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  rfl

/-- One entry: u ≠ v and the entry (u, v) of the matrix of G is 0, exactly if u and v are adjacent
in the complement graph. -/
theorem entry_compl {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (inst : Decidable (Gᶜ.Adj u v)) :
    (u.val != v.val && !adjB n (matrix G) u.val v.val) = @decide (Gᶜ.Adj u v) inst := by
  have h := stAdj n G u v
  by_cases huv : u = v
  · subst huv
    simp
  · have hne : u.val ≠ v.val := fun e => huv (Fin.ext e)
    by_cases hA : G.Adj u v
    · have h1 : adjB n (matrix G) u.val v.val = true := h.2 hA
      simp [h1, SimpleGraph.compl_adj, hA]
    · have h1 : adjB n (matrix G) u.val v.val = false := by
        rw [← Bool.not_eq_true]
        exact fun e => hA (h.1 e)
      simp [h1, SimpleGraph.compl_adj, hA, huv, hne]

/-- `complMatrix` turns the adjacency matrix of G into the adjacency matrix of the complement graph. -/
theorem stComplMatrix : StComplMatrix := fun n G => by
  obtain ⟨m, hm⟩ : ∃ m, m = matrix G := ⟨_, rfl⟩
  rw [← hm, complMatrix, pairs_eq, matrix, List.map_flatMap]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun v _ => ?_
  rw [hm]
  exact entry_compl G u v _

end Complement
