/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Corollary39.Definitions
public import ThreeSumApsp.Util.List

/-!
# The weights of the graph H as sums over lists of pairs of parts (proof of Corollary 39)

The weight of an edge of the graph H (the proof of Corollary 39) is a sum of weights of the original
graph over a list of pairs of parts that depends only on k and on the part of H.  A program for a
fixed k can therefore add these weights up one after the other.  Vertices of H, and choices of the
fixed vertices, are numbers whose digits in base n, least significant first, are the vertices of the
original graph.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open ThreeSumApsp.KClique Finset

/-- The pairs of parts whose edges are counted in the weight of an edge of H between its parts i and
i + 1: the four contributions of the proof of Corollary 39, in the order of KClique.weightH. -/
def pairsH (k : ℕ) (i : Fin 3) : List (Fin k × Fin k) :=
  ((List.finRange (width k)).flatMap fun j => (List.finRange (width k)).map
    fun j' => (groupPart i j, groupPart (i + 1) j'))
  ++ ((List.finRange (width k)).flatMap fun j =>
      ((List.finRange (width k)).filter fun j' => j < j').map
        fun j' => (groupPart i j, groupPart i j'))
  ++ ((List.finRange (numFixed k)).flatMap fun a => (List.finRange (width k)).map
    fun j => (fixedPart a, groupPart i j))
  ++ (if i = 0 then
      (List.finRange (numFixed k)).flatMap fun a =>
        ((List.finRange (numFixed k)).filter fun a' => a < a').map
          fun a' => (fixedPart a, fixedPart a')
    else [])

/-- The total weight, over a list of pairs of parts, of the edges between the vertices that v
chooses in these parts. -/
def pairSum {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) (L : List (Fin k × Fin k)) : ℤ :=
  (L.map fun pq => G.w pq.1 (v pq.1) pq.2 (v pq.2)).sum

/-- The weight of an edge of H is the sum over the list of pairs. -/
theorem weightH_eq_pairSum {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) (i : Fin 3) :
    weightH G (fixedOf v) i (groupOf v i) (groupOf v (i + 1)) = pairSum G v (pairsH k i) := by
  unfold weightH pairSum pairsH
  simp only [List.map_append, List.sum_append, List.sum_flatMap_map, List.map_map,
    Function.comp_def]
  simp only [List.sum_filter_finRange, ← Fin.sum_univ_def, fixedOf, groupOf]
  congr 1
  split_ifs with h
  · simp only [List.sum_flatMap_map, List.map_map, Function.comp_def, List.sum_filter_finRange,
      ← Fin.sum_univ_def]
  · simp

/-- The vertex in part p of the clique that is given by four numbers: F for the fixed vertices and
a, b, c for the three groups of parts. -/
def vtx (k n F a b c p : ℕ) : ℕ :=
  if p < numFixed k then F / n ^ p % n
  else if p < numFixed k + width k then a / n ^ (p - numFixed k) % n
  else if p < numFixed k + 2 * width k then b / n ^ (p - numFixed k - width k) % n
  else c / n ^ (p - numFixed k - 2 * width k) % n

/-- The vertices are below n. -/
theorem vtx_lt {n : ℕ} (hn : 0 < n) (k F a b c p : ℕ) : vtx k n F a b c p < n := by
  unfold vtx
  split_ifs <;> exact Nat.mod_lt _ hn

/-- The clique given by four numbers. -/
def cliqueOf {n : ℕ} (hn : 0 < n) (k F a b c : ℕ) : Fin k → Fin n :=
  fun p => ⟨vtx k n F a b c p, vtx_lt hn k F a b c p⟩

/-- The fixed vertices of the clique are the digits of F. -/
theorem fixedOf_cliqueOf {n : ℕ} (hn : 0 < n) (k : ℕ) (F : Fin (n ^ numFixed k)) (a b c : ℕ) :
    fixedOf (cliqueOf hn k F a b c) = finFunctionFinEquiv.symm F := by
  funext x
  apply Fin.ext
  rw [finFunctionFinEquiv_symm_apply_val]
  have hx : ((fixedPart x : Fin k) : ℕ) = x := rfl
  have hx2 := x.2
  simp only [fixedOf, cliqueOf, vtx, hx, if_pos hx2]

/-- The vertex in part number j of a group of parts is the digit number j of the number that stands
for the group. -/
theorem vtx_groupPart (k n F a b c : ℕ) (i : Fin 3) (j : Fin (width k)) :
    vtx k n F a b c (groupPart i j : Fin k) = ![a, b, c] i / n ^ (j : ℕ) % n := by
  have hj := j.isLt
  fin_cases i <;> simp [vtx, groupPart] <;> grind

section

variable {n : ℕ} (hn : 0 < n) (k F : ℕ)

/-- The vertices of the clique in the first group of parts are the digits of a. -/
theorem groupOf_cliqueOf_zero (a : Fin (n ^ width k)) (b c : ℕ) :
    groupOf (cliqueOf hn k F a b c) 0 = finFunctionFinEquiv.symm a :=
  funext fun j => Fin.ext <|
    (vtx_groupPart k n F a b c 0 j).trans (finFunctionFinEquiv_symm_apply_val a j).symm

/-- The vertices of the clique in the second group of parts are the digits of b. -/
theorem groupOf_cliqueOf_one (a : ℕ) (b : Fin (n ^ width k)) (c : ℕ) :
    groupOf (cliqueOf hn k F a b c) 1 = finFunctionFinEquiv.symm b :=
  funext fun j => Fin.ext <|
    (vtx_groupPart k n F a b c 1 j).trans (finFunctionFinEquiv_symm_apply_val b j).symm

/-- The vertices of the clique in the third group of parts are the digits of c. -/
theorem groupOf_cliqueOf_two (a b : ℕ) (c : Fin (n ^ width k)) :
    groupOf (cliqueOf hn k F a b c) 2 = finFunctionFinEquiv.symm c :=
  funext fun j => Fin.ext <|
    (vtx_groupPart k n F a b c 2 j).trans (finFunctionFinEquiv_symm_apply_val c j).symm

end

/-- The three weight matrices of H, entry by entry, as sums over the lists of pairs. -/
theorem graphH_entries {k n : ℕ} (hn : 0 < n) (G : KPartiteGraph k n) (F : Fin (n ^ numFixed k))
    (a b c : Fin (n ^ width k)) :
    (graphH G (finFunctionFinEquiv.symm F)).wAB a b
        = pairSum G (cliqueOf hn k F a b 0) (pairsH k 0) ∧
      (graphH G (finFunctionFinEquiv.symm F)).wBC b c
        = pairSum G (cliqueOf hn k F 0 b c) (pairsH k 1) ∧
      (graphH G (finFunctionFinEquiv.symm F)).wAC a c
        = pairSum G (cliqueOf hn k F a 0 c) (pairsH k 2) := by
  simp only [← weightH_eq_pairSum, fixedOf_cliqueOf, Fin.isValue, Fin.reduceAdd,
    groupOf_cliqueOf_zero, groupOf_cliqueOf_one, groupOf_cliqueOf_two]
  exact ⟨rfl, rfl, rfl⟩

end ThreeSumApsp.Spec
