/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Corollary 39: the graph `H` of the reduction from k-Clique to triangles

The objects of the proof of Corollary 39.  The first `t = k - 3⌊k/3⌋` parts are the fixed parts
(`numFixed`, `fixedPart`), and the others form three groups of `⌊k/3⌋` consecutive parts (`width`,
`groupPart`).  A `k`-clique splits into its fixed vertices and its vertices in the three groups
(`fixedOf`, `groupOf`).  For a choice of the fixed vertices, `graphH` is the complete tripartite
graph on the choices of one vertex in each part of a group, with the edge weights `weightH`.  Last
come maximum and minimum weight triangles and the negated weights. -/

@[expose] public section

namespace ThreeSumApsp.KClique

open Finset

/-- Corollary 39: "a complete k-partite graph with parts of n vertices and integer edge
weights". `w p u q v` is the weight of the edge between vertex `u` of part `p` and vertex `v` of
part `q`.  The graph is undirected, which is the field `symm`.  The values `w p u p v` (no such edge
exists) are never used. -/
structure KPartiteGraph (k n : ℕ) : Type where
  /-- The edge weights. -/
  w : Fin k → Fin n → Fin k → Fin n → ℤ
  /-- The graph is undirected. -/
  symm : ∀ p u q v, w p u q v = w q v p u

/-- Corollary 39: a "k-clique, with one vertex in each part" is a choice `v : Fin k → Fin n` of a
vertex in each part; its "total edge weight" is the sum of the weights of its (k choose 2) edges. -/
def KPartiteGraph.cliqueWeight {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) : ℤ :=
  ∑ p : Fin k, ∑ q ∈ univ.filter (fun q : Fin k => p < q), G.w p (v p) q (v q)

/-- Corollary 39: "some k-clique ... has total edge weight zero". -/
def KPartiteGraph.HasZeroClique {k n : ℕ} (G : KPartiteGraph k n) : Prop :=
  ∃ v, G.cliqueWeight v = 0

/-- Corollary 39: "a k-clique of minimum ... total edge weight". -/
def KPartiteGraph.IsMinWeightClique {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) : Prop :=
  ∀ v', G.cliqueWeight v ≤ G.cliqueWeight v'

/-- Corollary 39: "a k-clique of ... maximum, total edge weight". -/
def KPartiteGraph.IsMaxWeightClique {k n : ℕ} (G : KPartiteGraph k n) (v : Fin k → Fin n) : Prop :=
  ∀ v', G.cliqueWeight v' ≤ G.cliqueWeight v

/-- Proof of Corollary 39.  ⌊k/3⌋, the number of parts in each of the three groups. -/
def width (k : ℕ) : ℕ := k / 3

/-- Proof of Corollary 39: "let t := k - 3⌊k/3⌋ ∈ {1, 2}" (and t = 0 when k is divisible by 3): the
number of fixed vertices. -/
def numFixed (k : ℕ) : ℕ := k - 3 * (k / 3)

/-- Proof of Corollary 39: "t := k - 3⌊k/3⌋ ∈ {1, 2}" when k is not divisible by 3: t is the
remainder of k modulo 3. -/
theorem numFixed_eq_mod (k : ℕ) : numFixed k = k % 3 := by
  unfold numFixed
  omega

/-- The t fixed parts and the three groups of ⌊k/3⌋ parts are all the k parts. -/
theorem three_width_add (k : ℕ) : numFixed k + 3 * width k = k := by
  unfold numFixed width
  omega

/-- Proof of Corollary 39: "fixing one vertex in each of the first t parts".  The `a`-th of the
first t parts. -/
def fixedPart {k : ℕ} (a : Fin (numFixed k)) : Fin k := Fin.castLE (Nat.sub_le k (3 * (k / 3))) a

/-- Proof of Corollary 39.  The number of the `j`-th part of group `i` (see `groupPart`) is less
than k. -/
theorem groupPart_lt {k : ℕ} (i : Fin 3) (j : Fin (width k)) :
    numFixed k + i.1 * width k + j.1 < k := by
  have hi := i.2
  have hj := j.2
  have hmul : i.1 * width k ≤ 2 * width k := Nat.mul_le_mul_right _ (by omega)
  unfold numFixed width at *
  omega

/-- Proof of Corollary 39: "Split the k parts into three groups of k/3 parts each", applied to "the
remaining 3⌊k/3⌋ parts".  The paper does not say which parts form a group; we take consecutive
parts. `groupPart i j` is the `j`-th part of group `i`. The paper's groups 1, 2, 3 are `i = 0, 1,
2`. -/
def groupPart {k : ℕ} (i : Fin 3) (j : Fin (width k)) : Fin k :=
  ⟨numFixed k + i.1 * width k + j.1, groupPart_lt i j⟩

/-- Proof of Corollary 39.  The fixed vertices of a k-clique: its vertices in the first t parts. -/
def fixedOf {k n : ℕ} (v : Fin k → Fin n) : Fin (numFixed k) → Fin n := fun a => v (fixedPart a)

/-- Proof of Corollary 39.  The vertices of a k-clique in the parts of group `i`: the "vertices in
the ith part ... are the k/3-cliques of the original graph with one vertex in each part of the ith
group". -/
def groupOf {k n : ℕ} (v : Fin k → Fin n) (i : Fin 3) : Fin (width k) → Fin n :=
  fun j => v (groupPart i j)

/-- Proof of Corollary 39: "Let U be a vertex of H in part i and V a vertex in part i+1.  The weight
of the edge UV of H is the total weight of the edges of the original graph between a vertex of U and
a vertex of V, of the edges inside U, of the edges between U and the fixed vertices, and, if i = 1
and t = 2, of the edge between the two fixed vertices." The four lines below are these four
contributions.  The parts of H are indexed by ℤ₃, so `i + 1` is taken modulo 3; the paper's i = 1 is
`i = 0` here.  The last line sums over the pairs of fixed vertices: there is one pair when t = 2 and
none when t ≤ 1. `f` is the choice of the fixed vertices. -/
def weightH {k n : ℕ} (G : KPartiteGraph k n) (f : Fin (numFixed k) → Fin n) (i : Fin 3)
    (U V : Fin (width k) → Fin n) : ℤ :=
  (∑ j, ∑ j', G.w (groupPart i j) (U j) (groupPart (i + 1) j') (V j'))
  + (∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'),
      G.w (groupPart i j) (U j) (groupPart i j') (U j'))
  + (∑ a, ∑ j, G.w (fixedPart a) (f a) (groupPart i j) (U j))
  + (if i = 0 then
      ∑ a, ∑ a' ∈ univ.filter (fun a' => a < a'), G.w (fixedPart a) (f a) (fixedPart a') (f a')
    else 0)

/-- Proof of Corollary 39: the graph H, "the complete tripartite graph with" N := n^⌊k/3⌋ "vertices
per part", for the choice `f` of the fixed vertices, as an instance of Exact Triangle.  Vertex
number `finFunctionFinEquiv U` of a part is the tuple `U`. The parts A, B, C of the instance are the
parts 1, 2, 3 of H; the edge between C and A goes from part 3 to part 3 + 1 = 1. -/
def graphH {k n : ℕ} (G : KPartiteGraph k n) (f : Fin (numFixed k) → Fin n) :
    TriangleInstance ℤ (n ^ width k) where
  wAB a b := weightH G f 0 (finFunctionFinEquiv.symm a) (finFunctionFinEquiv.symm b)
  wBC b c := weightH G f 1 (finFunctionFinEquiv.symm b) (finFunctionFinEquiv.symm c)
  wAC a c := weightH G f 2 (finFunctionFinEquiv.symm c) (finFunctionFinEquiv.symm a)

/-- Proof of Corollary 39: a "maximum weight triangle". -/
def IsMaxWeightTriangle {N : ℕ} (T : TriangleInstance ℤ N) (a b c : Fin N) : Prop :=
  ∀ a' b' c', T.S a' b' c' ≤ T.S a b c

/-- Proof of Corollary 39: a "minimum weight triangle". -/
def IsMinWeightTriangle {N : ℕ} (T : TriangleInstance ℤ N) (a b c : Fin N) : Prop :=
  ∀ a' b' c', T.S a b c ≤ T.S a' b' c'

/-- Proof of Corollary 39: "the negated weights". -/
def negate {N : ℕ} (T : TriangleInstance ℤ N) : TriangleInstance ℤ N where
  wAB a b := -T.wAB a b
  wBC b c := -T.wBC b c
  wAC a c := -T.wAC a c

end ThreeSumApsp.KClique
