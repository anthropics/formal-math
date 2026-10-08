/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Corollary39.Definitions
public import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# Running-time claims for Corollary 39: the definitions

The record `DetTimeModel5` extends `DetTimeModel` by the problems of Section 5.3: maximum and
minimum weight triangles, and zero, minimum and maximum weight `k`-cliques. The claims (namespace
`Claim`) are propositions about an interpretation `M : DetTimeModel5`: the transfer claims that the
proof of Corollary 39 argues, one result that it cites ([VW13, Theorem 3.3]), and the two time
sentences of the corollary. The conventions are those of `DetTimeModel`. The word length is Θ(log of
the sum of the size parameters) bits, with a constant that may depend on `k`, because the triangle
instances have `n^⌊k/3⌋` vertices per part.

The transfer claims and the cited result are theorems for the reading by programs, `lightModel5`:
`claim_zeroCliqueFromExactTriangle`, `claim_maxCliqueFromMaxTriangle` and
`claim_minCliqueFromMinTriangle` for `k ≥ 3`, `claim_VW13_Theorem_3_3_max` and
`claim_minTriangleFromMax`.
-/

@[expose] public section

namespace ThreeSumApsp

/-- An interpretation of the sentences "is solved in time T" for the problems of Section 5.3, on top
of an interpretation for the problems of Sections 2 to 4. Each field is a predicate on running
times, with the intended meaning explained in `DetTimeModel`. Sizes (`n`, `s`, `k`) are exact; `u`
(numbers of absolute value at most `u`) is an upper bound. The algorithms are deterministic and
correct on every input. -/
structure DetTimeModel5 extends DetTimeModel where
  /-- Proof of Corollary 39: a deterministic algorithm finds a maximum weight triangle in a complete
  tripartite graph with `s` vertices per part and integer weights of absolute value at most `u`
  (`KClique.IsMaxWeightTriangle`). Arguments `s u`. -/
  maxTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Proof of Corollary 39: the same for a minimum weight triangle (`KClique.IsMinWeightTriangle`).
  Arguments `s u`. -/
  minTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Corollary 39: a deterministic algorithm decides whether a complete `k`-partite graph
  with parts of `n` vertices and integer edge weights of absolute value at most `u` has a `k`-clique
  of total weight zero (`KClique.KPartiteGraph.HasZeroClique`). The first argument is `k`; the
  arguments of the time are `n u`. -/
  zeroClique : ℕ → (ℕ → ℝ → ℝ) → Prop
  /-- Corollary 39: a deterministic algorithm finds a `k`-clique of minimum total weight
  (`KClique.KPartiteGraph.IsMinWeightClique`). -/
  minClique : ℕ → (ℕ → ℝ → ℝ) → Prop
  /-- Corollary 39: a deterministic algorithm finds a `k`-clique of maximum total weight
  (`KClique.KPartiteGraph.IsMaxWeightClique`). -/
  maxClique : ℕ → (ℕ → ℝ → ℝ) → Prop

namespace Claim

/-- Proof of Corollary 39, as a transfer claim from a triangle problem to a clique problem: "We
enumerate the n^t ways of fixing one vertex in each of the first t parts, and for each of them we
build H", a graph with N = n^⌊k/3⌋ vertices per part and weights of absolute value at most
(k choose 2) times the original bound, and solve the triangle problem on it. `triangle` and `clique`
say which running times solve the two problems. `C₀ N² (1 + log u)` allows for building H; the
constant may depend on `k`. The claim is meant for k ≥ 3. -/
def CliqueFromTriangle (triangle clique : (ℕ → ℝ → ℝ) → Prop) (k : ℕ) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℝ → ℝ, triangle T →
    clique fun n u =>
      (n : ℝ) ^ KClique.numFixed k * (T (n ^ (k / 3)) ((k.choose 2 : ℝ) * u) +
        C₀ * (((n ^ (k / 3) : ℕ) : ℝ) ^ 2 * (1 + logU u)))

/-- `CliqueFromTriangle` from Exact Triangle to Zero-Weight k-Clique. -/
def ZeroCliqueFromExactTriangle (M : DetTimeModel5) (k : ℕ) : Prop :=
  CliqueFromTriangle M.exactTriangle (M.zeroClique k) k

/-- `CliqueFromTriangle` from maximum weight triangles to Max-Weight k-Clique. -/
def MaxCliqueFromMaxTriangle (M : DetTimeModel5) (k : ℕ) : Prop :=
  CliqueFromTriangle M.maxTriangle (M.maxClique k) k

/-- `CliqueFromTriangle` from minimum weight triangles to Min-Weight k-Clique. -/
def MinCliqueFromMinTriangle (M : DetTimeModel5) (k : ℕ) : Prop :=
  CliqueFromTriangle M.minTriangle (M.minClique k) k

/-- CITED. [VW13, Theorem 3.3], as used in the proof of Corollary 39: "finding a maximum weight
triangle costs O(log² n) times as much" as deciding whether there is a triangle of weight zero. The
instances have weights O(U).

NOTE. The paper's factor log² n is read as (log U + log s + 1)²: log² U is the number of decisions
that give the weight of a maximum weight triangle, and a triangle of exactly that weight is then
found by O(log s) more decisions on instances with the same s, in which vertices are switched off by
a large weight. The term `s² (1 + log U)` allows for writing down an
instance. -/
def VW13_Theorem_3_3_max (M : DetTimeModel5) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ 0 ≤ C ∧ ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
    M.maxTriangle fun s U => C * ((T s (c * U) + (s : ℝ) ^ 2 * (1 + logU U)) *
      (logU U + Real.log s + 1) ^ 2)

/-- Proof of Corollary 39, as a transfer claim: "a minimum weight triangle is a maximum weight
triangle for the negated weights". -/
def MinTriangleFromMax (M : DetTimeModel5) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℝ → ℝ, M.maxTriangle T →
    M.minTriangle fun s U => T s U + C₀ * ((s : ℝ) ^ 2 * (1 + logU U))

/-- The exponent `k - ε_T⌊k/3⌋` of Corollary 39, with ε_T = 0.0017. -/
noncomputable abbrev cliqueExponent (k : ℕ) : ℝ :=
  (k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)

/-- **Corollary 39**, for one k: "Let k ≥ 3 and ν ≥ 1 be constants. Given a complete
k-partite graph with parts of n vertices and integer edge weights of absolute value at most n^ν,
deterministic algorithms decide in O(n^{k-ε_T⌊k/3⌋}) time whether some k-clique, with one vertex in
each part, has total edge weight zero". `κ` is the paper's ν. -/
def Corollary_39_zero (M : DetTimeModel5) (k : ℕ) : Prop :=
  ∀ κ : ℝ, 1 ≤ κ → ∃ T : ℕ → ℝ → ℝ, M.zeroClique k T ∧
    UpperBigOPow (fun n => T n ((n : ℝ) ^ κ)) (cliqueExponent k)

/-- **Corollary 39**, for one k: "and find a k-clique of minimum, or of maximum, total edge
weight", in the same time. -/
def Corollary_39_min_max (M : DetTimeModel5) (k : ℕ) : Prop :=
  ∀ κ : ℝ, 1 ≤ κ →
    (∃ T : ℕ → ℝ → ℝ, M.minClique k T ∧
      UpperBigOPow (fun n => T n ((n : ℝ) ^ κ)) (cliqueExponent k)) ∧
    (∃ T : ℕ → ℝ → ℝ, M.maxClique k T ∧
      UpperBigOPow (fun n => T n ((n : ℝ) ^ κ)) (cliqueExponent k))

end Claim

end ThreeSumApsp
