/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Programs.Sec5.Corollary39.GraphH.FillMeaning
public import ThreeSumApsp.TimeClaims.Sec5.Definitions

/-!
# Corollary 39: the tasks

The problems of Corollary 39, with the calling convention of all tasks: deciding whether some
k-clique has total weight zero (`kcTask`), finding a triangle of maximum (minimum) weight, and
finding a k-clique of maximum (minimum) total weight.  The instances of the triangle problems are
those of finding a negative triangle; those of the last two problems are those of Zero-Weight
k-Clique with a place for the k vertices of the answer.

With these tasks the sentence "is solved in time T" can be read, for all problems of Corollary 39,
as a statement about programs of the light language (`lightModel5`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec5

open ThreeSumApsp.KClique ThreeSumApsp.Spec Light.Sec3

/-! ## Weight zero -/

/-- A complete k-partite graph in the memory. -/
structure KcInst (k : ℕ) : Type where
  n : ℕ
  U : ℕ
  g : ℕ
  G : KPartiteGraph k n

/-- The weights stand below the free pointer, in the blocks (p, q) with p < q of an array of k²
blocks, and are bounded by U. -/
structure KcInst.Pre {k : ℕ} (x : KcInst k) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  weights : WeightsAt μ x.g x.G
  le : ∀ (p q : Fin k) (u v : Fin x.n), p < q → |x.G.w p u q v| ≤ (x.U : ℤ)
  below : x.g + k * k * x.n * x.n ≤ fr

/-- **Zero-Weight k-Clique**: kc(n, U, g, fr) returns 1 if some k-clique has total weight zero, and
0 if not. -/
noncomputable def kcTask (k : ℕ) : Task where
  Inst := KcInst k
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.g]
  Pre := KcInst.Pre
  Post x μ fr r μ' := r = flag x.G.HasZeroClique ∧ Kept μ μ' fr

/-! ## Minimum and maximum weight -/

/-- **Max-Weight Triangle**: maxTri(n, U, ab, bc, ac, res, fr) writes the vertices a, b, c of a
triangle of maximum weight to the cells res, res + 1, res + 2. -/
def maxTriTask : Task where
  Inst := FindInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.res]
  Pre := FindInst.Pre
  Post x μ fr _ μ' :=
    (∃ a b c : Fin x.n, μ' x.res = a.val ∧ μ' (x.res + 1) = b.val ∧ μ' (x.res + 2) = c.val ∧
      IsMaxWeightTriangle (triOf x.n x.AB x.BC x.AC) a b c) ∧
    KeptBut μ μ' fr x.res 3

/-- **Min-Weight Triangle**: minTri(n, U, ab, bc, ac, res, fr) writes the vertices a, b, c of a
triangle of minimum weight to the cells res, res + 1, res + 2. -/
def minTriTask : Task where
  Inst := FindInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.res]
  Pre := FindInst.Pre
  Post x μ fr _ μ' :=
    (∃ a b c : Fin x.n, μ' x.res = a.val ∧ μ' (x.res + 1) = b.val ∧ μ' (x.res + 2) = c.val ∧
      IsMinWeightTriangle (triOf x.n x.AB x.BC x.AC) a b c) ∧
    KeptBut μ μ' fr x.res 3

/-- A complete k-partite graph in the memory, and the place for the k vertices of a clique. -/
structure KcFindInst (k : ℕ) : Type extends KcInst k where
  res : ℕ

/-- The place for the answer lies below the free pointer and does not meet the weights. -/
structure KcFindInst.Pre {k : ℕ} (x : KcFindInst k) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends KcInst.Pre x.toKcInst μ fr where
  belowRes : x.res + k ≤ fr
  apart : x.g + k * k * x.n * x.n ≤ x.res ∨ x.res + k ≤ x.g

/-- **Max-Weight k-Clique**: maxKc(n, U, g, res, fr) writes the vertices of a k-clique of maximum
total weight, the vertex in part p to the cell res + p. -/
def maxKcTask (k : ℕ) : Task where
  Inst := KcFindInst k
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.g, x.res]
  Pre := KcFindInst.Pre
  Post x μ fr _ μ' :=
    (∃ v : Fin k → Fin x.n, (∀ p : Fin k, μ' (x.res + p) = (v p).val) ∧ x.G.IsMaxWeightClique v) ∧
      KeptBut μ μ' fr x.res k

/-- **Min-Weight k-Clique**: minKc(n, U, g, res, fr) writes the vertices of a k-clique of minimum
total weight, the vertex in part p to the cell res + p. -/
def minKcTask (k : ℕ) : Task where
  Inst := KcFindInst k
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.g, x.res]
  Pre := KcFindInst.Pre
  Post x μ fr _ μ' :=
    (∃ v : Fin k → Fin x.n, (∀ p : Fin k, μ' (x.res + p) = (v p).val) ∧ x.G.IsMinWeightClique v) ∧
      KeptBut μ μ' fr x.res k

/-! ## Minimum and maximum at once

The host for k-Clique is one program with a flag mx, true for the maximum and false for the minimum.
-/

/-- The weight x is at least as good as the weight y. -/
def better : Bool → ℤ → ℤ → Prop
  | true, x, y => y ≤ x
  | false, x, y => x ≤ y

/-- Max-Weight Triangle (mx = true) or Min-Weight Triangle (mx = false). -/
def optTriTask (mx : Bool) : Task where
  Inst := FindInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.res]
  Pre := FindInst.Pre
  Post x μ fr _ μ' :=
    (∃ a b c : Fin x.n, μ' x.res = a.val ∧ μ' (x.res + 1) = b.val ∧ μ' (x.res + 2) = c.val ∧
      ∀ a' b' c', better mx ((triOf x.n x.AB x.BC x.AC).S a b c)
        ((triOf x.n x.AB x.BC x.AC).S a' b' c')) ∧
    KeptBut μ μ' fr x.res 3

/-- Max-Weight k-Clique (mx = true) or Min-Weight k-Clique (mx = false). -/
def optKcTask (mx : Bool) (k : ℕ) : Task where
  Inst := KcFindInst k
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.g, x.res]
  Pre := KcFindInst.Pre
  Post x μ fr _ μ' :=
    (∃ v : Fin k → Fin x.n, (∀ p : Fin k, μ' (x.res + p) = (v p).val) ∧
      ∀ v', better mx (x.G.cliqueWeight v) (x.G.cliqueWeight v')) ∧ KeptBut μ μ' fr x.res k

/-- With the flag true, `optTriTask` is Max-Weight Triangle. -/
theorem optTriTask_true : optTriTask true = maxTriTask := rfl

/-- With the flag false, `optTriTask` is Min-Weight Triangle. -/
theorem optTriTask_false : optTriTask false = minTriTask := rfl

/-- With the flag true, `optKcTask` is Max-Weight k-Clique. -/
theorem optKcTask_true (k : ℕ) : optKcTask true k = maxKcTask k := rfl

/-- With the flag false, `optKcTask` is Min-Weight k-Clique. -/
theorem optKcTask_false (k : ℕ) : optKcTask false k = minKcTask k := rfl

/-! ## The time model -/

/-- The reading of "is solved in time T" by programs of the light language, extended by the problems
of Corollary 39. -/
noncomputable def lightModel5 : DetTimeModel5 where
  toDetTimeModel := lightModel
  maxTriangle := SolvedIn maxTriTask
  minTriangle := SolvedIn minTriTask
  zeroClique k := SolvedIn (kcTask k)
  minClique k := SolvedIn (minKcTask k)
  maxClique k := SolvedIn (maxKcTask k)

end Light.Sec5
