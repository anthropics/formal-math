/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.TopNet
public import FixedWidthVariableBoundStatement

/-! # From an algorithm for cliques to #k-SAT on n variables: definitions and interface statements

The Lean form of part (a) of the theorem of Appendix D. Given: a solver `S` for cliques
(`ClauseBound.Alg.Solver`) with a sequence of levels `Q : S.Seq e C₀`, and a function `slU` that
gives, for the level l, an integer s with 2^(−s) ≤ e_l and 2^s ≤ (2/e_l)^C. For n variables the
function picks the largest level l with K_l ≤ n^(1/17), sets s = s(l),
sparsifies with the threshold τ = 2^(4s+17) (walking the counting tree with `walkS`), and counts
every leaf by the networks of marks of `proof/rates/PaddedDescent/F/MarkNet.lean`,
each of which is rebalanced to K_l nodes and handed to the solver (`valS`). Here the code parameter
β is linear in s, with a slope that depends on the width k, so that a network
has O_k(n·s²) shared bits.
The exponent of the pad is computed from the input under the bound n; if it would be larger than n,
or if s is too small for the width k, or if 2^β > n + 1, the
function counts exhaustively. This file has definitions only. The statements `St…` are propositions. -/

@[expose] public section

namespace ClauseBound.TopN

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (MCtx markF markN adm nProf cls WfL occ nSat placeE)

/-! ### One sparse formula, for any way `val` to evaluate a network of marks -/

/-- One evaluation: the sum of `val` over the admissible profiles. gu is the number of nodes in
unary; p = (n, w, β, b) in unary, as for `PaddedDescent.F.evalF`. -/
def evalV (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml) : ℤ :=
  sumF (nProf gu.length (cls Ls).length Ls.length) pad fun y =>
    bif adm k gu.length p.1.length p.2.1.length Ls y then val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) else 0

/-! ### The parameters for width k and precision s -/

/-- The code parameter: 2^(betaN k s) is at least the number of clauses per variable of a leaf of
the sparsification tree for width k with the threshold 2^(4s+17). -/
def betaN (k s : ℕ) : ℕ := (4 * s + 17) * (2 ^ (k + 1) + 1) + k + 3

/-- The number of times that the set of clauses is divided into a layer and a rest. -/
def layersN (k s : ℕ) : ℕ := 2 * betaN k s + 4

/-- 2^β, cut off at n + 1. The function uses the networks only if 2^β ≤ n + 1, and then this is 2^β.
The cut-off keeps the number small enough to be written in unary. -/
def blockN (k n s : ℕ) : ℕ := min (2 ^ betaN k s) (n + 1)

/-- The bound on the number of shared bits of a network of marks on 3K⁸ nodes. -/
def UbN (k K n s : ℕ) : ℕ := Ub k (3 * K ^ 8) n (n + 2) (betaN k s) (layersN k s + 2)

/-- The bound on the size of a network of marks on 3K⁸ nodes. -/
def PbN (k K n s : ℕ) : ℕ := Pb (3 * K ^ 8) n (betaN k s) (blockN k n s)

/-- ⌊n^{1/17}⌋ in unary. -/
def root17 (n : ℕ) : U := List.replicate (((List.range (n + 1)).filter fun b => decide (b ^ 17 ≤ n)).length - 1) ()

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-! ### The exponent of the pad -/

/-- `needNet` computed under the bound b; `none` if the exponent of the solver is larger than the
bound. -/
def needNetC (b : U) (i : Idx) (Ub P B : ℕ) : Option ℕ :=
  (S.needC (b, i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) Ub P) (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ())).map fun v =>
    max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (P * (2 * (3 * S.K i ^ 8) / S.K i + 1))) (max ((S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) Ub P) v)

/-- The index of the level picked for the input x. -/
def idxN (k : ℕ) (pick : U → U × Idx) (x : List Bool) : Idx := (pick (root17 (nK k x))).2

/-- The precision picked for the input x. -/
def precN (k : ℕ) (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (slU (pick (root17 (nK k x))).1).length

end

/-! ### Budget.lean: what a pad of length 2^(restN …) suffices for -/

/-- The parameters are large enough for width k: clauses per variable, number of layers. -/
def StParN : Prop := ∀ k n s : ℕ, leafC (tauOf s) k + 2 ≤ 2 ^ betaN k s ∧
  (6 ≤ n → 2 ^ layersN k s * (2 ^ betaN k s * n) + 5 * 3 ^ layersN k s ≤ 3 ^ layersN k s * (n + 2))

/-! ### Walk.lean: the walk through the counting tree, for any way `val` to count a leaf -/

/-- If `val` is right on every node that has the properties of a leaf of the counting tree, and the
pad suffices for the rounds and for the stack, the walk returns the number of
satisfying assignments. -/
def StWalkCount : Prop := ∀ (k τ n : ℕ) (φ : Sat3.CNF n) (pad : U) (val : CNode → ℕ), 1 ≤ k → SatK.IsKCNF k φ → k ^ 2 ≤ τ →
  2 * (∑ j ∈ Finset.range (k * n / τ + 1), (bsum τ k * n).choose j) ≤ pad.length + 1 → stackLenC k τ n (inLen k n) ≤ pad.length →
  (∀ x : CNode, (leafF x).length ≤ (leafC τ k + 2) * n → (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → (∀ v, (occ x.1 v).length ≤ leafC τ k) →
    (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) → val x = cntN n (leafF x)) →
  (bif hasNil (decU k (SatK.enc k φ)).2 then 0 else walkS k pad τ val (rootC (decU k (SatK.enc k φ)))) = SatK.numSat φ

end ClauseBound.TopN
