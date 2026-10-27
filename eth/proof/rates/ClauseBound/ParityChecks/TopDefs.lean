/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs
public import FixedWidthVariableBoundStatement

/-! # From a clique solver to #k-SAT on n variables, along Appendix D: the function, the exponent of the pad, and the interface lemmas

As in proof/rates/ClauseBound/TopN/Defs.lean (level picked for n^{1/17}, precision s, sparsification
with the threshold 2^{4s+17}, walk through the counting tree), but a leaf is counted by `countOL`.
Two constants have no
explicit value and are parameters: c (the networks are used only if Δ ≤ (⌊log₂ n⌋ + 1)^c) and n₀
(and only if n ≥ n₀). -/

@[expose] public section

namespace ClauseBound.ParityChecks

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The count of the formula of a node of the counting tree, by `countOL`, with the bound Δ =
2^(betaN k s) on the number of clauses in which one variable occurs. -/
def valO (k : ℕ) (pad : U) (i : Idx) (n s : ℕ) (x : CNode) : ℕ :=
  countOL S k pad i n (blockN k n s) (parQ n (blockN k n s) (leafM x).length) (leafM x)

/-- The number of satisfying assignments of the formula written in p.1, by the walk through the
counting tree. -/
def numOL (k : ℕ) (i : Idx) (s : ℕ) (p : List Bool × U) : ℕ :=
  bif hasNil (decU k p.1).2 then 0 else walkS k p.2 (tauOf s) (valO S k p.2 i (nK k p.1) s) (rootC (decU k p.1))

/-- The exponent of a pad that suffices for everything but the networks: the list of profiles, the
lists of the checks, the rounds of the walk, the stack of the walk. -/
def restO (k K n s : ℕ) : ℕ :=
  3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (blockN k n s) * (7 * n + 1)) + (3 * Nat.size (blockN k n s * n) + 3 * Nat.size n + 12) + (n / 2 ^ s + 2) +
    (betaN k s + 5 * k + 10 + (k + 3) * Nat.size n)

/-- The exponent of a pad that suffices for n variables at the index i with precision s. -/
def needO (k : ℕ) (i : Idx) (n s : ℕ) : ℕ :=
  needNet S i (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s)) 0 + restO k (S.K i) n s

/-- The exponent `needO`, if the networks can be used and the exponent is at most n; otherwise
`none`: exhaustive counting is used. -/
def planAtO (c n₀ k n : ℕ) (i : Idx) (s : ℕ) : Option ℕ :=
  if s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n then
    (needNetC S (List.replicate n ()) i (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s)) 0).bind fun v =>
      if v + restO k (S.K i) n s ≤ n then some (v + restO k (S.K i) n s) else none
  else none

/-- The plan for the input x. -/
def planO (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U) (x : List Bool) : Option ℕ :=
  planAtO S c n₀ k (nK k x) (idxN k pick x) (precN k pick slU x)

/-- THE exponent function: the exponent of the plan, or n. -/
def eO (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (planO S c n₀ k pick slU x).getD (nK k x)

/-- THE function: the number of satisfying assignments of the formula written in p.1, in n + 1 bits,
when the pad p.2 is long enough. -/
def AO (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U) (p : List Bool × U) : List Bool :=
  outW (decU k p.1, bif (planO S c n₀ k pick slU p.1).isNone then bruteN k p else numOL S k (idxN k pick p.1) (precN k pick slU p.1) p)

end

/-! ### BudgetOL.lean -/

/-- The budgets other than those of the networks. -/
def StBudgetO : Prop := ∀ k K n s F : ℕ, 1 ≤ k → s0K k ≤ s → 2 ^ restO k K n s ≤ F →
  nProf (3 * K ^ 8) (blkOL (blockN k n s) * (7 * n + 1)) 3 ≤ F ∧
  8 * (6 * n + 1) * (blockN k n s * n + 1) * (Nat.size (blockN k n s * n) + 2) + 8 ≤ F ∧
  2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j) ≤ F + 1 ∧ stackLenC k (tauOf s) n (inLen k n) ≤ F

/-! ### TopOL.lean: correctness, for the n₀ that belongs to c -/

def StCorrectO : Prop := ∀ c : ℕ, ∃ n₀ : ℕ, ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eO S c n₀ k Q.pick slU (SatK.enc k φ) ≤ pad.length →
  AO S c n₀ k Q.pick slU (SatK.enc k φ, pad) = SatK.binary n (SatK.numSat φ)

/-! ### CertTopOL.lean -/

def StCertO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U), PolyT pick → PolyT slU →
  PolyT (AO S c n₀ k pick slU) ∧ PolyT (eO S c n₀ k pick slU)

/-! ### ArithOL.lean: the exponent is O_k(e·n·(s+1)) -/

/-- For a suitable c, and every n₀: with l the level picked for n and s = s(l), the exponent of the
pad is at most A·n·e_l·(s+1). -/
def StArithO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C k : ℕ), 1 ≤ k →
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∃ c : ℕ, ∀ n₀ : ℕ, ∃ A : ℕ, ∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n →
    ((planAtO S c n₀ k n (Q.pick (root17 n)).2 (slU (Q.pick (root17 n)).1).length).getD n : ℝ) ≤
      A * n * e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ)

/-! ### EndOL.lean -/

/-- The end theorem for the bound in n, along Appendix D, for a solver with a sequence of levels. r
is any function that dominates e_l·(s(l)+1) at the level picked for n and is not too small. -/
def StEndO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ), PolyT slU →
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (k : ℕ) (r : ℕ → ℝ) (c₁ : ℕ), 1 ≤ k → (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ r n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * r n) → SatK.CountInRateN k r

end ClauseBound.ParityChecks
