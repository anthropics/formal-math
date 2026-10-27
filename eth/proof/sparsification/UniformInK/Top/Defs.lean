/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Tree.Defs
public import ClauseBound.ParityChecks.TopDefs
public import ClauseBound.Both.Defs
public import UniformInKStatement

/-! # One function for all widths k: parameters, helper functions and interface statements

The twin of proof/rates/ClauseBound/ParityChecks/TopDefs.lean and
proof/rates/ClauseBound/Both/Defs.lean. The input is 1ᵏ 0 1ⁿ 0 and the clauses; the width k is read
from it (`kOf`, `fmlOf` of proof/rates/ClauseBound/Alg/Top.lean).
What differs from a fixed width:
* the sparsification uses the thresholds `thetaU τ`, so that Δ = 2^β with β = `betaU k s` =
  2k(4s+17), linear in k;
* the precision s is large enough for the width k when s ≥ `s0U` k = 2·(number of binary digits of
  k), which gives k² ≤ 2^s;
* the walk is called with the width cut off at ⌊log₂(n+1)⌋ (`kcU`), so that 2^k can be written in
  unary on every input; whenever the walk is used, the cut-off does nothing.
This file has definitions only. The statements `St…` are propositions; one file proves each of them. -/

@[expose] public section

namespace UniformInK

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

/-! ### The parameters for width k and precision s -/

/-- The code parameter: 2^(betaU k s) = τ^(2k) for τ = 2^(4s+17). It is at least the number of
clauses per variable of a leaf, and at least `bsumU τ k`. -/
def betaU (k s : ℕ) : ℕ := 2 * k * (4 * s + 17)

/-- The precision s is large enough for the width k if s ≥ s0U k; then k² ≤ 2^s. -/
def s0U (k : ℕ) : ℕ := 2 * Nat.size k

/-- 2^β, cut off at n + 1. The function uses the networks only if 2^β ≤ n + 1, and then this is 2^β. -/
def blockU (k n s : ℕ) : ℕ := min (2 ^ betaU k s) (n + 1)

/-- The width, cut off at ⌊log₂(n+1)⌋. -/
def kcU (k n : ℕ) : ℕ := min k (Nat.log 2 (n + 1))

/-- The width written in the input. -/
def kU (x : List Bool) : ℕ := (kOf x).length

/-- The number of variables written in the input. -/
def nU (x : List Bool) : ℕ := (fmlOf x).1.length

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-! ### The functions -/

/-- Exhaustive counting on the formula written in p.1: how many numbers y below 2^n, cut off at the
length of the pad p.2, code a satisfying assignment. -/
def bruteU (p : List Bool × U) : ℕ := ((rng p.2 (2 ^ (fmlOf p.1).1.length)).filter fun y => satAt (fmlOf p.1).2 y).length

/-- The exponent of a pad that suffices for everything but the networks: the list of profiles, the
lists of the checks, the rounds of the walk, the stack of the walk. -/
def restU (k K n s : ℕ) : ℕ :=
  3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (blockU k n s) * (7 * n + 1)) + (3 * Nat.size (blockU k n s * n) + 3 * Nat.size n + 12) + (n / 2 ^ s + 2) +
    (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n)

/-- The exponent of a pad that suffices for n variables at the index i with precision s. -/
def needU (k : ℕ) (i : Idx) (n s : ℕ) : ℕ :=
  needNet S i (UbOL k (S.K i) n (blockU k n s)) (PbOL (S.K i) n (blockU k n s)) 0 + restU k (S.K i) n s

/-- The index of the level picked for the input x. -/
def idxU (pick : U → U × Idx) (x : List Bool) : Idx := (pick (root17 (nU x))).2

/-- The precision picked for the input x. -/
def precU (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (slU (pick (root17 (nU x))).1).length

/-! ### Whether every variable occurs -/

/-- Does every variable below n occur in the formula written in x? -/
def allOccU (x : List Bool) : Bool := (List.range (nU x)).all fun v => (fmlOf x).2.any fun C => C.any fun l => l.1 == v

end

/-! ### The budgets -/

/-- The number of leaves: Σ_{j ≤ kn/τ} C(bsumU τ k · n, j) ≤ 2^(⌊n/2^s⌋ + 1) for τ = 2^(4s+17), k ≥
1 and s ≥ s0U k. -/
def StLeavesU : Prop := ∀ k n s : ℕ, 1 ≤ k → s0U k ≤ s →
  ∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j ≤ 2 ^ (n / 2 ^ s + 1)

/-- The parameters fit: clauses per variable of a leaf; and the threshold is large enough for the
width. -/
def StParU : Prop := ∀ k s : ℕ, 1 ≤ k → leafCU (tauOf s) k + 2 ≤ 2 ^ betaU k s ∧ (s0U k ≤ s → k ^ 2 ≤ tauOf s ∧ 8 * k ≤ tauOf s)

/-! ### Correctness -/

/-- On the code of an instance, `allOccU` says whether every variable occurs. -/
def StAllOccU : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → (allOccU (SatM.enc k φ) = true ↔ SatM.AllOccur φ)

/-! ### The running time of the padding machine against the bound in n -/

/-- What the fall-back to exhaustive counting needs of the rate r: where k² is larger than a
multiple of log n, k²·r(n) is bounded below. -/
def FallBack (r : ℕ → ℝ) : Prop := ∀ B : ℕ, ∃ c₂ : ℕ, ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → Nat.log 2 n < B * k ^ 2 → 1 ≤ (c₂ : ℝ) * (k : ℝ) ^ 2 * r n

end UniformInK
