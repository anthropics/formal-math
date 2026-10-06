/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Util.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The parameters and model running times of Sections 3.1 to 3.4

Numbers and functions that the running-time claims of Section 3 and the programs of Section 3 share.
None of them mentions a claim or a machine.

* `TriangleInstance.totalChunks`, the number of chunks in the proof of Theorem 17, and the three
  terms of the additional time of Theorem 17: `termScans`, `termPrime`, `termBuild`.
* The parameters of the proof of Theorem 19: `paramD₅`, `paramG₅` on the route through
  Theorem 5 and `paramD₂₆`, `paramG₂₆` on the route through Corollary 26; `strassen`, the number of
  ring operations of Strassen's algorithm.
* `splitCap`, the size of the pieces into which Corollary 15 splits the query pairs.
* `DivNondecreasing` and `GoodTime`, the condition of Theorem 21(b) on a running time, and
  `uniformTime`, the running time of Theorem 19 as a function of the size and of the bound on the
  weights.  (The number of vertices `n^{1/3}` of Theorem 21(b) is `cbrtCeil n`.)
-/

@[expose] public section

namespace ThreeSumApsp

/-- Proof of Theorem 17: the number of chunks "in all", summed over the residues `ϱ`. -/
noncomputable def TriangleInstance.totalChunks {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) : ℕ :=
  ∑ ϱ : Fin p, numChunks (T.residueClass p ϱ) (queryCap n D)

/-- Theorem 21(b): "with T(s)/s nondecreasing". -/
def DivNondecreasing (T : ℕ → ℝ) : Prop :=
  ∀ s₁ s₂ : ℕ, 1 ≤ s₁ → s₁ ≤ s₂ → T s₁ / s₁ ≤ T s₂ / s₂

/-- Theorem 21(b): a running time "T(s) with T(s)/s nondecreasing", for every fixed bound
`u` on the numbers.

NOTE.  We also ask that `T(s) ≥ s² (1 + log u)`, which is an upper bound for the time to write down
the `3s²` weights of an instance. The paper does not say this, but its bound
`O(n² T(n^{1/3}) log² U)` leaves no room for writing down the instances otherwise.  The condition is
a hypothesis on the running times that are fed into Theorem 21(b), so it makes the claims that use
it weaker, not stronger. -/
def GoodTime (T : ℕ → ℝ → ℝ) : Prop :=
  (∀ (s : ℕ) (u : ℝ), 1 ≤ s → (s : ℝ) ^ 2 * (1 + logU u) ≤ T s u) ∧
    ∀ u : ℝ, DivNondecreasing fun s => T s u

/-- The running time `K s^{3−δ} (log s + 1)^e (1 + log u)²` for Exact Triangle on `s` vertices per
part with weights of absolute value at most `u`, as a function of both arguments. -/
noncomputable def uniformTime (K δ : ℝ) (e : ℕ) (s : ℕ) (u : ℝ) : ℝ :=
  K * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2)

/-- **Theorem 17**, the first term of the additional time, "ν n³ log n/g".  It pays for the scans.
`κ` is the paper's ν. -/
noncomputable def termScans (n g : ℕ) (κ : ℝ) : ℝ := κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)

/-- **Theorem 17**, the second term of the additional time, "n^{ω+o(1)} D^{3/2}".  It pays for the
choice of the prime.  `MM n` stands for the number of ring operations of the matrix multiplication,
the paper's `n^{ω+o(1)}`. -/
noncomputable def termPrime (MM : ℕ → ℝ) (n D : ℕ) : ℝ := MM n * (D : ℝ) ^ (3 / 2 : ℝ)

/-- **Theorem 17**, the third term of the additional time, "n² D g".  It pays for building the
instances. -/
noncomputable def termBuild (n D g : ℕ) : ℝ := (n : ℝ) ^ 2 * (D : ℝ) * (g : ℝ)

/-- Strassen's number of ring operations, up to a constant: `n^{log₂ 7}`. -/
noncomputable def strassen (n : ℕ) : ℝ := (n : ℝ) ^ Real.logb 2 7

/-- Strassen's number of ring operations is not negative. -/
theorem strassen_nonneg (n : ℕ) : 0 ≤ strassen n := Real.rpow_nonneg n.cast_nonneg _

/-- Proof of Theorem 19, by Theorem 5: "Let D be the largest power of four with D ≤
n^{1/18}". -/
noncomputable def paramD₅ (n : ℕ) : ℕ := 4 ^ Nat.log 4 ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊

/-- Proof of Theorem 19, by Theorem 5: "and let g := ⌈D^{1/36}⌉". -/
noncomputable def paramG₅ (n : ℕ) : ℕ := ⌈(paramD₅ n : ℝ) ^ (1 / 36 : ℝ)⌉₊

/-- Proof of Theorem 19, by Corollary 26: "Let D := ⌊n^{1/18}⌋". -/
noncomputable def paramD₂₆ (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊

/-- Proof of Theorem 19, by Corollary 26: "and g := ⌈D^{0.0315}⌉". -/
noncomputable def paramG₂₆ (n : ℕ) : ℕ := ⌈(paramD₂₆ n : ℝ) ^ (0.0315 : ℝ)⌉₊

/-- Corollary 15: the size `⌊n²/√D⌋` of the sets into which `W` is split (at least 1, so
that the split makes sense for all values of the parameters). -/
noncomputable def splitCap (n D : ℕ) : ℕ := max 1 (queryCap n D)

end ThreeSumApsp
