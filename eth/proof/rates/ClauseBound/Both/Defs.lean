/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
public import FixedWidthVariableBoundStatement

/-! # The running time of the padding machine against the bound in n and the bound in m: statements

Two algorithms are functions of (input, pad), and both compute from the input the exponent of a pad
that suffices (`eM` of proof/rates/ClauseBound/Alg/Top.lean for the bound in m, `eO` of
proof/rates/ClauseBound/ParityChecks/TopDefs.lean
for the bound in n). `StTimeO` and `StTimeM` say that q·(|x| + 2^e + 1)^q, for the exponent e of the
one or of the other, is within the bound in n, respectively within the bound in m (there when every
variable occurs and there is a clause). -/

@[expose] public section

namespace ClauseBound.Both

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

end

/-! ### The running time of the padding machine against the two bounds (TimeM.lean for the bound in m) -/

/-- For the exponent of the algorithm for n: q·(|x| + 2^e + 1)^q is within the bound in n, for a
suitable c, every n₀ and every q. -/
def StTimeO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ),
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (k : ℕ) (r : ℕ → ℝ) (c₁ : ℕ), 1 ≤ k → (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ r n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * r n) →
  ∃ c : ℕ, ∀ n₀ q : ℕ, ∃ D : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    q * ((SatK.enc k φ).length + 2 ^ eO S c n₀ k Q.pick slU (SatK.enc k φ) + 1) ^ q ≤ SatK.boundN r D n

/-- For the exponent of the algorithm for m. -/
def StTimeM : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (r : ℕ → ℝ) (c₁ : ℕ),
  (∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ r m) →
  (∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * r m) →
  ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
    q * ((SatM.enc k φ).length + 2 ^ eM S Q.pick (SatM.enc k φ) + 1) ^ q ≤ SatM.bound r D k φ.length

end ClauseBound.Both
