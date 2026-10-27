/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInKStatement
public import CountKSatRate.Interfaces
import UniformInK.Top.End
import ClauseBound.Both.End

/-! # What the end of the proof of Theorem 1 uses of an algorithm, and the bit «satisfiable»

Theorem 1 counts the satisfying assignments; the count is positive exactly if the formula is
satisfiable, so the bit «satisfiable» is a polynomial-time function of the count. This file has

* `VariableBound.Decide.Alg rn rm A e`: what the end of the proof of Theorem 1 uses of an algorithm,
  given as a function A of (input, pad) with an exponent function e for the pad: both are
  polynomial-time, A is right on the code of every
  (k, φ) when the pad has at least 2^(e x) units, and the number of steps q·(|x| + 2^(e x) + 1)^q of
  the padding machine is within the bound in n and within the bound in m;
* `bitOf`, «some bit of the word is 1», and `polyT_bitOf`: it is polynomial-time.

Nothing here depends on which algorithm is used. -/

@[expose] public section

namespace SatM

open Turing
open Sat3 (CNF)

end SatM

namespace VariableBound.Decide

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate

/-- What the end of the proof of Theorem 1 uses of an algorithm: a function A of (input, pad) and an
exponent function e for the pad. -/
structure Alg (rn rm : ℕ → ℝ) (A : List Bool × U → List Bool) (e : List Bool → ℕ) : Prop where
  /-- A is polynomial-time -/
  polyA : PolyT A
  /-- e is polynomial-time -/
  polyE : PolyT e
  /-- on the code of (k, φ), k ≥ 1, φ a k-CNF, with a pad of at least 2^(e x) units, A is the number
  of satisfying assignments in n + 1 bits -/
  correct : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ e (SatM.enc k φ) ≤ pad.length → A (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
  /-- for n ≥ 1 the number of steps of the padding machine is within the bound in n, for every q,
  with a constant that does not depend on k -/
  timeN : ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.boundNK rn D k n
  /-- if all variables occur and m ≥ 1, it is within the bound in m, for every q, with a constant
  that does not depend on k -/
  timeM : ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
    q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.bound rm D k φ.length

/-- The one bit «some bit of the word w is 1». -/
def bitOf (w : List Bool) : List Bool := [w.any id]

end VariableBound.Decide

end

public section

namespace VariableBound.Decide

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Both.End UniformInK.End

/-! ### The bit -/

/-- «Some bit is 1» is polynomial-time. -/
theorem polyT_bitOf : PolyT bitOf := by
  unfold bitOf
  fun_prop

end VariableBound.Decide
