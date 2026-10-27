/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.Defs
import CountKSatRate.Leaf
import all CountKSat.Top.Count
import all UniformInK.Top.Correct

/-! # What a plan of the function for the bound in n says

`planAtD_some` says what a plan `some v` gives, for a polynomial-time solver: s ≥ s0U k, Δ = 2^β ≤ n +
1, n ≥ 29·⌈log₂(2Δ)⌉ + 19, and the exponent v is `needD`. -/

namespace VariableBound.Correct

open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net

/-- What a plan says, for a polynomial-time solver: the three tests hold, and the exponent is
`needD`. -/
theorem planAtD_some {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) {k n s v : ℕ} {i : Idx} (h : planAtD S k n i s = some v) :
    (s0U k ≤ s ∧ 2 ^ betaU k s ≤ n + 1 ∧ 29 * LD (2 ^ betaU k s) + 19 ≤ n) ∧ v = needD S k i n s := by
  unfold planAtD at h
  split_ifs at h with hc
  obtain ⟨v', h1, h2⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h2 with hc2
  obtain ⟨u, h3, h4⟩ := Option.map_eq_some_iff.1 h1
  have hu := hS.needC_eq _ _ _ h3
  refine ⟨hc, ?_⟩
  rw [← Option.some.inj h2, ← h4, hu]
  rfl

end VariableBound.Correct

namespace VariableBound

open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)

end VariableBound
