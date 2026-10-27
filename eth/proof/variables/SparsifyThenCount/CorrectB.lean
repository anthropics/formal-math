/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.Defs
import VariableBound.Top.CorrectB

/-! # The merged function is right

`stCorrectBDG : StCorrectBDG` holds for any family of thresholds that serves: the merged function
returns the number of satisfying assignments if the pad has the length that the
exponent `VariableBound.eBD` asks for. The test `VariableBound.useMD` and the exponent are those of
proof/variables/VariableBound and do not name the thresholds. Where the test holds, every variable
occurs and there is a clause (`VariableBound.CorrectB.useMD_enc`), which is what the
correctness of the algorithm for the bound in m needs (`StCorrectM`); elsewhere the function is
`ADG`, which is right by `StCorrectDG`. -/

public section

namespace SparsifyThenCount

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.CorrectB

/-- The merged function, run with thresholds that serve, is right on every k-CNF, for every k ≥ 1
and every n, when the pad has length at least 2^(eBD …); given that the two algorithms are right
(`StCorrectDG`, `StCorrectM`), the test on the
variables (`UniformInK.StAllOccU`) and the decoder (`StDecM`). -/
theorem stCorrectBDG (h : StCorrectDG) (hM : StCorrectM) (hA : StAllOccU) (hD : StDecM) : StCorrectBDG := by
  intro Θ Lc hSv Idx _ S e C₀ Q hS slU k n φ hk hφ pad hpad
  change (bif useMD S Q.pick slU (SatM.enc k φ) then AM S Q.pick (SatM.enc k φ, pad) else ADG Θ S Q.pick slU (SatM.enc k φ, pad)) = _
  unfold eBD at hpad
  cases hu : useMD S Q.pick slU (SatM.enc k φ) with
  | true =>
    rw [hu, cond_true] at hpad
    rw [cond_true]
    obtain ⟨h1, h2, -⟩ := (useMD_enc hA hD S k Q.pick slU φ hk hφ).1 hu
    exact hM Idx S e C₀ Q hS k n φ hk h2 hφ h1 pad hpad
  | false =>
    rw [hu, cond_false] at hpad
    rw [cond_false]
    exact h Θ Lc hSv Idx S e C₀ Q hS slU k n φ hk hφ pad hpad

end SparsifyThenCount
