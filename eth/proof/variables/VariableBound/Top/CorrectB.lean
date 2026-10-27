/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.Defs

/-! # When the merged function takes the algorithm for the bound in m, and its exponent is the smaller one

Part of the proof of Corollary 11, «computing the two exponents … and running only the algorithm
with the smaller one» (here the two exponents are computed exactly). `useMD_enc`: on the code of a
k-CNF the algorithm for the bound in m is taken
exactly if every variable occurs, there is a clause, and its exponent is not the larger one.
`stExpBD`: the exponent of the merged function is at most that of the algorithm for the bound in n,
and,
if every variable occurs and there is a clause, at most that of the algorithm for the bound in m. -/

public section

namespace VariableBound.CorrectB

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK

/-- On the code of (k, φ), k ≥ 1, φ a k-CNF, the algorithm for the bound in m is taken exactly if
every variable occurs, there is a clause, and its exponent is not the larger one. Given
`UniformInK.StAllOccU` and `StDecM`. -/
theorem useMD_enc (hA : StAllOccU) (hD : StDecM) {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pick : U → U × Idx) (slU : U → U) {n : ℕ} (φ : Sat3.CNF n)
    (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) :
    useMD S pick slU (SatM.enc k φ) = true ↔
      SatM.AllOccur φ ∧ 1 ≤ φ.length ∧ eM S pick (SatM.enc k φ) ≤ eD S pick slU (SatM.enc k φ) := by
  unfold useMD
  rw [(hD k n φ hk hφ.1).2, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hA k n φ hk hφ, Decode.length_toN, and_assoc]

end VariableBound.CorrectB

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.CorrectB

/-- For k ≥ 1 and a k-CNF: the exponent is at most that of the algorithm for n, and, if all
variables occur and there is a clause, at most that of the algorithm for m. -/
theorem stExpBD (hA : StAllOccU) (hD : StDecM) : StExpBD := by
  intro Idx _ S k pick slU n φ hk hφ
  have hiff := useMD_enc hA hD S k pick slU φ hk hφ
  unfold eBD
  cases hu : useMD S pick slU (SatM.enc k φ) with
  | true =>
    rw [cond_true]
    exact ⟨(hiff.1 hu).2.2, fun _ _ => le_rfl⟩
  | false =>
    rw [cond_false]
    refine ⟨le_rfl, fun h1 h2 => ?_⟩
    by_contra hlt
    have h3 := hiff.2 ⟨h1, h2, (not_le.1 hlt).le⟩
    rw [hu] at h3
    cases h3

end VariableBound
