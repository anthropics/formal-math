/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.Defs
import UniformInK.Top.End
import ClauseBound.Both.End

/-! # The merged function for thresholds Θ and its exponent function are an algorithm

`stAlgSG`: for thresholds Θ that serve and a solver with a sequence of levels, the merged function
(sparsification with the thresholds Θ, then the count of each output) with its exponent function is
an algorithm for the two rates in the sense of `VariableBound.Decide.Alg`. Only the first two of
its five hypotheses name the thresholds: the merged function is right (`StCorrectBDG`) and
polynomial-time (`StCertBDG`). The other three are those of proof/variables/VariableBound: the
exponent is at most those of the two algorithms merged
(`VariableBound.StExpBD`), and the two inequalities for the number of steps
(`VariableBound.StTimeD`, `ClauseBound.Both.StTimeM`). The steps from an algorithm to a machine and
to the statements that name no function are generic and are not repeated. -/

public section

namespace SparsifyThenCount

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound VariableBound.Decide

/-- For thresholds Θ that serve (with the bound Lc) and a solver with a sequence of levels: the
merged function for Θ and its exponent function are an algorithm for the rates rn and rm. Given: the
merged function is right (`StCorrectBDG`), it and the exponent function are polynomial-time
(`StCertBDG`), the exponent is at most those of the two algorithms merged (`StExpBD`), and the two
inequalities for the number of steps
(`StTimeD`, `StTimeM`). -/
theorem stAlgSG (hC : StCorrectBDG) (hK : StCertBDG) (hE : StExpBD) (hTD : StTimeD) (hTM : ClauseBound.Both.StTimeM) (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (hΘ : StepSparsify.Serves Θ Lc) :
    StAlgSG Θ := by
  intro Idx _ S e C₀ Q hS slU C hsl h1 h2 rn rm c₁ hrn hen hfb hrm hem _ _
  obtain ⟨hAB, heB⟩ := hK Θ Lc hΘ Idx S hS Q.pick slU Q.pick_poly hsl
  refine ⟨hAB, heB, fun k n φ hk hφ pad hp => hC Θ Lc hΘ Idx S e C₀ Q hS slU k n φ hk hφ pad hp, fun q => ?_, fun q => ?_⟩
  · obtain ⟨D, hD⟩ := hTD Idx S e C₀ Q hS slU C h1 h2 rn c₁ hrn hen hfb q
    exact ⟨D, fun k n φ hk hn1 hφ => (steps_mono q le_rfl (hE Idx S k Q.pick slU n φ hk hφ).1).trans (hD k n φ hk hn1 hφ)⟩
  · obtain ⟨D', hD'⟩ := hTM Idx S e C₀ Q hS rm c₁ hrm hem q
    exact ⟨D', fun k n φ hk hm1 hφ ho => (steps_mono q le_rfl ((hE Idx S k Q.pick slU n φ hk hφ).2 ho hm1)).trans (hD' k n φ hk hm1 hφ ho)⟩

end SparsifyThenCount
