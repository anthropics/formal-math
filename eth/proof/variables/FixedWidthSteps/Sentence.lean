/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.RouteDefs

/-! # The second statement of Theorem A (c), from the steps of its proof

The pieces give the named solver with its levels, and the number of the proviso is a number in [e_ℓ,
2e_ℓ] (`HypothesisHolds`); Theorem D (a) gives a machine M for it; some machine Mb tries all
assignments; there are a front end and a test; some machine N chooses between M and Mb by
the test; and by the main statement, with the rate of the pairs, N counts within the printed bound
for every fixed k. -/

public section

namespace FixedWidthSteps

open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth

/-- The second statement of Theorem A (c) (the bound in n for fixed width k, under its proviso),
from the steps of its proof. -/
theorem sentenceFromTheSteps : SentenceFromTheSteps := by
  intro hVariablesA hHyp hRate hChoose hFront hEx hEvery ρ c x₀ hPieces hx hc hProv
  obtain ⟨P, A, val, hP⟩ := hPieces
  obtain ⟨num, hnum, hb⟩ := hProv
  obtain ⟨C₀, h⟩ := hHyp c
  obtain ⟨Q, hpoly, hK, -, hNB⟩ := h ρ x₀ P A val hP hx hc
  obtain ⟨M, C', hMfin, hM⟩ := hVariablesA _ _ _ _ Q hpoly num (hNB num hnum hb)
  obtain ⟨Mb, cb, -, hMbfin, hMb, -⟩ := hEx
  obtain ⟨⟨pre, hprePoly, hpre⟩, hT⟩ := hFront
  obtain ⟨test, htestPoly, htest⟩ := hT ((solverOf (GeneralPieces.Tied.recOf P val c)).K (Q.idx 0))
  obtain ⟨_, _, N, _, q, hNfin, _, hN⟩ := hChoose M Mb hMfin hMbfin test pre id id id htestPoly hprePoly PolyT.id' PolyT.id' PolyT.id'
  have hρ0 : 0 < ρ := by have := hP.rho_ge; linarith
  have hα : 0 < AppRunningTime.alpha' ρ := Real.logb_pos one_lt_two (by rw [lt_div_iff₀ hρ0]; linarith [hP.rho_lt])
  exact ⟨N, hNfin, fun k hk => hEvery _ _ _ _ Q (AppRunningTime.alpha' ρ) (3 * x₀ + 6) hα (fun l => by rw [hK l]; exact hRate ρ x₀ l hP.rho_ge hP.rho_lt hx)
    M C' hM Mb cb hMb pre test hpre htest N q hN k hk⟩

end FixedWidthSteps
