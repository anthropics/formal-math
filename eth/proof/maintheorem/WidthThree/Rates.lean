/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatRateStatement
public import ThmEveryDeltaStatement
public import PaperSentencesStatement
public import MainTheoremFormsStatement
import PaddedDescent.RateLemmas
import VariableBound.Paper.Arith
import ToTuring.EndLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # At width 3: from one machine for all δ > 0 to Theorem 2 and to the failure of the exponential time hypothesis

This file goes from the hypothesis «one machine decides 3-SAT within A·2^{δn} steps for every δ > 0»
(`Sat3.SubexpTM`) to four statements:
for every δ > 0 some machine decides 3-SAT within c·2^{δn} steps (Theorem 2 in its decision form),
in two wordings, and the failure of the exponential time hypothesis (Corollary 5), in two wordings.
The proofs derive these four statements from the hypothesis alone. -/

public section

namespace WidthThree

open Turing
open scoped NNReal

/-! ### From «one machine for all δ > 0» to Theorem 2 and to the failure of the exponential time hypothesis -/

/-- If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then for every real δ > 0
some machine decides 3-SAT within c·2^{δn} steps. -/
theorem everyDeltaAMachine_of_subexpTM (h : Sat3.SubexpTM) : Sat3.ThmEveryDelta := by
  intro δ hδ
  obtain ⟨M, hfin, hM⟩ := h
  obtain ⟨c, hc⟩ := hM ⟨δ, hδ.le⟩ hδ
  refine ⟨M, c, hfin, fun n φ hφ => ?_⟩
  obtain ⟨b, hb, hr⟩ := hc n φ hφ
  exact ⟨b, _, hb, Nat.floor_le (by positivity), hr⟩

/-- If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then the exponential time
hypothesis, in the form «the infimum of the δ for which 3-SAT is in time O(2^{δn}) is positive»,
fails. -/
theorem ethFails_of_subexpTM (h : Sat3.SubexpTM) : ¬ Sat3.ETH_TM := h.not_ETH_TM

/-- If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then for every real δ > 0
some machine decides 3-SAT in time at most C·2^{δn}, in the wording with a real constant C and a
time function t(n) ≤ C·2^{δn}. -/
theorem everyDeltaAMachineWording_of_subexpTM (h : Sat3.SubexpTM) : PaperSentences.ThmEveryDelta := by
  intro δ hδ
  obtain ⟨M, hfin, hM⟩ := h
  obtain ⟨c, hc⟩ := hM ⟨δ, hδ.le⟩ hδ
  exact ⟨c, M, _, hfin, hc, fun n _ => Nat.floor_le (by positivity)⟩

/-- If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then the exponential time
hypothesis, in the form «s_k > 0 for all k ≥ 3», fails: it fails at k = 3. -/
theorem ethFailsWording_of_subexpTM (h : Sat3.SubexpTM) : ¬ PaperSentences.ETH := fun hE => h.not_ETH_TM (hE 3 le_rfl)

end WidthThree
