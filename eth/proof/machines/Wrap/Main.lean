/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Wrap.Defs
import Wrap.CodingExists
import Wrap.Sim
import Wrap.FrontEnd
import Wrap.Arith
import Wrap.ArithRate
import WidthThree.Rates
import VariableBound.Paper.MainTheorem
import VariableBound.Paper.Arith
import VariableBound.Paper.Rename.End

/-! # From any machine that meets the bound for counting to a machine for 3-SAT on the plain input code: the end theorems

The statements are those of proof/machines/Wrap/Defs.lean. The pieces: every machine with finite
alphabets has a coding of its configurations (CodingExists.lean); from a coding, a fixed host
machine runs the given machine step by step, with a polynomial-time function before and one
after (Sim.lean); the front end that pads a 3-CNF with four forced variables and writes its compact
code (FrontEnd.lean); a power of the time bound is below c·2^{δn} (Arith.lean) and below the bound
in n at width 3 with a larger constant (ArithRate.lean). Here they are put together. The steps from
«one machine for every δ» to the other four
statements are those of proof/maintheorem/WidthThree/Rates.lean. -/

public section

namespace Wrap

open Turing Groundwork
open scoped NNReal

/-- Every machine with finite alphabets can be given a polynomial-time front end and a
polynomial-time last step. -/
theorem everyMachineCanBeWrapped : EveryMachineCanBeWrapped := everyMachineCanBeWrapped_of coding_exists

/-! ### What a wrapper does on the plain code of a formula -/

/-- The condition on a time bound T under which the lemma below gives `Sat3.DecidesTM N T`: T n is
at least q·(time + X + 1)^q, where the time is the bound of the wrapped machine with the constants
C₁ and C₂ on a formula with m' ≥ 2 clauses in which n' variables occur,
4 ≤ n' ≤ n + 4, whose compact code has length L, X is the length of the plain code, and L and X are
at most a·(n+2)^d. -/
def Covers (q C₁ C₂ a d : ℕ) (T : ℕ → ℕ) : Prop :=
  ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
    q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ T n

/-- A wrapper N of a machine M that counts on the compact code within the bound, with «some bit is
1» after it, decides 3-SAT on the plain code within every time bound T that `Covers` allows.
M is used at width 3; the count of `pad4 φ`, written in binary, has a bit 1 if and only if `pad4 φ`
is satisfiable. At width 3 the bound with the constant C is at most the bound for width 3 with the
constant 9·C. -/
theorem decidesTM_of_wraps_counter {pre : List Bool → List Bool} (hpre : MapsPlainToPaddedCompact pre) {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : CountsCompactKCNFWithinMinBound M C)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wraps M pre someBit N q) {a d : ℕ}
    (hL : ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d)
    {T : ℕ → ℕ} (hT : Covers q (9 * C) C a d T) : Sat3.DecidesTM N T := by
  intro n φ hφ
  obtain ⟨h3, hlen, h4, hle, hsat⟩ := pad4KeepsSatAndMeetsSideConditions n φ hφ
  have hm : 2 ≤ (pad4 φ).length := by omega
  obtain ⟨ev⟩ := hW (Sat3.enc φ) _ _ (by rw [hpre n φ hφ]; exact hM 3 (n + 4) (pad4 φ) (by norm_num) h3 hm h4)
  have e : someBit (SatK.binary (MainTheoremForms.numOcc (pad4 φ)) (MainTheoremForms.numSatOcc (pad4 φ))) = [decide (MainTheoremForms.numSatOcc (pad4 φ) ≠ 0)] :=
    VariableBound.Rename.anyBit_binary (VariableBound.Paper.numSatOcc_lt (pad4 φ))
  rw [e] at ev
  refine ⟨decide (MainTheoremForms.numSatOcc (pad4 φ) ≠ 0), by rw [decide_eq_true_iff, ← VariableBound.Paper.satisfiable_iff, hsat], ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩⟩
  refine le_trans ?_ (hT n _ _ _ _ hm h4 hle (hL n φ hφ).1 (hL n φ hφ).2)
  gcongr
  exact VariableBound.Paper.timeMin_three_le C hm h4

/-! ### The main statements -/

/-- Every wrapper of a machine that counts, with «some bit is 1» after it, decides 3-SAT on the
plain code within c·2^{δn} steps, for every δ > 0: by `wrapped_time_le`, c·2^{δn} covers the time. -/
theorem everyWrapperOfACounterDecidesEveryDelta : EveryWrapperOfACounterDecidesEveryDelta := by
  intro pre hpre M C hM N q hW δ hδ
  obtain ⟨a, d, hL⟩ := length_encC_pad4_le
  obtain ⟨c, hc⟩ := wrapped_time_le q (9 * C) C a d (δ := (δ : ℝ)) (by exact_mod_cast hδ)
  exact ⟨c, decidesTM_of_wraps_counter hpre hM hW hL hc⟩

/-- Every wrapper of a machine that counts, with «some bit is 1» after it, decides 3-SAT on the
plain code within the bound in n at width 3 with a suitable constant: by `wrapped_time_le_rate`, it
covers the time. -/
theorem everyWrapperOfACounterDecidesAtRateInN : EveryWrapperOfACounterDecidesAtRateInN := by
  intro pre hpre M C hM N q hW
  obtain ⟨a, d, hL⟩ := length_encC_pad4_le
  obtain ⟨c, hc⟩ := wrapped_time_le_rate q (9 * C) C a d
  exact ⟨c, decidesTM_of_wraps_counter hpre hM hW hL hc⟩

/-! ### With the existence of the front end and of the wrapper -/

/-- «Nothing» and «some bit is 1» are polynomial-time. -/
theorem lastStepsArePolynomialTime : LastStepsArePolynomialTime := ⟨PolyT.id', VariableBound.Rename.anyBit_polyT⟩

/-- Existence, by `frontEndExists` and `everyMachineCanBeWrapped`, and the two statements on every
wrapper of a machine that counts. -/
theorem counterCanBeWrappedAndEveryWrapperDecides : CounterCanBeWrappedAndEveryWrapperDecides := fun M C hfin hM =>
  let ⟨pre, hpre⟩ := frontEndExists
  let ⟨N, q, hN, hW⟩ := everyMachineCanBeWrapped M hfin pre someBit hpre.1 lastStepsArePolynomialTime.2
  ⟨⟨pre, N, q, hpre, hN, hW⟩, fun pre' hpre' N' q' hW' =>
    ⟨everyWrapperOfACounterDecidesEveryDelta pre' hpre' M C hM N' q' hW', everyWrapperOfACounterDecidesAtRateInN pre' hpre' M C hM N' q' hW'⟩⟩

/-! ### The implications between propositions -/

/-- A machine that decides 3-SAT on the plain code within c·2^{δn} steps for every δ > 0 gives the
five statements. -/
theorem oneMachineEveryDeltaAndETHFails_of {N : TM2ComputableAux Bool Bool} (hN : ∀ i, Finite (N.tm.Γ i)) (h : DecidesEveryDelta N) : OneMachineEveryDeltaAndETHFails :=
  have hs : Sat3.SubexpTM := ⟨N, hN, h⟩
  ⟨hs, WidthThree.everyDeltaAMachine_of_subexpTM hs, WidthThree.ethFails_of_subexpTM hs, WidthThree.everyDeltaAMachineWording_of_subexpTM hs, WidthThree.ethFailsWording_of_subexpTM hs⟩

/-- If the bound for counting holds, so do the five statements: the machine of the hypothesis is
wrapped, and its wrapper decides for every δ, by `counterCanBeWrappedAndEveryWrapperDecides`. -/
theorem countingBoundImpliesFailureOfETH : CountingBoundImpliesFailureOfETH := fun ⟨M, C, hfin, hM⟩ =>
  let ⟨⟨pre, N, q, hpre, hN, hW⟩, hall⟩ := counterCanBeWrappedAndEveryWrapperDecides M C hfin hM
  oneMachineEveryDeltaAndETHFails_of hN (hall pre hpre.2 N q hW).1

end Wrap
