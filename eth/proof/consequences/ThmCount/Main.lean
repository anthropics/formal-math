/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmCount.Defs
import ThmCount.FrontEnd
import ThmCount.Rates
import Wrap.Main
import Mathlib.Tactic

/-! # Theorem C from Theorem D(b) at k = 3

This is not the route of the proof sketch of Appendix C; see the head of
proof/consequences/ThmCount/Defs.lean.
* `wrapper_counts`: let M have the body of Theorem D(b) with the constant C, let `pre` map the plain
  code of a 3-CNF φ to the code of (3, φ with four forced variables more), and let N wrap M with
  `pre` and `dropFour`, with the number q. Then N computes the number of satisfying assignments of
  every 3-CNF on n variables within q·(⌊2^{C·9·(n+4)·log log(n+4)/√(log(n+4))}⌋ + a·(n+2)^d + 1)^q
  steps, where a·(n+2)^d bounds the length of the plain code.
* `stFromVariablesB`, `stCanBeWrappedAndEveryWrapperCounts`, `stTheorem`: with the comparison of the
  rates `stRates`.
* `stRemarkTime_of`: the time in the closing remark of Appendix C, as a sentence, from Theorem D(b),
  with the second comparison of rates `remark_rate`. -/

public section

namespace ThmCount

open Turing Groundwork PaperSentences

/-- Every machine N that wraps a machine M with the body of Theorem D(b), with a front end that adds
four forced variables and with `dropFour` as the last step, computes the number of satisfying
assignments of every 3-CNF on n variables within q·(time of M on n + 4 variables + a·(n+2)^d + 1)^q
steps, if a·(n+2)^d bounds the length of the plain code. -/
theorem wrapper_counts {a d : ℕ} (hl : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → (SatK.enc 3 φ).length ≤ a * (n + 2) ^ d)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : MainTheoremForms.ThmVariablesBFor M C) {pre : List Bool → List Bool} (hpre : MapsToPadded pre)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wrap.Wraps M pre dropFour N q) :
    SatK.CountsTM 3 N fun n => q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q := by
  intro n φ h3
  obtain ⟨p1, -, p3⟩ := stPadKeepsCount n φ h3
  have hrun : Wrap.Outputs M (pre (SatK.enc 3 φ)) (SatK.binary (n + 4) (SatK.numSat (Wrap.pad4 φ))) (MainTheoremForms.timeN C 3 (n + 4)) := by
    rw [hpre n φ h3]
    exact hM 3 (n + 4) (Wrap.pad4 φ) (by norm_num) (by omega) p1
  obtain ⟨ev⟩ := hW _ _ _ hrun
  rw [p3] at ev
  have hle : q * (MainTheoremForms.timeN C 3 (n + 4) + (SatK.enc 3 φ).length + 1) ^ q ≤ q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hl n φ h3; omega) q)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

/-- The time of `wrapper_counts` is at most the same expression with 2^{C·expN 3 (n+4)} in the place
of its floor, as a real number. -/
theorem time_cast (C q a d n : ℕ) : ((q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q : ℕ) : ℝ) ≤
    (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q := by
  have h : (MainTheoremForms.timeN C 3 (n + 4) : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) := Nat.floor_le (by positivity)
  push_cast
  gcongr

/-- **For every machine M with the body of Theorem D(b)**, every front end that adds four forced
variables and every machine N that wraps M with it and with `dropFour`: N computes the number of
satisfying assignments of every 3-CNF, on n ≥ 2 variables in time 2^{C'·n/(log n)^{1/20}}. This is
the statement `ThmCount.StFromVariablesB`. -/
theorem stFromVariablesB : StFromVariablesB := fun M C hM pre hpre N q hW => by
  obtain ⟨a, d, hl⟩ := stInputLength
  obtain ⟨C', hC'⟩ := stRates C q a d
  exact ⟨C', _, wrapper_counts hl hM hpre hW, fun n hn => (time_cast C q a d n).trans (hC' n hn)⟩

/-- Existence and the statement on every wrapper in one: for every machine M with finite alphabets
and the body of Theorem D(b) there are a polynomial-time front end, a machine N with finite
alphabets and q such that N wraps M with it and with `dropFour`; and every such N counts, as in
`stFromVariablesB`. This is the statement `ThmCount.StCanBeWrappedAndEveryWrapperCounts`. -/
theorem stCanBeWrappedAndEveryWrapperCounts : StCanBeWrappedAndEveryWrapperCounts := fun M C hfin hM => by
  refine ⟨?_, fun pre hpre N q hW => stFromVariablesB M C hM pre hpre N q hW⟩
  obtain ⟨pre, hp, hm⟩ := stFrontEnd
  obtain ⟨N, q, hf, hW⟩ := Wrap.everyMachineCanBeWrapped M hfin pre dropFour hp stLastStep
  exact ⟨pre, N, q, hp, hm, hf, hW⟩

/-- Theorem C from Theorem D(b): if one algorithm computes, for all k ≥ 1 and n ≥ 4, the number of
satisfying assignments of a k-CNF on n variables in time 2^{C·k²·n·log log n/√(log n)}, then one
algorithm computes the number of satisfying assignments of a 3-CNF on n ≥ 2 variables in time
2^{O(n/(log n)^{1/20})}. This is the statement `ThmCount.StTheorem`. -/
theorem stTheorem : StTheorem := fun h => by
  obtain ⟨M, C, hfin, hM⟩ := h
  obtain ⟨⟨pre, N, q, -, hm, hf, hW⟩, h2⟩ := stCanBeWrappedAndEveryWrapperCounts M C hfin hM
  obtain ⟨C', t, ht, hle⟩ := h2 pre hm N q hW
  exact ⟨C', N, t, hf, ht, hle⟩

/-- The time of the closing remark of Appendix C, as a sentence, from Theorem D(b): one algorithm
computes the number of satisfying assignments of a 3-CNF on n ≥ 4 variables in time 2^{O(n·(log log
n)^{2/3}/(log n)^{1/6})}. The machine is a wrapper as in `stCanBeWrappedAndEveryWrapperCounts`. -/
theorem stRemarkTime_of (h : MainTheoremForms.ThmVariablesB) : StRemarkTime := by
  obtain ⟨M, C, hfin, hM⟩ := h
  obtain ⟨⟨pre, N, q, -, hm, hf, hW⟩, -⟩ := stCanBeWrappedAndEveryWrapperCounts M C hfin hM
  obtain ⟨a, d, hl⟩ := stInputLength
  obtain ⟨K, hK⟩ := time_le C q a d
  exact ⟨K, N, _, hf, wrapper_counts hl hM hm hW, fun n hn => (time_cast C q a d n).trans (hK n _ (remark_rate hn).1 (remark_rate hn).2)⟩

end ThmCount
