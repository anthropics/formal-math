/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.CircuitDefs
public import SizeCircuit.General
public import SizeCircuit.Addition
import SizeCircuit.Compare
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: «a circuit with O(n) gates of two inputs tests whether |S| = s»

`testsSize_sizeGates`: the circuits `sizeGates n s` of
proof/consequences/SizeCircuit/CircuitDefs.lean have at most 6·(n+1) gates, their gates read earlier
wires only, and on a word of length n ≥ 1 their output is 1 exactly if the word has s ones. From the
addition (Addition.lean) and the comparison (Compare.lean), applied to the values of the wires on
the input. -/

public section

namespace SizeCircuit

open Groundwork CircuitLowerBound CircuitLowerBound.Blocks ENP

/-- The sum of the bits of a word is the number of its ones. -/
theorem sum_toNat (x : List Bool) : (x.map Bool.toNat).sum = x.count true := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases b
    · rw [List.count_cons_of_ne (by decide)]
      simp
    · rw [List.count_cons_self]
      simp [add_comm]

/-- The number of input wires that are 1 is the number of ones of the input. -/
theorem onesAmong_inputs (x : List Bool) (K : List GateD) : onesAmong (wireVal x K) (List.range x.length) = x.count true := by
  have h : ((List.range x.length).map fun i => (wireVal x K i).toNat) = x.map Bool.toNat := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < x.length := by simpa using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, wireVal_input x K hi, List.getD_eq_getElem _ _ hi]
  rw [onesAmong, h, sum_toNat]

/-- **«a circuit with O(n) gates of two inputs tests whether |S| = s».** For all n ≥ 1 and all s,
`sizeGates n s` has at least one and at most 6·(n+1) gates, every gate reads earlier wires only, and
on a word of length n the output is 1 exactly if the word has s ones. -/
theorem testsSize_sizeGates : TestsSize sizeGates 6 := by
  intro n s hn
  obtain ⟨-, -, hd, hW, hK, hD⟩ := added_spec n
  have hlen : (sizeGates n s).length = (added n).2.2.2.length + ((added n).2.2.1.length + 1) := by
    rw [sizeGates, List.length_append, length_compareGates]
  have hWF : WFa n (sizeGates n s) := (wfa_append n _ _).2 ⟨hW, wfa_compareGates (by omega) hd⟩
  refine ⟨fun h => ?_, by rw [hlen]; omega, wf_of_wfa hWF, fun x hx => ?_⟩
  · rw [h, List.length_nil] at hlen
    omega
  · subst hx
    have hO : Obeys (wireVal x (sizeGates x.length s)) x.length
        ((added x.length).2.2.2 ++ compareGates (x.length + (added x.length).2.2.2.length) s (added x.length).2.2.1) :=
      obeys_wireVal x (sizeGates x.length s) hWF
    obtain ⟨h1, h2⟩ := (obeys_append _ _ _ _).1 hO
    have e1 := addValue_added _ _ h1
    have e2 := compareGates_spec _ _ _ _ h2
    have hidx : x.length + (sizeGates x.length s).length - 1 = x.length + (added x.length).2.2.2.length + (added x.length).2.2.1.length := by
      rw [hlen]
      omega
    rw [eval_eq_wireVal, hidx, e2, e1, onesAmong_inputs, decide_eq_true_eq]

end SizeCircuit
