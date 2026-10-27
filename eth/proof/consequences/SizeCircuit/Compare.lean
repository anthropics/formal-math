/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.CircuitDefs
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: the circuit compares the number of ones with s

Facts on `compareGates` of proof/consequences/SizeCircuit/CircuitDefs.lean, for «a circuit with O(n)
gates of two inputs tests whether |S| = s»: under all values of the wires that obey its gates, its
last wire is 1 exactly if the digit wires write the number s (`compareGates_spec`); its gates read
earlier wires only (`wfa_compareGates`). -/

public section

namespace SizeCircuit

open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

/-! ### Numbers and their digits -/

/-- Digit i of the number with the digits b 0, …, b (L − 1) is b i. -/
theorem testBit_num (b : ℕ → Bool) (L i : ℕ) (hi : i < L) : (num b L).testBit i = b i := by
  have h1 : toWord L (num b L) = (List.range L).map b := by
    have h := toWord_ofWord ((List.range L).map b)
    rw [List.length_map, List.length_range] at h
    exact h
  rw [← getD_toWord hi, h1, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi), List.getElem_map, List.getElem_range]

/-- The digits b 0, …, b (L − 1) write s exactly if s has at most L digits and these are its digits. -/
theorem num_eq_iff (b : ℕ → Bool) (L s : ℕ) : num b L = s ↔ s < 2 ^ L ∧ ∀ i < L, b i = s.testBit i := by
  constructor
  · rintro rfl
    exact ⟨num_lt b L, fun i hi => (testBit_num b L i hi).symm⟩
  · rintro ⟨h1, h2⟩
    rw [num_congr h2, num_testBit, Nat.mod_eq_of_lt h1]

/-! ### The gates -/

/-- The gate with a constant value. -/
theorem gval_const (v : ℕ → Bool) (c : Prop) [Decidable c] (i j : ℕ) : gval v ((if c then opOne else opZero), i, j) = decide c := by
  by_cases h : c
  · rw [if_pos h, gval_one, decide_eq_true h]
  · rw [if_neg h, gval_zero, decide_eq_false h]

/-- The gate "the wire i, and the wire j has the value t". -/
theorem gval_digit (v : ℕ → Bool) (t : Bool) (i j : ℕ) : gval v ((if t then opAnd else opAndN), i, j) = (v i && (v j == t)) := by
  cases t
  · rw [if_neg Bool.false_ne_true, gval_andN]
    cases v i <;> cases v j <;> rfl
  · rw [if_pos rfl, gval_and]
    cases v i <;> cases v j <;> rfl

/-- The comparison has one gate for each digit and one more. -/
theorem length_compareGates (N s : ℕ) (digits : List ℕ) : (compareGates N s digits).length = digits.length + 1 := by
  simp [compareGates]

/-- In the chain that begins at the wire N + 1 and starts from the wire N, the wire before place i
is N + i. -/
private theorem prevW_eq (N i : ℕ) : prevW (N + 1) N i = N + i := by
  unfold prevW
  split_ifs <;> omega

/-- **The comparison.** Under values v of the wires that obey the gates of the comparison, its last
wire is 1 exactly if the digit wires write the number s. -/
theorem compareGates_spec (v : ℕ → Bool) (N s : ℕ) (digits : List ℕ) (h : Obeys v N (compareGates N s digits)) :
    v (N + digits.length) = decide (ofWord (digits.map v) = s) := by
  obtain ⟨h0, h1⟩ : v N = gval v ((if s < 2 ^ digits.length then opOne else opZero), 0, 0) ∧
      Obeys v (N + 1) ((List.range digits.length).map fun i => ((if s.testBit i then opAnd else opAndN), N + i, digits.getD i 0)) := h
  rw [gval_const] at h0
  rw [obeys_map] at h1
  have hc := chain_all v (N + 1) N digits.length (fun i => v (digits.getD i 0) == s.testBit i)
    (fun i hi => by rw [h1 i hi, gval_digit, prevW_eq]) digits.length le_rfl
  rw [prevW_eq, h0] at hc
  have hm : digits.map v = (List.range digits.length).map fun i => v (digits.getD i 0) := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < digits.length := by simpa using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi]
  rw [hc, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [hm]
  exact (num_eq_iff (fun i => v (digits.getD i 0)) digits.length s).symm

/-- The gates of the comparison read earlier wires only, if there is a wire 0 and the digit wires
exist. -/
theorem wfa_compareGates {N s : ℕ} {digits : List ℕ} (hN : 0 < N) (hd : ∀ x ∈ digits, x < N) : WFa N (compareGates N s digits) := by
  refine ⟨⟨hN, hN⟩, (wfa_map (N + 1) _ digits.length).2 fun i hi => ⟨?_, ?_⟩⟩
  · show N + i < N + 1 + i
    omega
  · show digits.getD i 0 < N + 1 + i
    rw [List.getD_eq_getElem _ _ hi]
    have := hd _ (List.getElem_mem hi)
    omega

end SizeCircuit
