/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.GroupingDefs
import Printed.GroupingEntry
import Eight.ViaGrouping.Search
import Mathlib.Tactic

/-! # The numbers K, g, P, B, U, L and B' of the input

The procedure reads K, g, P, B and the numbers c_{a,b} off its input and computes U, L and B' from
them. On the input that belongs to ζ = a/b, K and a network N with parameters P, B these are the
numbers of Lemma 8 (Appendix A) of the paper:

* `inK_groupingInput`, `inG_groupingInput`, `inP_groupingInput`, `inB_groupingInput`,
  `inU_groupingInput`: K, g, P, B and the total U of N;
* `lbLen_groupingInput`: the number of bits between two groups that the test forms is Y_{γ,γ'};
* `ceil_div_nat`: ⌈n/d⌉ as a quotient of natural numbers;
* `labelLengthIsL`: the number computed is L = ⌈(U + 2ζgP)/K²⌉, and `Printed.bitsOut` is B'. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)

/-- The K of the input. -/
theorem inK_groupingInput : inK (groupingInput a b K N P B) = K := List.length_replicate

/-- The g of the input. -/
theorem inG_groupingInput : inG (groupingInput a b K N P B) = g := List.length_replicate

/-- The P of the input. -/
theorem inP_groupingInput : inP (groupingInput a b K N P B) = P := List.length_replicate

/-- The B of the input. -/
theorem inB_groupingInput : inB (groupingInput a b K N P B) = B := List.length_replicate

variable {P B}

/-- The sum of the numbers c_{a,b} of the input is the total U. -/
theorem inU_groupingInput (hN : N.Is P B) : inU (groupingInput a b K N P B) = N.U := by
  unfold inU
  rw [inG_groupingInput]
  have h := Uc_eq_U (asked_isNetworkP N hN)
  exact h

/-- The number of bits between two groups that the test forms from the input is Y_{γ,γ'}. -/
theorem lbLen_groupingInput (hK0 : 0 < K) (hN : N.Is P B) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g askedData.under.toPaperNetwork (groupingInput a b K N P B).2 x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' :=
  lbLen_eq_Y hK0 (asked_isNetworkP N hN) x hne

/-- ⌈n/d⌉ = ⌊(n + d − 1)/d⌋ for natural numbers n and d ≥ 1. -/
private theorem ceil_div_nat (n d : ℕ) (hd : 0 < d) : ⌈(n : ℝ) / d⌉₊ = (n + d - 1) / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈(n : ℝ) / d⌉₊ := ⟨_, rfl⟩
  rw [← hq]
  apply le_antisymm
  · rw [hq, Nat.ceil_le, div_le_iff₀ hdr]
    have h := Nat.div_add_mod (n + d - 1) d
    have h' := Nat.mod_lt (n + d - 1) hd
    have h2 : n ≤ d * ((n + d - 1) / d) := by omega
    calc (n : ℝ) ≤ ((d * ((n + d - 1) / d) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = _ := by rw [Nat.cast_mul, mul_comm]
  · have h1 : (n : ℝ) / d ≤ q := hq ▸ Nat.le_ceil _
    rw [div_le_iff₀ hdr] at h1
    have h2 : n ≤ q * d := by exact_mod_cast h1
    exact Nat.lt_succ_iff.1 (Nat.div_lt_of_lt_mul (calc n + d - 1 < q * d + d := by omega
      _ = d * (q + 1) := by ring))

/-- The number that the procedure computes, written out. -/
theorem labelLength_groupingInput (hN : N.Is P B) :
    labelLength (groupingInput a b K N P B) = (b * N.U + 2 * min a b * g * P + b * K ^ 2 - 1) / (b * K ^ 2) := by
  unfold labelLength
  rw [inU_groupingInput a b K N hN, inG_groupingInput, inP_groupingInput, inK_groupingInput]
  rfl

/-- The number computed is the L of Lemma 8, and `Printed.bitsOut` is its B'. -/
theorem labelLengthIsL : LabelLengthIsL := by
  intro a b K g N P B hb hab hK hN
  refine ⟨?_, ?_⟩
  · have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hd : 0 < b * K ^ 2 := by positivity
    have e : ((N.U : ℝ) + 2 * ((a : ℝ) / b) * g * P) / (K : ℝ) ^ 2 = ((b * N.U + 2 * a * g * P : ℕ) : ℝ) / ((b * K ^ 2 : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [labelLength_groupingInput a b K N hN, min_eq_left hab, AppRunningTime.Lof, e, ceil_div_nat _ _ hd]
  · unfold bitsOut AppRunningTime.B'of
    have h : 2 * g * P + K - 1 = 2 * (g * P) + (K - 1) := by
      have := Nat.mul_assoc 2 g P
      omega
    rw [h]

end ExplicitCost
