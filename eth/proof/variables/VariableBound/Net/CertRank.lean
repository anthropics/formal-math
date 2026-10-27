/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Rank
public import ClauseBound.ParityChecks.CertLib

/-! # Step 3 of Appendix D: the position of a string is found in polynomial time

In Step 3 of Appendix D, counting marks, multiplying powers of 2 and finding the position of a
string among those with as many ones take τ = n^O(1) operations. Proved here (`stCertRank`):
binomial coefficients of numbers given in
unary, the position `rank` of a string, and the number `cw` = ⌈log C(t, μ)⌉ of bits of a position,
in unary, are polynomial-time (`PolyT`, `Unary`).
The position is computed by a fold from the right whose state is the part of the string read so far
together with its position. -/

public section

namespace VariableBound.Net

open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib

namespace CertRank

/-- One step of the fold: put the bit b in front of the string c.1, whose position is c.2. -/
def stepR (b : Bool) (c : List Bool × ℕ) : List Bool × ℕ := (b :: c.1, (bif b then c.1.length.choose (c.1.count true + 1) else 0) + c.2)

/-- The fold yields the string and its position. -/
theorem foldr_stepR (x : List Bool) : x.foldr stepR ([], 0) = (x, rank x) := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [List.foldr_cons, ih]; rfl

/-- One step of the fold is polynomial-time. -/
theorem stepR_polyT : PolyT fun p : Bool × List Bool × ℕ => stepR p.1 p.2 := by
  have h1 : Unary fun p : Bool × List Bool × ℕ => p.2.1.count true + 1 := by
    have h : Unary fun p : Bool × List Bool × ℕ => (p.2.1.filter fun e => e == true).length + 1 := by fun_prop
    exact unary_congr h fun p => by rw [List.count, List.countP_eq_length_filter]
  have h2 : PolyT fun p : Bool × List Bool × ℕ => p.2.1.length.choose (p.2.1.count true + 1) := choose_polyT (by fun_prop) h1
  unfold stepR
  fun_prop

/-- The word of the position of a string is at most as long as the word of the string. -/
theorem len_rank_le (x : List Bool) : len (rank x) ≤ len x := by
  rw [len_nat, len_bools]
  have h : Nat.size (rank x) ≤ x.length := by
    rw [Nat.size_le]
    exact (Rank.rank_lt x).trans_le (Nat.choose_le_two_pow _ _)
  omega

/-- The position of a string among the strings of its length with as many ones is polynomial-time. -/
theorem rank_polyT : PolyT rank := by
  have h : PolyT fun x : List Bool => x.foldr stepR ([], 0) := by
    refine PolyT.foldr (l := fun x : List Bool => x) (a := fun _ => (([] : List Bool), 0)) (g := fun _ b c => stepR b c) (by fun_prop) (by fun_prop)
      (PolyT.comp (g := fun p : List Bool × Bool × List Bool × ℕ => p.2) stepR_polyT (by fun_prop))
      ⟨fun n => n + n + 2, (PB.id'.add PB.id').add (PB.const 2), fun x k => ?_⟩
    rw [foldr_stepR, len_pair]
    have h1 := len_rank_le (x.drop k)
    have h2 := len_drop_le x k
    change _ ≤ len x + len x + 2
    omega
  exact (PolyT.snd h).congr fun x => by rw [foldr_stepR]

/-- C(t, μ) does not change if μ is cut off at t + 1. -/
theorem choose_min (t μ : ℕ) : t.choose (min μ (t + 1)) = t.choose μ := by
  rcases Nat.le_total μ (t + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]

end CertRank

open CertRank

/-- Step 3 of Appendix D: binomial coefficients C(t, μ) are polynomial-time for t and μ given in
unary; the position of a string among those with as many ones is polynomial-time; and ⌈log C(t, μ)⌉
is
given in unary for t given in unary and μ polynomial-time. -/
theorem stCertRank : StCertRank := by
  refine ⟨fun α _ t μ ht hμ => choose_polyT ht.poly hμ, rank_polyT, fun α _ t μ ht hμ => ?_⟩
  have h1 : Unary fun x => min (μ x) (t x + 1) := unary_min_right hμ (ht.add (Unary.const 1))
  have h2 : PolyT fun x => (t x).choose (min (μ x) (t x + 1)) := choose_polyT ht.poly h1
  unfold cw
  exact clog_unary (h2.congr fun x => choose_min _ _)

end VariableBound.Net
