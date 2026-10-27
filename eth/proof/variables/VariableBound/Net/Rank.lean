/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs

/-! # Step 3, «The total»: ranks of subsets

«Within a profile, replace the string of the marks of the t_(a,b,κ) objects, in a fixed order, by
its position in the list of all strings of this length with μ_(a,b,κ) ones.» Proved here:

* `rank_lt`, `rank_inj`: the position is below C(t, μ), and two strings of the same length with as
  many ones and the same position are equal;
* `stLab`: the label that a shows to b has c_(a,b) bits, and the labels of two settings of the
  profile agree if and only if the two settings give the same marks to every object with the test
  {a, b}.
  With this, Ψ_(a,b) factors through c_(a,b) bits. -/

public section

namespace VariableBound.Net

open Groundwork Groundwork.Prog

namespace Rank

/-- A bit 0 in front does not change the number of ones. -/
theorem count_false_cons (x : List Bool) : (false :: x).count true = x.count true := by simp

/-- The position of a string is below the number C(t, μ) of strings of its length t with as many
ones, μ. -/
theorem rank_lt (x : List Bool) : rank x < x.length.choose (x.count true) := by
  induction x with
  | nil => simp [rank]
  | cons b x ih =>
    cases b with
    | false =>
      simp only [rank, cond_false, zero_add, List.length_cons]
      rw [count_false_cons]
      exact ih.trans_le (Nat.choose_le_succ _ _)
    | true =>
      simp only [rank, cond_true, List.length_cons, List.count_cons_self]
      rw [Nat.choose_succ_succ']
      omega

/-- Two strings of the same length with as many ones and the same position are equal. -/
theorem rank_inj (x x' : List Bool) (hl : x.length = x'.length) (hc : x.count true = x'.count true) (hr : rank x = rank x') : x = x' := by
  induction x generalizing x' with
  | nil => exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons b x ih =>
    cases x' with
    | nil => simp at hl
    | cons b' x' =>
      have hl' : x.length = x'.length := by simpa using hl
      have h1 := rank_lt x
      have h2 := rank_lt x'
      cases b <;> cases b' <;> simp only [rank, cond_false, cond_true, zero_add, List.count_cons_self, count_false_cons] at hc hr
      · rw [ih x' hl' hc hr]
      · -- x' begins with 1 and x with 0: the position of x' is at least C(t − 1, μ), that of x is below it
        rw [hl', hc] at h1
        omega
      · rw [← hl', ← hc] at h2
        omega
      · have hc' : x.count true = x'.count true := by omega
        rw [hl', hc'] at hr
        rw [ih x' hl' hc' (by omega)]

/-- The objects with the test {a, b} are those with the test {b, a}. -/
theorem tst_comm (g n : ℕ) (D : Dat) (a b κ : ℕ) : tst g n D a b κ = tst g n D b a κ := by
  unfold tst
  rw [min_comm, max_comm]

/-- μ_(a,b,κ) = μ_(b,a,κ). -/
theorem mu_comm (g : ℕ) (D : Dat) (y a b κ : ℕ) : mu g D y a b κ = mu g D y b a κ := by
  unfold mu
  rw [min_comm, max_comm]

/-- The string of marks has one bit for each object with the test. -/
theorem length_str (g n : ℕ) (D : Dat) (a b κ : ℕ) (z : List Bool) : (str g n D a b κ z).length = (tst g n D a b κ).length := by
  simp [str]

/-- The label is the word of kind 0 followed by the word of kind 1. -/
theorem labD_eq (g n : ℕ) (D : Dat) (y a b : ℕ) (z : List Bool) :
    labD g n D y a b z = toWord (cw (tst g n D a b 0).length (mu g D y a b 0)) (rank (str g n D a b 0 z))
      ++ toWord (cw (tst g n D a b 1).length (mu g D y a b 1)) (rank (str g n D a b 1 z)) := by
  simp [labD, List.range_succ]

/-- The position of a string of t bits with μ ones can be written with ⌈log C(t, μ)⌉ bits. -/
theorem rank_lt_two_pow (x : List Bool) (t μ : ℕ) (ht : x.length = t) (hμ : x.count true = μ) : rank x < 2 ^ cw t μ := by
  subst ht hμ
  exact (rank_lt x).trans_le (Nat.le_pow_clog (by norm_num) _)

/-- The words of ⌈log C(t, μ)⌉ bits of the positions of two strings of t bits with μ ones agree if
and only if the strings agree. -/
theorem toWord_rank_inj (x x' : List Bool) (t μ : ℕ) (ht : x.length = t) (ht' : x'.length = t) (hμ : x.count true = μ) (hμ' : x'.count true = μ) :
    toWord (cw t μ) (rank x) = toWord (cw t μ) (rank x') ↔ x = x' := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := congrArg ofWord h
  rw [ofWord_toWord (rank_lt_two_pow x t μ ht hμ), ofWord_toWord (rank_lt_two_pow x' t μ ht' hμ')] at h1
  exact rank_inj x x' (ht.trans ht'.symm) (hμ.trans hμ'.symm) h1

end Rank

open Rank

/-- Step 3, «The total»: the labels have c_(a,b) bits; two settings of the profile (the strings have
μ ones) have the same label if and only if they give the same marks to every object with the test
{a, b}. -/
theorem stLab : StLab := by
  refine ⟨fun g n D y a b z => ?_, fun g n D y a b z z' hz hz' => ?_⟩
  · simp [labD_eq, capD, List.range_succ]
  · rw [labD_eq, labD_eq, tst_comm g n D b a 0, tst_comm g n D b a 1, mu_comm g D y b a 0, mu_comm g D y b a 1]
    have e : ∀ κ < 2, (toWord (cw (tst g n D a b κ).length (mu g D y a b κ)) (rank (str g n D a b κ z))
        = toWord (cw (tst g n D a b κ).length (mu g D y a b κ)) (rank (str g n D b a κ z')) ↔ str g n D a b κ z = str g n D b a κ z') := fun κ hκ =>
      toWord_rank_inj _ _ _ _ (length_str g n D a b κ z) ((length_str g n D b a κ z').trans (by rw [tst_comm])) (hz κ hκ) (hz' κ hκ)
    constructor
    · intro h
      obtain ⟨h0, h1⟩ := List.append_inj h (by simp)
      intro κ hκ
      obtain rfl | rfl : κ = 0 ∨ κ = 1 := by omega
      · exact (e 0 hκ).1 h0
      · exact (e 1 hκ).1 h1
    · intro h
      rw [h 0 (by norm_num), h 1 (by norm_num)]

end VariableBound.Net
