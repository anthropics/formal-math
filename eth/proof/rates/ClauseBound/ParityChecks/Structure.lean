/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-! # What a potential below 1 gives

The potential is a sum of four nonnegative terms, so each of them is below 1 if the potential is.
`structure_` reads off the three bounds on the checks chosen so far: on the number of
pairs (check, clause in it), on the size of every check and on the number of checks that contain a
given clause; the last two in the form 2^(number) < …, before logarithms are taken.
`final` says that in the final state the first term is a nonnegative integer, hence 0, and that this
makes the checks good. That the four terms are nonnegative is a hypothesis of
both theorems. -/

public section

open Finset ParityChecks

namespace ClauseBound.ParityChecks.Structure

variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-- p = 1/nb is positive. -/
theorem pr_pos {nb : ℕ} (h : 2 ≤ nb) : 0 < pr nb := by
  have : (0 : ℚ) < nb := by exact_mod_cast (by omega : 0 < nb)
  unfold pr
  positivity

/-- From (1/c)·S < 1, for a sum S of nonnegative terms a_i/b_i with 0 < b_i ≤ B: every a_i is below
c·B. -/
theorem lt_of_sum_lt {ι : Type} (s : Finset ι) (a b : ι → ℚ) (c B : ℚ) (hc : 0 < c) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hB : ∀ i ∈ s, b i ≤ B) (h : 1 / c * ∑ i ∈ s, a i / b i < 1) {i : ι} (hi : i ∈ s) : a i < c * B := by
  have h1 : a i / b i ≤ ∑ i ∈ s, a i / b i :=
    single_le_sum (f := fun i => a i / b i) (fun k hk => div_nonneg (ha k hk) (hb k hk).le) hi
  have h2 : ∑ i ∈ s, a i / b i < c := by
    rwa [one_div, inv_mul_lt_iff₀ hc, mul_one] at h
  have h3 : a i < c * b i := (div_lt_iff₀ (hb i hi)).1 (h1.trans_lt h2)
  exact h3.trans_le (mul_le_mul_of_nonneg_left (hB i hi) hc.le)

/-- What Υ < 1 gives in any state: fewer than 8pmr pairs, 2^|Λ_j'| < 8r(1 + p)^m for every check,
and 2^load(e) < 8m(1 + p)^r for every clause e, where load(e) is the number of checks j' < r that
contain e. -/
theorem structure_ (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E)
    (hnn : 0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D)
    (hnb : 2 ≤ nb) (hE : 1 ≤ Fintype.card E) (hs : IsState r j Λ D) (hU : Ups V nb r j Λ D < 1) :
    ((∑ j' ∈ range r, #(Λ j') : ℕ) : ℚ) < 8 * pr nb * Fintype.card E * r ∧
    (∀ j' < r, (2 : ℚ) ^ #(Λ j') < 8 * r * (1 + pr nb) ^ Fintype.card E) ∧
    ∀ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} < 8 * Fintype.card E * (1 + pr nb) ^ r := by
  obtain ⟨n1, n2, n3, n4⟩ := hnn
  have hp := pr_pos hnb
  have hr : (0 : ℚ) < r := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le j) hs.j_lt
  have hm : (0 : ℚ) < Fintype.card E := by exact_mod_cast hE
  have h1p : (1 : ℚ) ≤ 1 + pr nb := by linarith
  unfold Ups at hU
  have u2 : Uinc nb r j Λ D < 1 := by linarith
  have u3 : Urow nb r j Λ D < 1 := by linarith
  have u4 : Ucol nb r j Λ D < 1 := by linarith
  refine ⟨?_, fun j' hj' => ?_, fun e => ?_⟩
  · unfold Uinc at u2
    rw [div_lt_one (by positivity)] at u2
    have : 0 ≤ pr nb * ((∑ j' ∈ range r, undRow j D j' : ℕ) : ℚ) := by positivity
    linarith
  · exact lt_of_sum_lt (range r) (fun j' => (2 : ℚ) ^ #(Λ j')) (fun j' => (1 + pr nb) ^ (Fintype.card E - undRow j D j')) (8 * r) _
      (by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
      (fun _ _ => pow_le_pow_right₀ h1p (Nat.sub_le _ _)) u3 (mem_range.2 hj')
  · exact lt_of_sum_lt univ (fun e => (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'}) (fun e => (1 + pr nb) ^ (r - undCol r j D e))
      (8 * Fintype.card E) _ (by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
      (fun _ _ => pow_le_pow_right₀ h1p (Nat.sub_le _ _)) u4 (mem_univ e)

/-- ½(1 + (−1)^q) = [q even]. -/
theorem half_eq (q : ℕ) : (1 / 2 : ℚ) * (1 + (-1) ^ q) = (ev q : ℚ) := by
  unfold ev
  rcases Nat.even_or_odd q with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.2 h)]; norm_num

theorem ev_nonneg (q : ℕ) : 0 ≤ ev q := by
  unfold ev
  split_ifs <;> norm_num

omit [Fintype E] in
/-- In the final state the first term of the potential is the integer Σ_ξ ω(ξ)·∏_{j' < r} [|V_j'(ξ)|
even]. -/
theorem Upar_final (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) :
    Upar V nb (r + 1) r Λ ∅ = ((∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) : ℤ) : ℚ) := by
  unfold Upar
  rw [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  push_cast
  refine sum_congr rfl fun ξ _ => ?_
  rw [empty_inter, card_empty, pow_zero, mul_one, half_eq, prod_range_succ, mul_assoc]

/-- In the final state Υ < 1 makes the checks good. -/
theorem final (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E)
    (hnn : 0 ≤ Upar V nb r (r - 1) Λ ∅ ∧ 0 ≤ Uinc nb r (r - 1) Λ (∅ : Finset E) ∧ 0 ≤ Urow nb r (r - 1) Λ (∅ : Finset E) ∧
      0 ≤ Ucol nb r (r - 1) Λ (∅ : Finset E))
    (hs : IsState r (r - 1) Λ (∅ : Finset E)) (hU : Ups V nb r (r - 1) Λ ∅ < 1) : Good V nb r Λ := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hs.j_lt; omega⟩
  rw [Nat.add_sub_cancel] at hnn hU
  obtain ⟨-, n2, n3, n4⟩ := hnn
  have u1 : Upar V nb (r + 1) r Λ ∅ < 1 := by
    unfold Ups at hU
    linarith
  rw [Upar_final] at u1
  have hterm : ∀ ξ ∈ (univ : Finset X), 0 ≤ (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) := fun ξ _ =>
    mul_nonneg (Int.natCast_nonneg _) (prod_nonneg fun _ _ => ev_nonneg _)
  have h0 : ∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) = 0 := by
    have h1 : ∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) < 1 := by exact_mod_cast u1
    have h2 := sum_nonneg hterm
    omega
  intro ξ hξ
  by_contra hno
  have h1 := (sum_eq_zero_iff_of_nonneg hterm).1 h0 ξ (mem_univ ξ)
  have h2 : ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) = 1 := prod_eq_one fun j' hj' => by
    have : Even #(Λ j' ∩ V ξ) := Nat.not_odd_iff_even.1 fun ho => hno ⟨j', mem_range.1 hj', ho⟩
    rw [ev, if_pos this]
  have h3 : 0 < omega V nb ξ := Nat.choose_pos hξ
  rw [h2, mul_one] at h1
  omega

end ClauseBound.ParityChecks.Structure
