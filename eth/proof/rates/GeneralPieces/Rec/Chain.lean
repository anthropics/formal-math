/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Defs
public import GeneralPieces.Num.PartA
public import ClauseBound.Gen.Chain
public import ClauseBound.Gen.Rate
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The schedule (40) is a chain of steps that are in order, through case (ii)

This follows the step from ℓ to ℓ+1 in the proof of part (b) of the theorem on the general recursion
(Appendix A), from the display for U = min(U_row, U_col) to the display for K²L, sentence by
sentence; most
theorems quote their sentence. Throughout K, g, ζ are K_ℓ, g_ℓ, ζ_ℓ and N = g⁴λ. The end is
`stChain2`: for pieces with parameters (ρ, c) whose numbers of bits are at most 2λ, and every x₀ ≥
18,
every step g_ℓ·g_ℓ → K_ℓ of the schedule satisfies `LevelOK2` at every label length λ ≥ 1.
Differences from the paper: the program uses one label length for all patterns ι of a level,
computed from an upper bound `ubarG` for U = min(U_row, U_col), where the paper's L depends
on ι; it is ⌊·⌋ + 1 where the paper has ⌈·⌉. The hypothesis 2^x₀ ≥ c + 5 of the theorem is not used
in this file. -/

public section

namespace GeneralPieces.Chain

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen

variable {P : PiecesF} {ρ : ℝ} {c : ℕ}

/-! ### The display for U = min(U_row, U_col) -/

/-- The network that the program takes on a square grid is "the network with the smaller total": its
total is min(U_row, U_col). -/
theorem total_eq_min (P : PiecesF) (a h lam y : ℕ) :
    totalG P a a (decide (totalG P a a true h lam y < totalG P a a false h lam y)) h lam y =
      min (totalG P a a false h lam y) (totalG P a a true h lam y) := by
  by_cases hlt : totalG P a a true h lam y < totalG P a a false h lam y
  · rw [decide_eq_true hlt, min_eq_right hlt.le]
  · rw [decide_eq_false hlt, min_eq_left (not_lt.1 hlt)]

/-- The program's upper bound for U at level ℓ, written out: g(g−1)·gλ + |R|·max_i (c_i^row +
c_i^col). -/
theorem ubar_eq (P : PiecesF) (x₀ l lam : ℕ) :
    ubarG P (step P x₀ l) lam = g x₀ l * (g x₀ l - 1) * g x₀ l * lam + nRectG (g x₀ l) (g x₀ l) * capSum P 0 lam := by
  simp [ubarG, step_p, step_d, step_h, step_thin]

/-- U = min(U_row, U_col) is at most the program's upper bound: the minimum is at most the average. -/
theorem U_le_ubar (hP : Par P ρ c) (x₀ l lam y : ℕ) (hlam : 1 ≤ lam) :
    min (totalG P (g x₀ l) (g x₀ l) false 0 lam y) (totalG P (g x₀ l) (g x₀ l) true 0 lam y) ≤ ubarG P (step P x₀ l) lam := by
  rw [← total_eq_min, ubar_eq]
  exact ClauseBound.Gen.Chain.total_min_le P (g x₀ l) 0 lam y (hP.spec 0 lam hlam).cnt_pos

/-- First inequality of the display, "U ≤ N/g + |R|(4ρλ + c log(2λ))", for the program's upper
bound. -/
theorem ubar_le_first (hP : Par P ρ c) (x₀ l lam : ℕ) (hx : 18 ≤ x₀) (hlam : 1 ≤ lam) :
    (ubarG P (step P x₀ l) lam : ℝ) ≤ (g x₀ l : ℝ) ^ 4 * lam / g x₀ l +
      nRectG (g x₀ l) (g x₀ l) * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by
  have hg : (0 : ℝ) < g x₀ l := by
    have := pow_le_g hx l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have hs : ((g x₀ l * (g x₀ l - 1) * g x₀ l * lam : ℕ) : ℝ) ≤ (g x₀ l : ℝ) ^ 3 * lam := by
    have : g x₀ l * (g x₀ l - 1) * g x₀ l * lam ≤ g x₀ l ^ 3 * lam := by
      calc g x₀ l * (g x₀ l - 1) * g x₀ l * lam ≤ g x₀ l * g x₀ l * g x₀ l * lam := by gcongr; exact Nat.sub_le _ _
        _ = g x₀ l ^ 3 * lam := by ring
    exact_mod_cast this
  have e1 : (g x₀ l : ℝ) ^ 4 * lam / g x₀ l = (g x₀ l : ℝ) ^ 3 * lam := by field_simp
  rw [ubar_eq, e1, Nat.cast_add, Nat.cast_mul (nRectG _ _)]
  exact add_le_add hs (mul_le_mul_of_nonneg_left (hP.caps 0 lam hlam) (Nat.cast_nonneg _))

/-- Second inequality of the display, "N/g + |R|(4ρλ + c log(2λ)) ≤ N(ρ + 1/g) + (c/4)g⁴ log(2λ)":
there are at most g⁴/4 rectangles. -/
theorem ubar_le_second (hP : Par P ρ c) (x₀ l lam : ℕ) (hlam : 1 ≤ lam) :
    (g x₀ l : ℝ) ^ 4 * lam / g x₀ l + nRectG (g x₀ l) (g x₀ l) * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) ≤
      (g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / g x₀ l) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) := by
  have hR : (nRectG (g x₀ l) (g x₀ l) : ℝ) ≤ (g x₀ l : ℝ) ^ 4 / 4 := by
    have : ((4 * nRectG (g x₀ l) (g x₀ l) : ℕ) : ℝ) ≤ ((g x₀ l ^ 4 : ℕ) : ℝ) := by exact_mod_cast four_nRect_le (g x₀ l)
    push_cast at this
    linarith
  have h0 : 0 ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := le_trans (Nat.cast_nonneg _) (hP.caps 0 lam hlam)
  have h1 := mul_le_mul_of_nonneg_right hR h0
  have e1 : (g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / g x₀ l) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) =
      (g x₀ l : ℝ) ^ 4 * lam / g x₀ l + (g x₀ l : ℝ) ^ 4 / 4 * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by ring
  rw [e1]
  exact add_le_add_right h1 _

/-! ### "Case (ii) of the lemma applies to the network with the smaller total" -/

/-- "K divides g". -/
theorem K_dvd_g (x₀ l : ℕ) : K x₀ l ∣ g x₀ l := Dvd.intro_left _ rfl

/-- "2ζ²g = 2^{ℓ+x₀−9}K". -/
theorem two_zeta_sq_g (x₀ l : ℕ) (hx : 9 ≤ x₀) : 2 * zeta l ^ 2 * (g x₀ l : ℝ) = 2 ^ (l + x₀ - 9) * K x₀ l := by
  have hg : (g x₀ l : ℝ) = 2 ^ (3 * l + x₀) * K x₀ l := by rw [g]; push_cast; rfl
  obtain ⟨t, rfl⟩ : ∃ t, x₀ = t + 9 := ⟨x₀ - 9, by omega⟩
  have e1 : l + (t + 9) - 9 = l + t := by omega
  have e2 : (2 : ℝ) ^ (3 * l + (t + 9)) = 2 ^ (l + t) * 2 ^ 9 * (2 ^ l) ^ 2 := by ring
  rw [hg, zeta, e1, e2, pow_add 2 l 5]
  field_simp

/-- "2gK ≤ g² = K_{ℓ+1}". -/
theorem two_gK_le (x₀ l : ℕ) (hx : 1 ≤ x₀) : 2 * g x₀ l * K x₀ l ≤ K x₀ (l + 1) := by
  have h : 2 * K x₀ l ≤ g x₀ l := by
    unfold g
    refine Nat.mul_le_mul_right _ ?_
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (3 * l + x₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 * g x₀ l * K x₀ l = g x₀ l * (2 * K x₀ l) := by ring
    _ ≤ g x₀ l * g x₀ l := Nat.mul_le_mul_left _ h
    _ = K x₀ (l + 1) := by rw [K_succ, sq]

/-- "ln(2gK) ≤ 0.7 log K_{ℓ+1}". -/
theorem log_two_gK_le (x₀ l : ℕ) (hx : 18 ≤ x₀) : Real.log (2 * g x₀ l * K x₀ l) ≤ 0.7 * Real.logb 2 (K x₀ (l + 1)) := by
  have h1 : (2 : ℝ) * g x₀ l * K x₀ l ≤ K x₀ (l + 1) := by exact_mod_cast two_gK_le x₀ l (by omega)
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have hg : (0 : ℝ) < g x₀ l := by
    have := pow_le_g hx l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have h2 := Real.log_le_log (by positivity) h1
  have h3 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  rw [logb_K]
  rw [K_cast x₀ (l + 1), Real.log_pow] at h2
  have h4 : (x x₀ (l + 1) : ℝ) * Real.log 2 ≤ x x₀ (l + 1) * 0.7 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  linarith

/-- "0.7 log K_{ℓ+1} ≤ 1.4 (3x₀+6) 2^ℓ". -/
theorem logK_succ_le (x₀ l : ℕ) : 0.7 * Real.logb 2 (K x₀ (l + 1)) ≤ 1.4 * (3 * x₀ + 6) * 2 ^ l := by
  have h1 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have h2 : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg x₀
  rw [PartA.logK_formula, pow_succ]
  push_cast
  linarith

/-- "1.4 (3x₀+6) ≤ 2^{x₀−9} for x₀ ≥ 18". -/
theorem num_le (x₀ : ℕ) (hx : 18 ≤ x₀) : 1.4 * (3 * (x₀ : ℝ) + 6) ≤ 2 ^ (x₀ - 9) := by
  have h1 := pow_x₀ x₀ hx
  have e : 2 ^ x₀ = 2 ^ (x₀ - 9) * 2 ^ 9 := by rw [← pow_add]; congr 1; omega
  rw [e] at h1
  have h2 : 2 * (3 * x₀ + 6) ≤ 2 ^ (x₀ - 9) := by
    generalize 2 ^ (x₀ - 9) = w at h1 ⊢
    omega
  have h3 : ((2 * (3 * x₀ + 6) : ℕ) : ℝ) ≤ ((2 ^ (x₀ - 9) : ℕ) : ℝ) := Nat.cast_le.2 h2
  push_cast at h3
  have h4 : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _
  linarith

/-- The condition 2ζ²g ≥ K·ln(2gK) of case (ii) holds at every level, by the four sentences above. -/
theorem hoeffding_cond (x₀ l : ℕ) (hx : 18 ≤ x₀) : (K x₀ l : ℝ) * Real.log (2 * g x₀ l * K x₀ l) ≤ 2 * zeta l ^ 2 * g x₀ l := by
  rw [two_zeta_sq_g x₀ l (by omega), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc Real.log (2 * g x₀ l * K x₀ l) ≤ 0.7 * Real.logb 2 (K x₀ (l + 1)) := log_two_gK_le x₀ l hx
    _ ≤ 1.4 * (3 * x₀ + 6) * 2 ^ l := logK_succ_le x₀ l
    _ ≤ 2 ^ (x₀ - 9) * 2 ^ l := mul_le_mul_of_nonneg_right (num_le x₀ hx) (by positivity)
    _ = 2 ^ (l + x₀ - 9) := by rw [← pow_add]; congr 1; omega

/-- "ζg = 2^{2ℓ+x₀−5}K". -/
theorem zeta_mul_g (x₀ l : ℕ) (hx : 5 ≤ x₀) : zeta l * (g x₀ l : ℝ) = 2 ^ (2 * l + x₀ - 5) * K x₀ l := by
  have hg : (g x₀ l : ℝ) = 2 ^ (3 * l + x₀) * K x₀ l := by rw [g]; push_cast; rfl
  obtain ⟨t, rfl⟩ : ∃ t, x₀ = t + 5 := ⟨x₀ - 5, by omega⟩
  have e1 : 2 * l + (t + 5) - 5 = 2 * l + t := by omega
  have e2 : (2 : ℝ) ^ (3 * l + (t + 5)) = 2 ^ (2 * l + t) * 2 ^ (l + 5) := by ring
  rw [hg, zeta, e1, e2]
  field_simp

/-- "Also 1/g ≤ ζ". -/
theorem inv_g_le_zeta (x₀ l : ℕ) (hx : 18 ≤ x₀) : 1 / (g x₀ l : ℝ) ≤ zeta l := by
  have hg : (0 : ℝ) < g x₀ l := by
    have := pow_le_g hx l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have hK : (1 : ℝ) ≤ K x₀ l := by
    have := big_le_K hx l
    exact_mod_cast (by omega : 1 ≤ K x₀ l)
  rw [div_le_iff₀ hg, zeta_mul_g x₀ l (by omega)]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hK

/-- ζ of the step at level ℓ is ζ_ℓ = 2^{−ℓ−5}. -/
theorem zetaOf_step (hm : P.m = 1) (x₀ l : ℕ) : zetaOf (step P x₀ l) = zeta l := by
  rw [zetaOf, step_D, hm, zeta, pow_succ 2 (l + 4)]
  push_cast
  field_simp

/-! ### The display for K²L -/

/-- First inequality of the display, "K²L ≤ U + 2ζN + K²", for the program's label length one level
down and its upper bound for U. -/
theorem K_sq_L_le_first (hm : P.m = 1) (x₀ l lam : ℕ) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤
      ubarG P (step P x₀ l) lam + 2 * zeta l * ((g x₀ l : ℝ) ^ 4 * lam) + (K x₀ l : ℝ) ^ 2 := by
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have hdiv := Nat.cast_div_le (α := ℝ)
    (m := (step P x₀ l).D * ubarG P (step P x₀ l) lam + 3 * (step P x₀ l).p ^ 2 * ((step P x₀ l).d ^ 2 * (P.m * lam)))
    (n := (step P x₀ l).D * (step P x₀ l).K ^ 2)
  have e : (2 : ℝ) * zeta l = 1 / 2 ^ (l + 4) := by
    rw [zeta, pow_succ (2 : ℝ) (l + 4)]; field_simp
  rw [lamNextG, Nat.cast_add, Nat.cast_one, mul_add, mul_one, e]
  refine add_le_add_left ?_ _
  refine (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans (le_of_eq ?_)
  rw [step_D, step_K, step_p, step_d, hm]
  push_cast
  field_simp

/-- The display "K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴ log(2λ) + K²". -/
theorem K_sq_L_le (hP : Par P ρ c) (hm : P.m = 1) (x₀ l lam : ℕ) (hx : 18 ≤ x₀) (hlam : 1 ≤ lam) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤
      (ρ + 3 * zeta l) * ((g x₀ l : ℝ) ^ 4 * lam) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) + (K x₀ l : ℝ) ^ 2 := by
  have h1 := K_sq_L_le_first hm x₀ l lam
  have h2 := (ubar_le_first hP x₀ l lam hx hlam).trans (ubar_le_second hP x₀ l lam hlam)
  have h3 : (g x₀ l : ℝ) ^ 4 * lam * (1 / g x₀ l) ≤ (g x₀ l : ℝ) ^ 4 * lam * zeta l :=
    mul_le_mul_of_nonneg_left (inv_g_le_zeta x₀ l hx) (by positivity)
  linarith

/-! ### The schedule -/

/-- Every step of the schedule is in order at every label length. -/
theorem levelOK2 (hP : Par P ρ c) (hm : P.m = 1) (x₀ : ℕ) (hx : 18 ≤ x₀) (l lam : ℕ) (hlam : 1 ≤ lam) : LevelOK2 P (step P x₀ l) lam := by
  have hK2 : 2 ≤ K x₀ l := by have := big_le_K hx l; omega
  refine ⟨by rw [step_h]; exact hP.spec 0 lam hlam, by rw [step_K]; exact hK2, by rw [step_p]; exact hK2.trans (K_le_g x₀ l), ?_,
    by rw [step_K, step_p]; exact K_dvd_g x₀ l, by rw [zetaOf_step hm, step_K, step_p]; exact hoeffding_cond x₀ l hx,
    fun _ => by rw [step_p, step_d], fun h => ?_, fun y _ _ => ?_, fun y _ h => ?_⟩
  · rw [step_D, hm]
    have : 1 ≤ 2 ^ (l + 4) := Nat.one_le_two_pow
    omega
  · rw [step_thin] at h; exact absurd h (by decide)
  · have h := U_le_ubar hP x₀ l lam y hlam
    rw [← total_eq_min] at h
    simp only [step_thin, Bool.not_false, Bool.true_and]
    unfold colSide
    simp only [step_thin, Bool.false_eq_true, if_false, step_p, step_d, step_h]
    exact h
  · rw [step_thin] at h; simp at h

/-- `StChain2`: the schedule (40) is a chain of steps g_ℓ·g_ℓ → K_ℓ that ends at K₀ nodes, and every
step is in order at its label length. -/
theorem stChain2 : StChain2 := by
  intro P ρ c x₀ hP hm hx₀ _ l
  induction l with
  | zero => intro lam _; rfl
  | succ l ih =>
    intro lam hlam
    refine ⟨?_, levelOK2 hP hm x₀ hx₀ l lam hlam, ?_⟩
    · rw [step_p, step_d, K_succ, sq]
    · rw [step_K]
      exact ih _ (Nat.le_add_left 1 _)

end GeneralPieces.Chain
