/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
import PairsToBound.Arith
import SparsificationLemma.Cal.Alpha
import SparsificationLemma.Cal.Beta
import VariableBound.Paper.Arith
import VariableBound.Printed.VariablesA.Setting
import VariableBound.Params.Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-! # Theorem D (a) along the printed Step 5: the numbers

* `eps_between`: «Take ε ≤ 1 between e and 2e» (Step 5 of Appendix D): ε = min(a/b, 1) is such a
  number if a/b is in [e, 2e] and e ≤ 1.
* `occBoundIsThePrinted`: 2·(θ₀ + … + θ_(k−1)) + 2 ≤ 2·(8k/ε)^(3k) + 2, where θ₀, …, θ_(k−1) are the
  k thresholds of Calabro's sparsification algorithm that `thresholds` computes; from the two
  statements on these thresholds `SparsificationLemma.Cal.StDegSum` and
  `SparsificationLemma.Cal.StDegLe`.
* `boundsGrowWithDelta`: each of the four bounds is made of sums, products, powers and rounded
  logarithms of Δ with coefficients that are not negative.
* `cutOffIsIdle`: k ≤ k⁴ ≤ log n gives 2^k ≤ n.
* `outputsAreWithinTheSetting`: «so log Δ ≤ 3k·log(8k/e) + 2 … which is at most 4kC₀·log log n for
  large n». Here n is large if log log n ≥ 40 and n is at least the n₀ of «Setting and parameters»
  (`MainTheoremForms.SettingN0Stmt`), which gives Δ ≤ n^(1/(40C₀)) ≤ n. For the bound n ≥
  29·⌈log₂(2Δ)⌉ + 19: ⌈log₂(2Δ)⌉ ≤ log n + 2 and 30·log n ≤ n because (log n)³ ≤ n². -/

public section

namespace RecursionToBound

open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper

/-! ### ε -/

/-- ε > 0 for a fraction with positive numerator and denominator. -/
theorem epsOf_pos {r : ℕ × ℕ} (h1 : 0 < r.1) (h2 : 0 < r.2) : 0 < epsOf r := by
  unfold epsOf
  exact lt_min (by positivity) one_pos

/-- ε ≤ 1. -/
theorem epsOf_le_one (r : ℕ × ℕ) : epsOf r ≤ 1 := min_le_right _ _

/-- ε as a real number is min(a/b, 1). -/
theorem epsOf_cast (r : ℕ × ℕ) : ((epsOf r : ℚ) : ℝ) = min ((r.1 : ℝ) / r.2) 1 := by
  unfold epsOf
  push_cast
  rfl

/-- A fraction a/b that is at least e > 0 has a > 0 and b > 0. -/
theorem pos_of_le_div {r : ℕ × ℕ} {e : ℝ} (he : 0 < e) (h : e ≤ (r.1 : ℝ) / r.2) : 0 < r.1 ∧ 0 < r.2 := by
  have h0 : (0 : ℝ) < (r.1 : ℝ) / r.2 := lt_of_lt_of_le he h
  constructor
  · by_contra hh
    have h1 : r.1 = 0 := by omega
    rw [h1] at h0
    simp at h0
  · by_contra hh
    have h1 : r.2 = 0 := by omega
    rw [h1] at h0
    simp at h0

/-- «Take ε ≤ 1 between e and 2e»: if e ≤ a/b ≤ 2e and e ≤ 1, then e ≤ ε ≤ 2e and ε ≤ 1 for ε =
min(a/b, 1). -/
theorem eps_between {r : ℕ × ℕ} {e : ℝ} (he1 : e ≤ 1) (h1 : e ≤ (r.1 : ℝ) / r.2) (h2 : (r.1 : ℝ) / r.2 ≤ 2 * e) :
    e ≤ ((epsOf r : ℚ) : ℝ) ∧ ((epsOf r : ℚ) : ℝ) ≤ 2 * e ∧ ((epsOf r : ℚ) : ℝ) ≤ 1 := by
  rw [epsOf_cast]
  exact ⟨le_min h1 he1, (min_le_left _ _).trans h2, min_le_right _ _⟩

/-! ### The bound on the occurrences -/

/-- «So every variable occurs in at most 2(8k/ε)^(3k) + 2 clauses of each output» (Step 5 of
Appendix D): the bound that the function computes is at most the printed one. -/
theorem occBoundIsThePrinted : OccBoundIsThePrinted := by
  intro k r hk h1 h2
  have hε0 := epsOf_pos h1 h2
  have hε1 := epsOf_le_one r
  obtain ⟨-, hα, -, -, -⟩ := Cal.stAlpha k (epsOf r) hk hε0 hε1
  have hs := (Cal.stDegSum (Cal.alphaC k (epsOf r)) k (by omega) (by omega)).2.1
  have hd := Cal.stDegLe k (epsOf r) hk hε0 hε1
  have h3 : (occBound k r : ℝ) ≤ 2 * ((2 + 4 * Cal.alphaC k (epsOf r) * (32 * Cal.alphaC k (epsOf r)) ^ (k - 2) : ℕ) : ℝ) + 2 := by
    unfold occBound thresholds
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hs) 2
  linarith

/-! ### The bounds grow with Δ -/

/-- ⌈log₂(2Δ)⌉ grows with Δ. -/
theorem LD_mono {Δ Δ' : ℕ} (h : Δ ≤ Δ') : LD Δ ≤ LD Δ' := Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 h)

/-- The bound on the number of objects grows with Δ. -/
theorem objMax_mono (n : ℕ) {Δ Δ' : ℕ} (h : Δ ≤ Δ') : objMax n Δ ≤ objMax n Δ' := by
  unfold objMax sbMax
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left 32 h) (LD_mono h))) (Nat.mul_le_mul_right n h)

/-- The bounds on the total, on P, on the number of profiles and on the size s̄ of a check grow with
Δ. -/
theorem boundsGrowWithDelta : BoundsGrowWithDelta := by
  intro k K n Δ Δ' h
  have hLD := LD_mono h
  have hsb : sbMax Δ ≤ sbMax Δ' := by
    unfold sbMax
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 32 h) hLD
  have htb : tbMax n Δ ≤ tbMax n Δ' := by
    unfold tbMax
    have := Nat.clog_mono_right 2 (Nat.mul_le_mul_right n h)
    omega
  refine ⟨?_, ?_, ?_, hsb⟩
  · unfold UbD
    have h1 : Nat.clog 2 (96 * Δ * LD Δ) ≤ Nat.clog 2 (96 * Δ' * LD Δ') := Nat.clog_mono_right 2 (Nat.mul_le_mul (Nat.mul_le_mul_left 96 h) hLD)
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left hLD n)) (Nat.mul_le_mul_left _ h1)) _
  · unfold PbD PD
    refine Nat.ceil_mono ?_
    unfold P0
    have a1 : (Δ : ℚ) ≤ Δ' := by exact_mod_cast h
    have a2 : (tbMax n Δ : ℚ) ≤ tbMax n Δ' := by exact_mod_cast htb
    have a3 : (sbMax Δ : ℚ) ≤ sbMax Δ' := by exact_mod_cast hsb
    gcongr
  · unfold nPrMax PaddedDescent.F.Mark.nProf
    exact Nat.pow_le_pow_left (Nat.succ_le_succ (objMax_mono n h)) _

/-! ### The cut-off of k -/

/-- In the range of Theorem D (a) the cut-off of k at ⌊log₂(n+1)⌋ does nothing. -/
theorem cutOffIsIdle : CutOffIsIdle := by
  intro k n hn h
  unfold kcU
  refine min_eq_left ?_
  have hk : (k : ℝ) ≤ lg n := le_trans (by exact_mod_cast Nat.le_self_pow (by norm_num) k) h
  have h2 : (2 : ℝ) ^ k ≤ n := by
    have := (Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hn)).1 hk
    rwa [Real.rpow_natCast] at this
  have h3 : 2 ^ k ≤ n := by exact_mod_cast h2
  exact Nat.le_log_of_pow_le (by norm_num) (h3.trans (Nat.le_succ n))

/-! ### Logarithms -/

/-- x^j = 2^{j·log x} for x > 0. -/
theorem pow_eq_two_rpow {x : ℝ} (hx : 0 < x) (j : ℕ) : x ^ j = (2 : ℝ) ^ ((j : ℝ) * lg x) := by
  rw [mul_comm, Real.rpow_mul two_pos.le, lg, Real.rpow_logb two_pos (by norm_num) hx, Real.rpow_natCast]

/-- log(8x) = 3 + log x for x > 0. -/
theorem lg_eight_mul {x : ℝ} (hx : 0 < x) : lg (8 * x) = 3 + lg x := by
  unfold lg
  rw [Real.logb_mul (by norm_num) hx.ne', show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
  norm_num

/-- log(8k/e) = 3 + log(k/e) for k, e > 0. -/
theorem lg_eight_div {k e : ℝ} (hk : 0 < k) (he : 0 < e) : lg (8 * k / e) = 3 + lg (k / e) := by
  rw [mul_div_assoc, lg_eight_mul (div_pos hk he)]

/-- «As e ≥ (log n)^(−C₀) and k ≤ (log n)^(1/4)»: log(k/e) ≤ (C₀ + 1/4)·log log n, for k ≥ 1. -/
theorem lg_div_le {k C₀ : ℕ} {L e : ℝ} (hk : 1 ≤ k) (hk4 : (k : ℝ) ^ 4 ≤ L) (he : 1 / L ^ C₀ ≤ e) : lg (k / e) ≤ (C₀ + 1 / 4) * lg L := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hk4
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1 : lg (k / e) = lg k - lg e := Real.logb_div (by positivity) he0.ne'
  have h2 : 4 * lg k ≤ lg L := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hk4
    rw [Real.logb_pow] at this
    simpa [lg] using this
  have h3 : -((C₀ : ℝ) * lg L) ≤ lg e := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) he
    rw [one_div, Real.logb_inv, Real.logb_pow] at this
    simpa [lg] using this
  rw [h1]
  linarith

/-- If Δ ≤ 2·a^j + 2 with a ≥ 1, then log Δ ≤ j·log a + 2, for Δ ≥ 1. -/
theorem lg_le_of_le_pow {Δ j : ℕ} {a : ℝ} (hΔ : 1 ≤ Δ) (ha : 1 ≤ a) (h : (Δ : ℝ) ≤ 2 * a ^ j + 2) : lg Δ ≤ j * lg a + 2 := by
  have hp : 1 ≤ a ^ j := one_le_pow₀ ha
  have h1 : (Δ : ℝ) ≤ 4 * a ^ j := by linarith
  have h2 : lg Δ ≤ lg (4 * a ^ j) := lg_mono (by exact_mod_cast hΔ) h1
  have h3 : lg (4 * a ^ j) = 2 + j * lg a := by
    unfold lg
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  linarith

/-- If log n ≥ 900, then 29·(log n + 2) + 19 ≤ n. -/
theorem lin_lg_le {n : ℕ} (hn : 1 ≤ n) (hL : 900 ≤ lg n) : 29 * (lg n + 2) + 19 ≤ (n : ℝ) := by
  have h1 := lg_cube_le hn
  have h2 : (30 * lg n) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (lg n)]
  have h3 : 30 * lg n ≤ n := (sq_le_sq₀ (by linarith) (Nat.cast_nonneg n)).1 h2
  linarith

/-- ⌈log₂(2Δ)⌉ ≤ log n + 2 for Δ ≤ n, n ≥ 1. -/
theorem LD_le_lg {Δ n : ℕ} (hn : 1 ≤ n) (h : Δ ≤ n) : (LD Δ : ℝ) ≤ lg n + 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ lg n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have h1 : (n : ℝ) ≤ (2 : ℝ) ^ ⌈lg n⌉₊ := by
    have e : (n : ℝ) = (2 : ℝ) ^ lg n := (Real.rpow_logb two_pos (by norm_num) hn0).symm
    calc (n : ℝ) = (2 : ℝ) ^ lg n := e
      _ ≤ (2 : ℝ) ^ ((⌈lg n⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
      _ = (2 : ℝ) ^ ⌈lg n⌉₊ := Real.rpow_natCast _ _
  have h2 : n ≤ 2 ^ ⌈lg n⌉₊ := by exact_mod_cast h1
  have h3 : 2 * Δ ≤ 2 ^ (⌈lg n⌉₊ + 1) := by
    rw [pow_succ]
    omega
  have h4 : LD Δ ≤ ⌈lg n⌉₊ + 1 := Nat.clog_le_of_le_pow h3
  have h5 : ((⌈lg n⌉₊ : ℕ) : ℝ) < lg n + 1 := Nat.ceil_lt_add_one hL0
  have h6 : (LD Δ : ℝ) ≤ ((⌈lg n⌉₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h4
  linarith

/-! ### Every Δ up to the bound on the occurrences is within «Setting and parameters» -/

/-- «… so log Δ ≤ 3k·log(8k/e) + 2 = O(k·log(k/e)). As e ≥ (log n)^(−C₀) and k ≤ (log n)^(1/4), this
is at most 3k(3 + (C₀ + 1/4)·log log n) + 2, which is at most 4kC₀·log log n for large n, because C₀
≥ 1» (Step 5 of Appendix D), for every Δ from 2 to the bound on the occurrences; with Δ ≤ n + 1 and
n ≥ 29·⌈log₂(2Δ)⌉ + 19. -/
theorem outputsAreWithinTheSetting : OutputsAreWithinTheSetting := by
  intro C₀ hC
  obtain ⟨n₀, hn₀⟩ := VariableBound.VariablesA.settingN0 VariableBound.paramIneq C₀ hC
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 : ℝ) ^ ((2 : ℝ) ^ (40 : ℕ)))
  refine ⟨max n₀ N, fun k n Δ r e hn hk hk4 he he1 hr1 hr2 hΔ2 hΔ => ?_⟩
  have hnN : (2 : ℝ) ^ ((2 : ℝ) ^ (40 : ℕ)) ≤ n := hN.trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnN
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have hL : (2 : ℝ) ^ (40 : ℕ) ≤ lg n := (Real.le_logb_iff_rpow_le one_lt_two hn0).2 hnN
  have hL0 : 0 < lg n := lt_of_lt_of_le (by positivity) hL
  have hLL : 40 ≤ lg (lg n) := by
    refine (Real.le_logb_iff_rpow_le one_lt_two hL0).2 ?_
    rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hL
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hC' : (1 : ℝ) ≤ C₀ := by exact_mod_cast hC
  obtain ⟨hr1p, hr2p⟩ := pos_of_le_div he0 hr1
  obtain ⟨hε1, -, -⟩ := eps_between he1 hr1 hr2
  -- log Δ ≤ 3k·log(8k/e) + 2
  have c1 : lg Δ ≤ 3 * k * lg (8 * k / e) + 2 := by
    have hae : 8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ) ≤ 8 * k / e := div_le_div_of_nonneg_left (by positivity) he0 hε1
    have ha1 : 1 ≤ 8 * (k : ℝ) / e := by rw [le_div_iff₀ he0]; linarith
    have h1 : (Δ : ℝ) ≤ 2 * (8 * (k : ℝ) / e) ^ (3 * k) + 2 := by
      have h2 : (Δ : ℝ) ≤ occBound k r := by exact_mod_cast hΔ
      have h3 := occBoundIsThePrinted k r hk hr1p hr2p
      have h4 : (8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ (3 * k) ≤ (8 * (k : ℝ) / e) ^ (3 * k) :=
        pow_le_pow_left₀ (div_nonneg (by positivity) (he0.le.trans hε1)) hae _
      linarith
    have h5 := lg_le_of_le_pow (by omega) ha1 h1
    push_cast at h5
    exact h5
  -- the middle step
  have c3a : 3 * k * lg (8 * k / e) + 2 ≤ 3 * k * (3 + (C₀ + 1 / 4) * lg (lg n)) + 2 := by
    have h1 := lg_div_le (by omega) hk4 he
    rw [lg_eight_div (by linarith) he0]
    have h2 : 3 * (k : ℝ) * (3 + lg (k / e)) ≤ 3 * k * (3 + (C₀ + 1 / 4) * lg (lg n)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have c3b : 3 * (k : ℝ) * (3 + (C₀ + 1 / 4) * lg (lg n)) + 2 ≤ 4 * k * C₀ * lg (lg n) := by
    have h1 : 0 ≤ (k : ℝ) * lg (lg n) * ((C₀ : ℝ) - 1) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h2 : 0 ≤ (k : ℝ) * (lg (lg n) - 40) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- Δ ≤ (log n)^(4kC₀)
  have c2 : (Δ : ℝ) ≤ lg n ^ (4 * k * C₀) := by
    have h1 : lg Δ ≤ ((4 * k * C₀ : ℕ) : ℝ) * lg (lg n) := by
      push_cast
      linarith
    rw [pow_eq_two_rpow hL0]
    exact (Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast (by omega : 0 < Δ))).1 h1
  -- Δ ≤ n
  have c4 : Δ ≤ n := by
    have h1 := (hn₀ n k Δ ((le_max_left _ _).trans hn) hk4 hΔ2 c2).2.2.1
    have h2 : (n : ℝ) ^ (1 / (40 * C₀ : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) ?_
      rw [div_le_one (by positivity)]
      linarith
    rw [Real.rpow_one] at h2
    exact_mod_cast h1.trans h2
  refine ⟨c1, c2, ⟨c3a, c3b⟩, by omega, ?_⟩
  have h1 := LD_le_lg hn1 c4
  have h2 := lin_lg_le hn1 (le_trans (by norm_num) hL)
  have h3 : ((29 * LD Δ + 19 : ℕ) : ℝ) ≤ n := by
    push_cast
    linarith
  exact_mod_cast h3

end RecursionToBound
