/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
import RecursionToBound.Numbers
import RecursionToBound.OneOutput
import SparsificationLemma.Cal.Alpha
import ClauseBound.Gen.RateAux
import ClauseBound.Alg.TopArith
import VariableBound.Paper.Arith
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.Arith
import VariableBound.Printed.VariablesA.StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Theorem D (a) along the printed Step 5: the walk, and the whole exponent

* `walkCost`: the exponent of the walk is ⌈εn⌉ + 2 plus the number of binary digits of the bound on
  the stack. That bound is a product of (32α)^(2k), of powers of n and 2 with exponents O(k), and of
  k; the number of binary digits of a product or a sum is at most the sum of those of its parts
  (`size_stack_le`, `size_inLen_le`). With 32α ≤ (8k/ε)³
  (`SparsificationLemma.Cal.StAlphaLe`) this gives εn + 29·k·(log n + log(8k/ε)).
* `exponentIsWithinTheBound`: the bound of Step 5 of Appendix D, 2^(2en)·n^{O(k)}·2^{O(ekn·log Δ)} =
  2^{O(k²·e·n·log(k/e))}. With w = log(k/e) ≥ 1 and X = k²·e·n·w, every Δ in the list has log Δ ≤
  3k·log(8k/e) + 2 ≤ 14·k·w
  (`outputsAreWithinTheSetting`), so one output costs at most 14·A·X (`oneOutputCost`). The walk
  costs at most 2en + c·k·log n + 4c·k·w ≤ (2 + 5c)·X, because k·log n ≤ en
  (`MainTheoremForms.StepSparsifyLargeStmt`), en ≤ X and k·w ≤ X. -/

public section

namespace RecursionToBound

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen.Rate ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper

/-! ### The walk -/

/-- The number of binary digits of the bound on the number of clauses of the input: at most k·s + 4k +
s + 5, s the number of binary digits of n. -/
theorem size_inLen_le (k n : ℕ) : Nat.size (inLen k n) ≤ k * Nat.size n + 4 * k + Nat.size n + 5 := by
  unfold inLen
  have m1 := size_mul_le (k * 2 ^ k + 1) ((n + 2) ^ (k + 1))
  have m2 := size_add_le (k * 2 ^ k) 1
  have m3 := size_mul_le k (2 ^ k)
  have m4 := size_pow_le (n + 2) (k + 1)
  have m5 := size_add_le n 2
  have h3 : Nat.size (2 ^ k) = k + 1 := Nat.size_pow
  have hk := size_le_self k
  have c1 : Nat.size 1 ≤ 1 := Nat.size_le.2 (by norm_num)
  have c2 : Nat.size 2 ≤ 2 := Nat.size_le.2 (by norm_num)
  have b : (k + 1) * Nat.size (n + 2) ≤ k * Nat.size n + 2 * k + Nat.size n + 2 := by
    calc (k + 1) * Nat.size (n + 2) ≤ (k + 1) * (Nat.size n + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = k * Nat.size n + 2 * k + Nat.size n + 2 := by ring
  omega

/-- The number of binary digits of the bound on the stack of the walk, for a formula of at most m
clauses. -/
theorem size_stack_le (k τ n m : ℕ) : Nat.size (stackLenCU k τ n m) ≤ 2 * k * Nat.size τ + 2 * k + Nat.size m + 5 * Nat.size n + 36 := by
  unfold stackLenCU bsumU
  have f1 := size_add_le ((τ ^ (2 * k) * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n) 16
  have f2 := size_add_le ((τ ^ (2 * k) * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8)) (3 * n)
  have f3 := size_mul_le (τ ^ (2 * k) * n + 1) (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8)
  have f4 := size_mul_le 3 n
  have a1 := size_add_le (τ ^ (2 * k) * n) 1
  have a2 := size_mul_le (τ ^ (2 * k)) n
  have a3 := size_pow_le τ (2 * k)
  have g1 := size_add_le (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10)) 8
  have g2 := size_add_le (2 ^ k * m * (k * (3 * n + 5) + 10)) (2 * n * (2 * (3 * n + 5) + 10))
  have h1 := size_mul_le (2 ^ k * m) (k * (3 * n + 5) + 10)
  have h2 := size_mul_le (2 ^ k) m
  have h3 : Nat.size (2 ^ k) = k + 1 := Nat.size_pow
  have h4 := size_add_le (k * (3 * n + 5)) 10
  have h5 := size_mul_le k (3 * n + 5)
  have h6 := size_add_le (3 * n) 5
  have p1 := size_mul_le (2 * n) (2 * (3 * n + 5) + 10)
  have p2 := size_mul_le 2 n
  have p3 := size_add_le (2 * (3 * n + 5)) 10
  have p4 := size_mul_le 2 (3 * n + 5)
  have hk := size_le_self k
  have c1 : Nat.size 1 ≤ 1 := Nat.size_le.2 (by norm_num)
  have c2 : Nat.size 2 ≤ 2 := Nat.size_le.2 (by norm_num)
  have c3 : Nat.size 3 ≤ 2 := Nat.size_le.2 (by norm_num)
  have c5 : Nat.size 5 ≤ 3 := Nat.size_le.2 (by norm_num)
  have c8 : Nat.size 8 ≤ 4 := Nat.size_le.2 (by norm_num)
  have c10 : Nat.size 10 ≤ 4 := Nat.size_le.2 (by norm_num)
  have c16 : Nat.size 16 ≤ 5 := Nat.size_le.2 (by norm_num)
  omega

/-- Step 5: the sparsification «produces at most 2^(εn) outputs in time 2^(εn)·n^{O(k)}» (Appendix
D); here with an extra factor (8k/ε)^{O(k)}: the exponent for the walk is at most εn + 29·k·(log n +
log(8k/ε)). -/
theorem walkCost : WalkCost := by
  refine ⟨29, fun k n r hk hn h1 h2 => ?_⟩
  have hε0 := epsOf_pos h1 h2
  have hε1 := epsOf_le_one r
  have hε0' : (0 : ℝ) < ((epsOf r : ℚ) : ℝ) := by exact_mod_cast hε0
  have hε1' : ((epsOf r : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hε1
  obtain ⟨-, hα, -, -, -⟩ := Cal.stAlpha k (epsOf r) hk hε0 hε1
  have hαle := Cal.stAlphaLe k (epsOf r) hk hε0 hε1
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hL := one_le_lg hn
  have hw0 : 0 ≤ lg (8 * k / ((epsOf r : ℚ) : ℝ)) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [le_div_iff₀ hε0']
    linarith
  have ht : ((32 * Cal.alphaC k (epsOf r)).size : ℝ) ≤ 6 * lg (8 * k / ((epsOf r : ℚ) : ℝ)) := by
    have a1 := size_le_two_logb (32 * Cal.alphaC k (epsOf r)) (by omega)
    have a2 : lg ((32 * Cal.alphaC k (epsOf r) : ℕ) : ℝ) ≤ lg ((8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ 3) :=
      lg_mono (by exact_mod_cast (by omega : 0 < 32 * Cal.alphaC k (epsOf r))) (by push_cast; exact hαle)
    have a3 : lg ((8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ 3) = 3 * lg (8 * k / ((epsOf r : ℚ) : ℝ)) := by
      unfold lg
      rw [Real.logb_pow]
      norm_num
    unfold lg at a2 a3 ⊢
    linarith
  have hs : (n.size : ℝ) ≤ 2 * lg n := size_le_two_logb n hn
  have hceil : ((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) ≤ ((epsOf r : ℚ) : ℝ) * n + 1 := by
    have a1 := Nat.ceil_lt_add_one (a := epsOf r * (n : ℚ)) (by positivity)
    have a2 : (((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℚ) : ℝ) < ((epsOf r * (n : ℚ) + 1 : ℚ) : ℝ) := by exact_mod_cast a1
    push_cast at a2
    exact a2.le
  have hst : Nat.size (stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n)) ≤
      2 * k * Nat.size (32 * Cal.alphaC k (epsOf r)) + k * Nat.size n + 6 * k + 6 * Nat.size n + 41 := by
    have a1 := size_stack_le k (32 * Cal.alphaC k (epsOf r)) n (inLen k n)
    have a2 := size_inLen_le k n
    omega
  have hst' : ((Nat.size (stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n)) : ℕ) : ℝ) ≤
      2 * (k : ℝ) * ((32 * Cal.alphaC k (epsOf r)).size : ℝ) + (k : ℝ) * (n.size : ℝ) + 6 * k + 6 * (n.size : ℝ) + 41 := by exact_mod_cast hst
  have b1 : (k : ℝ) * ((32 * Cal.alphaC k (epsOf r)).size : ℝ) ≤ k * (6 * lg (8 * k / ((epsOf r : ℚ) : ℝ))) := mul_le_mul_of_nonneg_left ht (by linarith)
  have b2 : (k : ℝ) * (n.size : ℝ) ≤ k * (2 * lg n) := mul_le_mul_of_nonneg_left hs (by linarith)
  have b3 : (k : ℝ) ≤ k * lg n := le_mul_of_one_le_right (by linarith) hL
  have b4 : 3 * lg n ≤ k * lg n := mul_le_mul_of_nonneg_right hk' (by linarith)
  have b5 : 0 ≤ (k : ℝ) * lg (8 * k / ((epsOf r : ℚ) : ℝ)) := mul_nonneg (by linarith) hw0
  unfold needWalk
  push_cast
  nlinarith

/-! ### The whole exponent -/

/-- A maximum over a list of natural numbers is at most b if every member is. -/
theorem foldr_max_zero_le {L : List ℕ} {b : ℕ} (h : ∀ x ∈ L, x ≤ b) : L.foldr max 0 ≤ b := by
  induction L with
  | nil => exact Nat.zero_le b
  | cons a L ih =>
    rw [List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The numbers in the list of the Δ are at least 2 and at most the bound on the occurrences. -/
theorem of_mem_deltas {k n Δ : ℕ} {r : ℕ × ℕ} (h : Δ ∈ deltas k r n) : 2 ≤ Δ ∧ Δ ≤ occBound k r := by
  unfold deltas at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  have := List.mem_range.1 hj
  omega

/-- «The time is 2^(2en)·n^{O(k)}·2^{O(ekn·log Δ)} = 2^{O(k²·e·n·log(k/e))}, because k·log n ≤ en
for large n» (Step 5 of Appendix D): the exponent of the padding string where there is a plan is at
most A·k²·e_ℓ·n·log(k/e_ℓ). -/
theorem exponentIsWithinTheBound : ExponentIsWithinTheBound := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨A₁, n₁a, hA⟩ := oneOutputCost Idx S e C₀ Q hS
  obtain ⟨c, hc⟩ := walkCost
  obtain ⟨n₁b, hb⟩ := outputsAreWithinTheSetting C₀ (VariableBound.VariablesA.one_le_C₀ Q)
  obtain ⟨n₁c, hcL⟩ := VariableBound.VariablesA.stepSparsifyLarge C₀
  refine ⟨14 * A₁ + 2 + 5 * c, max (max n₁a n₁b) (max n₁c 2), fun k n l hn hl hk hk4 => ?_⟩
  have hna : n₁a ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnb : n₁b ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hnc : n₁c ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn2 : 2 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have he0 := VariableBound.VariablesA.e_pos Q l
  have he1 := Q.e_le l
  have hen := VariableBound.VariablesA.e_ge_n Q hl
  obtain ⟨hr1, hr2⟩ := hnum.2 l
  generalize num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()) = r at hr1 hr2 ⊢
  obtain ⟨hr1p, hr2p⟩ := pos_of_le_div he0 hr1
  obtain ⟨hε1, hε2, -⟩ := eps_between he1 hr1 hr2
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨w1, w2⟩ := VariableBound.VariablesA.lg_div_facts hk he0 he1
  have hw : 1 ≤ lg (k / e l) := w1.trans w2
  have hklg := hcL k n (e l) hnc hk4 hen
  have hL := one_le_lg hn2
  obtain ⟨w, hwdef⟩ : ∃ w, w = lg (k / e l) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = e l * n := ⟨_, rfl⟩
  rw [← hwdef] at hw
  rw [← hY] at hklg
  have hY1 : 1 ≤ Y := by nlinarith
  have hX : expVariablesA k n (e l) = (k : ℝ) ^ 2 * w * Y := by rw [expVariablesA, ← hwdef, hY]; ring
  have h8 : lg (8 * k / e l) ≤ 4 * w := by
    rw [lg_eight_div (by linarith) he0, ← hwdef]
    linarith
  have hkw : 3 ≤ (k : ℝ) * w := by nlinarith
  have hYX : Y ≤ (k : ℝ) ^ 2 * w * Y := le_mul_of_one_le_left (by linarith) (by nlinarith)
  have hkwX : (k : ℝ) * w ≤ (k : ℝ) ^ 2 * w * Y := by
    have : (k : ℝ) * w * 1 ≤ (k : ℝ) * w * (k * Y) := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    calc (k : ℝ) * w = (k : ℝ) * w * 1 := (mul_one _).symm
      _ ≤ (k : ℝ) * w * (k * Y) := this
      _ = (k : ℝ) ^ 2 * w * Y := by ring
  have hX0 : 0 ≤ (k : ℝ) ^ 2 * w * Y := by linarith
  -- the outputs
  have hout : (needOutputs S k r (Q.idx l) n : ℝ) ≤ ((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := by
    have hb0 : 0 ≤ ((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := mul_nonneg (Nat.cast_nonneg _) hX0
    refine le_trans ?_ (Nat.floor_le hb0)
    have : needOutputs S k r (Q.idx l) n ≤ ⌊((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y)⌋₊ := by
      unfold needOutputs
      refine foldr_max_zero_le fun x hx => ?_
      obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hΔ2, hΔo⟩ := of_mem_deltas hΔ
      obtain ⟨d1, d2, -, -, -⟩ := hb k n Δ r (e l) hnb hk hk4 hen he1 hr1 hr2 hΔ2 hΔo
      refine Nat.le_floor ((hA k n l Δ hna hl hk hk4 hΔ2 d2).trans ?_)
      have g1 : lg Δ ≤ 14 * (k * w) := by
        have : 3 * (k : ℝ) * lg (8 * k / e l) ≤ 3 * k * (4 * w) := mul_le_mul_of_nonneg_left h8 (by linarith)
        linarith
      calc (A₁ : ℝ) * e l * k * n * lg Δ ≤ (A₁ : ℝ) * e l * k * n * (14 * (k * w)) := mul_le_mul_of_nonneg_left g1 (by positivity)
        _ = ((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := by rw [hY]; push_cast; ring
    exact_mod_cast this
  -- the walk
  have hwalk : (needWalk k r n : ℝ) ≤ ((2 + 5 * c : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := by
    refine (hc k n r hk hn2 hr1p hr2p).trans ?_
    have g1 : ((epsOf r : ℚ) : ℝ) * n ≤ 2 * Y := by
      rw [hY]
      have := mul_le_mul_of_nonneg_right hε2 hn0
      linarith
    have g2 : lg (8 * k / ((epsOf r : ℚ) : ℝ)) ≤ 4 * w :=
      (lg_mono (div_pos (by linarith) (lt_of_lt_of_le he0 hε1)) (div_le_div_of_nonneg_left (by linarith) he0 hε1)).trans h8
    have g3 : (c : ℝ) * k * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ))) ≤ (c : ℝ) * (Y + 4 * (k * w)) := by
      have : (k : ℝ) * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ))) ≤ Y + 4 * (k * w) := by
        have := mul_le_mul_of_nonneg_left g2 (by linarith : (0 : ℝ) ≤ k)
        linarith
      calc (c : ℝ) * k * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ))) = (c : ℝ) * (k * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg c)
    have g4 : (c : ℝ) * (Y + 4 * (k * w)) ≤ (c : ℝ) * (5 * ((k : ℝ) ^ 2 * w * Y)) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg c)
    push_cast
    linarith
  rw [hX]
  push_cast at hout hwalk ⊢
  linarith

end RecursionToBound
