/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
import RecursionToBound.Numbers
import RecursionToBound.Exponent
import PairsToBound.Arith
import PairsToBound.Width
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.Arith
import VariableBound.Printed.VariablesA.StepSparsify
import VariableBound.Paper.Arith
import UniformInK.Top.Time
import ClauseBound.Alg.End
import CountKSatRate.Pad
import Wrap.Sim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Theorem D (a) along the printed Step 5: the end

Let M compute `count S n₁ Q.pick num` with the exponent `expo S n₁ Q.pick num`, for n₁ large. Let x
be the code of (k, φ), with ℓ the level of n, 3 ≤ k ≤ (log n)^(1/4) and φ a k-CNF on n variables;
write e = e_ℓ and X = k²·e·n·log(k/e).

* The output is right (`CountIsRight`, a hypothesis here).
* M takes at most q·(|x| + 2^(expo x) + 1)^q steps, and |x| + 1 ≤ (n+2)^(5k) ≤ 2^{10·k·log n}.
* The function takes k′ = `widthOr3 φ`, and 3 ≤ k′ ≤ k (`WidthOnTheCode`, a hypothesis;
  `cutOffIsIdle`). «The bound increases with k» (`PairsToBound.expVariablesA_mono`).
* The exponent is read from the plan `planAt` at (k′, n, the level), an optional value; where there
  is no plan the exponent is n. If n < n₁ there is no plan: «For the finitely many smaller n ≥ K₀^17
  … trying all assignments is within the bound» (`MainTheoremForms.StepSparsifySmallStmt`): n ≤ c·X
  and k·log n ≤ c·X.
* If n ≥ n₁ and there is a plan, the exponent is `needOutputs` + `needWalk` at k′; if there is none,
  the exponent is n, which is below that sum (`PlanFailsOnlyAboveN`, a hypothesis). The sum is at
  most A·X (`exponentIsWithinTheBound`). And k·log n ≤ e·n ≤ X
  (`MainTheoremForms.StepSparsifyLargeStmt`).

So with a = c + A + 1: 1 ≤ a·X, the exponent is at most a·X and k·log n ≤ a·X;
`steps_le_timeVariablesA` turns this into the bound with the constant 12·q·a. That a machine exists
is `CountKSatRate.stPaddedW` with `CountIsPolynomialTime` (a hypothesis). -/

public section

namespace RecursionToBound

open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End UniformInK Wrap MainTheoremForms PairsToBound VariableBound.Paper
open Sat3 (CNF)

/-- The running time q·(len + 2^E + 1)^q of a machine that is given a padding string of 2^E units,
against the bound of Theorem D (a). If 1 ≤ a·X, E ≤ a·X and k·log n ≤ a·X for X = k²·e·n·log(k/e), n
≥ 4 and len + 1 ≤ (n+2)^(5k), then q·(len + 2^E + 1)^q ≤ 2^{12qa·X}, rounded down. -/
theorem steps_le_timeVariablesA (q a : ℕ) {k n E len : ℕ} {e : ℝ} (h1 : 1 ≤ (a : ℝ) * expVariablesA k n e) (hE : (E : ℝ) ≤ (a : ℝ) * expVariablesA k n e)
    (hk : (k : ℝ) * lg n ≤ (a : ℝ) * expVariablesA k n e) (hn : 4 ≤ n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (len + 2 ^ E + 1) ^ q ≤ timeVariablesA (q * 12 * a) k n e := by
  have h0 : 0 ≤ (a : ℝ) * expVariablesA k n e := by linarith
  have t1 : ((2 ^ E : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * ((a : ℝ) * expVariablesA k n e)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    push_cast
    linarith
  have t2 : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * ((a : ℝ) * expVariablesA k n e)) := by
    have g1 : (n + 2) ^ (5 * k) ≤ n ^ (10 * k) := by
      calc (n + 2) ^ (5 * k) ≤ (n ^ 2) ^ (5 * k) := Nat.pow_le_pow_left (by nlinarith) _
        _ = n ^ (10 * k) := by rw [← pow_mul, show 2 * (5 * k) = 10 * k by ring]
    calc ((len + 1 : ℕ) : ℝ) ≤ ((n ^ (10 * k) : ℕ) : ℝ) := by exact_mod_cast hlen.trans g1
      _ = (2 : ℝ) ^ (((10 * k : ℕ) : ℝ) * lg n) := by rw [Nat.cast_pow, natCast_pow_eq (by omega)]
      _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        push_cast
        linarith
  have h := choice_le q 10 h1 t1 t2
  rw [Nat.add_comm len (2 ^ E)]
  refine h.trans (le_of_eq ?_)
  unfold timeVariablesA
  congr 2
  push_cast
  ring

/-- Theorem D (a) for every machine that computes the named function. Four statements on the
function are hypotheses: it is right, it is polynomial-time, it sparsifies unless the exponent
exceeds n, and it reads the width and the level from the code. `exponentIsWithinTheBound` and
`cutOffIsIdle` are used directly. -/
theorem thmVariablesAForEveryMachine_of (hRight : CountIsRight) (hPoly : CountIsPolynomialTime) (hPlan : PlanFailsOnlyAboveN) (hWidth : WidthOnTheCode) : ThmVariablesAForEveryMachine := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀a, hR⟩ := hRight Idx S e C₀ Q hS num hnum
  obtain ⟨A, n₁a, hA⟩ := exponentIsWithinTheBound Idx S e C₀ Q hS num hnum
  obtain ⟨n₁b, hL⟩ := VariableBound.VariablesA.stepSparsifyLarge C₀
  refine ⟨max n₀a (max n₁a n₁b), fun n₁ hn₁ => ⟨?_, fun M q hM => ?_⟩⟩
  · obtain ⟨hp1, hp2⟩ := hPoly Idx S hS n₁ Q.pick num Q.pick_poly hnum.1
    obtain ⟨M, q, hf, hM⟩ := CountKSatRate.stPaddedW _ _ hp2 hp1
    exact ⟨M, q, hf, hM⟩
  obtain ⟨c, hc⟩ := VariableBound.VariablesA.stepSparsifySmall C₀ n₁
  refine ⟨q * 12 * (c + A + 1), fun k n l φ hl hk hk4 hφ => ?_⟩
  have hn₀a : n₀a ≤ n₁ := (le_max_left _ _).trans hn₁
  have hn₁a : n₁a ≤ n₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn₁
  have hn₁b : n₁b ≤ n₁ := ((le_max_right _ _).trans (le_max_right _ _)).trans hn₁
  have hk1 : 1 ≤ k := by omega
  have h0 : S.K (Q.idx 0) ^ 17 ≤ n := (Nat.pow_le_pow_left ((VariableBound.VariablesA.K_strictMono Q).monotone (Nat.zero_le l)) 17).trans hl.1
  have hn4 : 4 ≤ n := by
    have := (Nat.pow_le_pow_left (Q.K_two l) 17).trans hl.1
    omega
  have he0 := VariableBound.VariablesA.e_pos Q l
  have he1 := Q.e_le l
  have hen := VariableBound.VariablesA.e_ge_n Q hl
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hLg := one_le_lg (m := n) (by omega)
  -- what the function reads from the code
  have hnU : nU (SatM.enc k φ) = n := by
    unfold nU
    rw [fmlOf_enc hk1 hφ.1, List.length_replicate]
  have hw := hWidth.1 k n φ hk1 hφ
  obtain ⟨hnum', hidx⟩ := hWidth.2 Idx S e C₀ Q num k n l φ hk1 hφ hl
  obtain ⟨hw3, -, hwle⟩ := widthOr3Stmt n φ
  have hwk : widthOr3 φ ≤ k := by
    have := (hwle k hk1 hφ).1
    omega
  have hw4 : ((widthOr3 φ : ℕ) : ℝ) ^ 4 ≤ lg n := (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hwk) 4).trans hk4
  have hcut := cutOffIsIdle (widthOr3 φ) n (by omega) hw4
  have hexpo : expo S n₁ Q.pick num (SatM.enc k φ) =
      (planAt S n₁ (widthOr3 φ) n (Q.idx l) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()))).getD n := by
    unfold expo plan
    rw [hw, hnU, hcut, hidx, hnum']
  -- X ≥ 0
  obtain ⟨w1, w2⟩ := VariableBound.VariablesA.lg_div_facts hk he0 he1
  have hX0 : 0 ≤ expVariablesA k n (e l) := by
    unfold expVariablesA
    have : 0 ≤ lg (k / e l) := by linarith
    positivity
  have up : ∀ b : ℕ, b ≤ c + A + 1 → (b : ℝ) * expVariablesA k n (e l) ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) := fun b hb =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hX0
  -- the three bounds
  have key : 1 ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) ∧ ((expo S n₁ Q.pick num (SatM.enc k φ) : ℕ) : ℝ) ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) ∧
      (k : ℝ) * lg n ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) := by
    by_cases hsmall : n < n₁
    · obtain ⟨s1, s2⟩ := hc k n (e l) (by omega) hsmall hk hen he1
      have hE : expo S n₁ Q.pick num (SatM.enc k φ) = n := by
        rw [hexpo]
        unfold planAt
        rw [if_neg (not_le.2 hsmall)]
        rfl
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have u := up c (by omega)
      rw [hE]
      exact ⟨by linarith, by linarith, by linarith⟩
    · have hge : n₁ ≤ n := not_lt.1 hsmall
      have s1 := hL k n (e l) (hn₁b.trans hge) hk4 hen
      have s2 : e l * n ≤ expVariablesA k n (e l) := by
        have g1 : 1 ≤ (k : ℝ) ^ 2 * lg (k / e l) := by nlinarith
        have g2 : 0 ≤ e l * n := by positivity
        calc e l * n = 1 * (e l * n) := (one_mul _).symm
          _ ≤ (k : ℝ) ^ 2 * lg (k / e l) * (e l * n) := mul_le_mul_of_nonneg_right g1 g2
          _ = expVariablesA k n (e l) := by unfold expVariablesA; ring
      have s3 : (1 : ℝ) ≤ k * lg n := by nlinarith
      have hAx := hA (widthOr3 φ) n l (hn₁a.trans hge) hl hw3 hw4
      have hmono := expVariablesA_mono (n := n) hw3 hwk he0 he1
      have hAx' : ((needOutputs S (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) (Q.idx l) n +
          needWalk (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) n : ℕ) : ℝ) ≤ (A : ℝ) * expVariablesA k n (e l) :=
        hAx.trans (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg A))
      obtain ⟨p1, p2⟩ := hPlan Idx S hS n₁ (widthOr3 φ) n (Q.idx l) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()))
      have hE : expo S n₁ Q.pick num (SatM.enc k φ) ≤ needOutputs S (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) (Q.idx l) n +
          needWalk (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) n := by
        rw [hexpo]
        cases hp : planAt S n₁ (widthOr3 φ) n (Q.idx l) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) with
        | none => exact (p2 hp hge).le
        | some v => exact (p1 v hp).2.1.le
      have hE' : ((expo S n₁ Q.pick num (SatM.enc k φ) : ℕ) : ℝ) ≤ (A : ℝ) * expVariablesA k n (e l) := le_trans (by exact_mod_cast hE) hAx'
      have u1 := up 1 (by omega)
      have u2 := up A (by omega)
      rw [Nat.cast_one, one_mul] at u1
      exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨k1, k2, k3⟩ := key
  have hcount := hR n₁ hn₀a k n φ h0 hk hk4 hφ (PaddedDescent.pad (expo S n₁ Q.pick num (SatM.enc k φ))) (by rw [PaddedDescent.pad, List.length_replicate])
  have hrun := hM (SatM.enc k φ)
  rw [hcount] at hrun
  exact Outputs.mono hrun (steps_le_timeVariablesA q (c + A + 1) k1 k2 k3 hn4 (UniformInK.Time.length_enc_succ_le hk1 hφ))

/-- Theorem D (a) with the printed clause on the number in [e_ℓ, 2e_ℓ], from the form for every
machine that computes the named function. -/
theorem thmVariablesAWithNumberBetween_of (h : ThmVariablesAForEveryMachine) : ThmVariablesAWithNumberBetween := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := h Idx S e C₀ Q hS num hnum
  obtain ⟨⟨M, q, hf, hM⟩, hall⟩ := hn₀ n₀ le_rfl
  obtain ⟨C', hC'⟩ := hall M q hM
  exact ⟨M, C', hf, hC'⟩

end RecursionToBound
