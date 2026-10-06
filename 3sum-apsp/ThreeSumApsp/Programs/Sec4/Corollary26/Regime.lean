/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.Corollary26
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters

/-!
# Corollary 26: the parameters 21, 1/9 and 60, and the regime N ≥ D^18

Corollary 26 is the case c = 21, θ = 1/9 of the programs with rational parameters, with the
threshold 60 (`ratParams26`): the preprocessing calls that of Theorem 30 with L = 21 m and t = ⌈m/9⌉
if m = ⌈log₄ D⌉ ≥ 60. On the inputs with N ≥ D^18, and for m ≥ 60, the hypotheses of Theorem 30 hold
at these L and t (`hyp30_26`), and its two cost expressions are O(N²/D^{0.063}) and O(D^{0.437})
(`costs26`); both come from `Corollary26.costs`. Then the bound N²/D^{0.063} (`preBound26`) and what
is used about it. `regime26` puts this in the form in which the statements about the programs with
rational parameters ask for it (`CostsWithin`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec Finset

/-! ## The parameters -/

/-- The parameters of Corollary 26 in the program text: "L := 21m and t := ⌈m/9⌉", and the 60 of
"for all m ≥ 60". -/
def ratParams26 : RatParams where
  a := 21
  b := 1
  p := 1
  q := 9
  m₀ := 60
  hb := le_rfl
  hq := by norm_num
  hc := by norm_num
  hp := le_rfl
  hθ := by norm_num
  hm₀ := by norm_num

/-- L = 21 m. -/
theorem ratParams26_L (m : ℕ) : ratParams26.L m = 21 * m := by
  simp [RatParams.L, ratParams26]

/-- t = ⌈m/9⌉. -/
theorem ratParams26_t (m : ℕ) : ratParams26.t m = (m + 8) / 9 := by
  simp [RatParams.t, ratParams26]

/-- The 60 of "for all m ≥ 60": below it the program computes inner products. -/
theorem ratParams26_m₀ : ratParams26.m₀ = 60 := rfl

/-- The parameters of Theorem 30: L = 21 m. -/
def par26 (N D₀ : ℕ) : Sec2.Par := ⟨21 * logFour D₀, logFour D₀, N⟩
/-- t = ⌈m/9⌉. -/
def switch26 (D₀ : ℕ) : ℕ := (logFour D₀ + 8) / 9

/-- At the parameters of Corollary 26, Theorem 30 is used with L = 21 m. -/
theorem parOf_ratParams26 (N D₀ : ℕ) : parOf ratParams26 N D₀ = par26 N D₀ := by
  simp only [parOf, par26, ratParams26_L]

/-- At the parameters of Corollary 26, Theorem 30 is used with t = ⌈m/9⌉. -/
theorem switchOf31_ratParams26 (D₀ : ℕ) : switchOf31 ratParams26 D₀ = switch26 D₀ := by
  simp only [switchOf31, switch26, ratParams26_t]

/-- The ceiling ⌈m/9⌉ in natural numbers. -/
theorem switchOf_ninth (m : ℕ) : switchOf (1 / 9) m = (m + 8) / 9 := by
  have h := switchOf_div 1 m (q := 9) (by norm_num)
  norm_num at h
  exact h

/-! ## The two cost expressions -/

/-- The bound of the preprocessing of Corollary 26. -/
noncomputable def preBound26 (D₀ N : ℕ) : ℝ := (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)

/-- **The costs of Theorem 30 at the parameters of Corollary 26**, for m ≥ 60. -/
theorem costs26 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ D₀ N : ℕ, D₀ ^ 18 ≤ N → 60 ≤ logFour D₀ → Hyp30 (par26 N D₀) (switch26 D₀) ∧
      cost8 (21 * logFour D₀) (logFour D₀) (switch26 D₀) N ≤ C * preBound26 D₀ N ∧
      costQuery (21 * logFour D₀) (logFour D₀) (switch26 D₀) ≤ C * (D₀ : ℝ) ^ (0.437 : ℝ) := by
  obtain ⟨C, hC, h⟩ := Corollary26.costs
  refine ⟨C, hC, fun D₀ N hN hm => ?_⟩
  obtain ⟨hN0, hcost8, hquery⟩ := h D₀ N (logFour D₀) hN (ceil_logb_four D₀).symm hm
  rw [switchOf_ninth] at hcost8 hquery
  refine ⟨⟨le_trans (by norm_num) hm, ?_, ?_, hN0⟩, hcost8, hquery⟩
  · change 10 * logFour D₀ ≤ 21 * logFour D₀
    omega
  · change (logFour D₀ + 8) / 9 ≤ logFour D₀
    omega

/-- Proof of Corollary 26: "For m ≥ 60, Theorem 30 thus applies". -/
theorem hyp30_26 {N D₀ : ℕ} (hN : D₀ ^ 18 ≤ N) (hm : 60 ≤ logFour D₀) :
    Hyp30 (par26 N D₀) (switch26 D₀) := by
  obtain ⟨_, -, hcosts⟩ := costs26
  exact (hcosts D₀ N hN hm).1

/-! ## The overheads -/

/-- `N D₀ ≤ N²/D₀^{0.063}`, because `D₀^{1.063} ≤ D₀^{18} ≤ N`. -/
theorem N_mul_D_le_preBound26 {D₀ N : ℕ} (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) :
    (N : ℝ) * (D₀ : ℝ) ≤ preBound26 D₀ N := by
  have hD1 : (1 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < (D₀ : ℝ) := by linarith
  have hle : (D₀ : ℝ) * (D₀ : ℝ) ^ (0.063 : ℝ) ≤ (N : ℝ) :=
    calc (D₀ : ℝ) * (D₀ : ℝ) ^ (0.063 : ℝ) = (D₀ : ℝ) ^ (1.063 : ℝ) := by
          rw [show (1.063 : ℝ) = 1 + 0.063 by norm_num, Real.rpow_add hD0, Real.rpow_one]
      _ ≤ (D₀ : ℝ) ^ ((18 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
      _ ≤ (N : ℝ) := by
          rw [Real.rpow_natCast]
          exact_mod_cast hN
  rw [preBound26, le_div_iff₀ (by positivity), mul_assoc, sq]
  gcongr

/-- N ≥ 1, because N ≥ D^18. -/
theorem one_le_of_pow_eighteen_le {D₀ N : ℕ} (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) : 1 ≤ N :=
    le_trans (Nat.one_le_pow _ _ hD) hN

/-- N ≥ D, because N ≥ D^18. -/
theorem le_of_pow_eighteen_le {D₀ N : ℕ} (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) : D₀ ≤ N := by
  refine le_trans ?_ hN
  calc D₀ = D₀ ^ 1 := (pow_one _).symm
    _ ≤ D₀ ^ 18 := Nat.pow_le_pow_right hD (by norm_num)

/-- The bound of the preprocessing is at least 1. -/
theorem one_le_preBound26 {D₀ N : ℕ} (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) : 1 ≤ preBound26 D₀ N := by
  refine le_trans ?_ (N_mul_D_le_preBound26 hD hN)
  have : 1 ≤ N * D₀ := Nat.mul_pos (one_le_of_pow_eighteen_le hD hN) hD
  exact_mod_cast this

/-! ## The regime -/

/-- **The regime N ≥ D^18.** There is a constant with which, on these inputs, the two bounds of
Corollary 26 dominate the two costs of Theorem 30 at L = 21 m and t = ⌈m/9⌉ for m ≥ 60. -/
theorem regime26 : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D₀ : ℕ, 1 ≤ D₀ → D₀ ^ 18 ≤ N →
    CostsWithin ratParams26 C N D₀ (preBound26 D₀ N) ((D₀ : ℝ) ^ (0.437 : ℝ)) := by
  obtain ⟨C, hC, hcost⟩ := costs26
  refine ⟨C, hC, fun N D₀ hD hN => ⟨one_le_of_pow_eighteen_le hD hN, hD,
    le_of_pow_eighteen_le hD hN, one_le_preBound26 hD hN,
    Real.one_le_rpow (by exact_mod_cast hD) (by norm_num), fun hm => ?_⟩⟩
  rw [parOf_ratParams26, switchOf31_ratParams26, ratParams26_L]
  exact hcost D₀ N hN hm

end Light.Sec4
