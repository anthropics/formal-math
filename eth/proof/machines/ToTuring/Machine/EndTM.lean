/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
public import ToTuring.PolyT
import ToTuring.Machine.Host
import StepMachines.Prog.Decode
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! From step counts to a Turing machine, last part. A machine cut into polynomial-time steps
(`Stepped`, `IsPolyT`) that
decides 3-SAT within c·2^{(δ/2)n} steps, with states of polynomial size, gives a Turing machine of
Mathlib that decides
3-SAT within O(2^{δn}) steps (`InTimeTM δ`). The host of Machine/Host.lean needs (number of steps + 1)
· (a
polynomial in the length of the input) steps of its own. That length is polynomial in n, so
`exists_pow_le` bounds the second
factor by a constant times 2^{(δ/2)n}. -/

namespace Groundwork

open Sat3 Turing
open scoped NNReal

/-- A polynomial is below every exponential, up to a constant. -/
public theorem exists_pow_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ C : ℕ, ∀ n : ℕ, ((n : ℝ) + 2) ^ k ≤ C * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ε * Real.log 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact mul_pos hε (Real.log_pos one_lt_two)
  refine ⟨⌈(k.factorial : ℝ) / a ^ k * Real.exp (a * 2)⌉₊, fun n => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (a * ((n : ℝ) + 2)) (by positivity) k
  have h2 : (2 : ℝ) ^ (ε * n) = Real.exp (a * n) := by
    rw [Real.rpow_def_of_pos two_pos, ha]; congr 1; ring
  have h3 : Real.exp (a * ((n : ℝ) + 2)) = Real.exp (a * 2) * Real.exp (a * n) := by
    rw [← Real.exp_add]; congr 1; ring
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h4 : ((n : ℝ) + 2) ^ k ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * 2) * Real.exp (a * n) := by
    rw [mul_pow, div_le_iff₀ hk, h3] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  rw [h2]
  exact h4.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.exp_pos _).le)


/-- Take a machine cut into polynomial-time steps that decides 3-SAT in at most c·2^{δn/2} steps,
with every state of size at
most c·(|input|+1)^c. It gives a Turing machine with finite alphabets that decides 3-SAT within
⌊C·2^{δn}⌋ steps, which is
`InTimeTM δ`. -/
public theorem inTimeTM_of_machine {δ : ℝ≥0} (hδ : 0 < δ) (M : Stepped (List Bool) Bool) [IsPolyT M] (c : ℕ)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      ∃ (T : ℕ) (b : Bool), M.Runs (enc φ) T (c * ((enc φ).length + 1) ^ c) b ∧
        (b = true ↔ Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) : InTimeTM δ := by
  have hδ2 : (0 : ℝ) < (δ : ℝ) / 2 := by have : (0 : ℝ) < δ := hδ; positivity
  obtain ⟨N', c', hfin, hP⟩ := exists_tm M (2 * c)
  obtain ⟨C₁, hC₁⟩ := exists_pow_le (4 * c') hδ2
  refine ⟨N', c' * (c + 1) * 25 ^ c' * C₁, hfin, fun n φ h3 => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n φ h3
  obtain ⟨N, hN⟩ : ∃ N, N = (enc φ).length := ⟨_, rfl⟩
  rw [← hN] at hr
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((δ : ℝ) / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
  have hS : c * (N + 1) ^ c ≤ (N + 2) ^ (2 * c) := by
    have h1 : c ≤ (N + 2) ^ c := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) c)
    have h2 : (N + 1) ^ c ≤ (N + 2) ^ c := Nat.pow_le_pow_left (by omega) c
    calc c * (N + 1) ^ c ≤ (N + 2) ^ c * (N + 2) ^ c := Nat.mul_le_mul h1 h2
      _ = (N + 2) ^ (2 * c) := by rw [two_mul, pow_add]
  obtain ⟨ev⟩ := hP (enc φ) T _ b hr (hN ▸ hS)
  rw [← hN] at ev
  have hle : c' * (T + 1) * (N + 1) ^ c' ≤ ⌊((c' * (c + 1) * 25 ^ c' * C₁ : ℕ) : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * (2 : ℝ) ^ ((δ : ℝ) / 2 * n) := by nlinarith
    have h2 : ((N : ℝ) + 1) ^ c' ≤ (25 : ℝ) ^ c' * (C₁ * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) := by
      have h5 : N + 1 ≤ 25 * (n + 2) ^ 4 := hN ▸ Groundwork.Decode.length_enc_succ_le h3
      have h6 : ((N : ℝ) + 1) ≤ 25 * ((n : ℝ) + 2) ^ 4 := by exact_mod_cast h5
      calc ((N : ℝ) + 1) ^ c' ≤ (25 * ((n : ℝ) + 2) ^ 4) ^ c' := by gcongr
        _ = (25 : ℝ) ^ c' * ((n : ℝ) + 2) ^ (4 * c') := by rw [mul_pow, ← pow_mul]
        _ ≤ _ := by gcongr; exact hC₁ n
    have h7 : (2 : ℝ) ^ ((δ : ℝ) * n) = (2 : ℝ) ^ ((δ : ℝ) / 2 * n) * (2 : ℝ) ^ ((δ : ℝ) / 2 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    push_cast
    rw [h7]
    calc (c' : ℝ) * ((T : ℝ) + 1) * ((N : ℝ) + 1) ^ c'
        ≤ (c' : ℝ) * (((c : ℝ) + 1) * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) *
            ((25 : ℝ) ^ c' * (C₁ * (2 : ℝ) ^ ((δ : ℝ) / 2 * n))) := by gcongr
      _ = _ := by ring
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩

end Groundwork
