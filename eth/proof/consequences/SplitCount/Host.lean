/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import ToTuring.Machine.EndTM
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # The time of a Turing machine that simulates a machine cut into steps

Let M be a machine cut into steps that writes the number of satisfying assignments of a k-CNF on n
variables within c·2^{(δ/2)n} steps, on states of size polynomial in the length of the input, and
let N be a Turing machine that simulates M with the overhead q·(T+1)·(|x|+S+1)^q. The length of the
input is polynomial in n, so N counts within ⌊C·2^{δn}⌋ steps: `counts_of_simulation`.
Here the Turing machine is the given one, and not only some Turing machine that exists, so that the
statement `StTiedTM` can tie it to M. -/

public section

namespace SplitCount

open Groundwork Turing

/-- If N simulates M with the overhead q·(T+1)·(|x|+S+1)^q, the code of a k-CNF on n variables has
length + 1 at most a·(n+2)^d, and M writes the number of satisfying assignments within c·2^{(δ/2)n}
steps on states of size at most c·(length + 1)^c, then N counts the satisfying assignments of k-CNFs
within ⌊C·2^{δn}⌋ steps, for some C. -/
theorem counts_of_simulation {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (M : Stepped (List Bool) (List Bool)) (N' : TM2ComputableAux Bool Bool) (q : ℕ)
    (hP : ∀ (x w : List Bool) (T S : ℕ), M.Runs x T S w →
      Nonempty (TM2OutputsInTime N'.tm (x.map N'.inputAlphabet.invFun) (some (w.map N'.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q)))
    (c a d : ℕ) (hlen : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ → (SatK.enc k φ).length + 1 ≤ a * (n + 2) ^ d)
    (h : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
      ∃ T : ℕ, M.Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n)) :
    ∃ C : ℕ, SatK.CountsTM k N' fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨C₁, hC₁⟩ := exists_pow_le (d * (c + 1) * q) hδ2
  refine ⟨q * (c + 1) * ((c + 1) ^ q * a ^ ((c + 1) * q)) * C₁, fun n φ h3 => ?_⟩
  obtain ⟨T, hr, hT⟩ := h n φ h3
  obtain ⟨N, hN⟩ : ∃ N, N = (SatK.enc k φ).length := ⟨_, rfl⟩
  rw [← hN] at hr
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨ev⟩ := hP (SatK.enc k φ) _ T _ hr
  rw [← hN] at ev
  have hS : N + c * (N + 1) ^ c + 1 ≤ (c + 1) * (a * (n + 2) ^ d) ^ (c + 1) := by
    have h5 : N + 1 ≤ a * (n + 2) ^ d := hN ▸ hlen n φ h3
    have h1 : N + 1 ≤ (N + 1) ^ (c + 1) := Nat.le_self_pow (by omega) _
    have h2 : (N + 1) ^ c ≤ (N + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc N + c * (N + 1) ^ c + 1 ≤ (N + 1) ^ (c + 1) + c * (N + 1) ^ (c + 1) := by
          have := Nat.mul_le_mul_left c h2
          omega
      _ = (c + 1) * (N + 1) ^ (c + 1) := by ring
      _ ≤ (c + 1) * (a * (n + 2) ^ d) ^ (c + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 _)
  have hle : q * (T + 1) * (N + c * (N + 1) ^ c + 1) ^ q ≤
      ⌊((q * (c + 1) * ((c + 1) ^ q * a ^ ((c + 1) * q)) * C₁ : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * (2 : ℝ) ^ (δ / 2 * n) := by nlinarith
    have h2 : (((N + c * (N + 1) ^ c + 1 : ℕ) : ℝ)) ^ q ≤
        (((c : ℝ) + 1) ^ q * (a : ℝ) ^ ((c + 1) * q)) * (C₁ * (2 : ℝ) ^ (δ / 2 * n)) := by
      have h6 : ((N + c * (N + 1) ^ c + 1 : ℕ) : ℝ) ≤ ((c : ℝ) + 1) * ((a : ℝ) * ((n : ℝ) + 2) ^ d) ^ (c + 1) := by
        exact_mod_cast hS
      calc (((N + c * (N + 1) ^ c + 1 : ℕ) : ℝ)) ^ q ≤ (((c : ℝ) + 1) * ((a : ℝ) * ((n : ℝ) + 2) ^ d) ^ (c + 1)) ^ q := by gcongr
        _ = (((c : ℝ) + 1) ^ q * (a : ℝ) ^ ((c + 1) * q)) * ((n : ℝ) + 2) ^ (d * (c + 1) * q) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_assoc, mul_assoc]
        _ ≤ _ := by gcongr; exact hC₁ n
    have h7 : (2 : ℝ) ^ (δ * n) = (2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    rw [h7]
    calc ((q * (T + 1) * (N + c * (N + 1) ^ c + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * ((T : ℝ) + 1) * (((N + c * (N + 1) ^ c + 1 : ℕ) : ℝ)) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * (((c : ℝ) + 1) * (2 : ℝ) ^ (δ / 2 * n)) *
            ((((c : ℝ) + 1) ^ q * (a : ℝ) ^ ((c + 1) * q)) * (C₁ * (2 : ℝ) ^ (δ / 2 * n))) := by gcongr
      _ = _ := by push_cast; ring
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

end SplitCount
