/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Spec

/-! Two facts about evaluators of Z, the sum over all labellings of the edges: `Correct K ε` (Z in
about 2^{ε·K²·λ} steps) is monotone in ε,
and brute force, the loop over all labellings of the edges, is correct with ε = 1/2. -/

namespace Groundwork.Prog

open Finset Stepped

/-- The default word, as a function of the context. -/
@[expose] public def nilC {C : Type} (_ : C) : List Bool := []

/-- Brute force (`brute`, the loop over all labellings of the edges) as an evaluator. -/
@[expose] public def bruteE (K : ℕ) : Evaluator := ⟨fun lam R => brute K lam nilC R⟩

/-- `Correct K ε` is monotone in ε. -/
public theorem Evaluator.Correct.mono {E : Evaluator} {K : ℕ} {ε ε' : ℝ} (h : E.Correct K ε) (hε : ε ≤ ε') :
    E.Correct K ε' := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun C _ lam R c B t S Rm hl ht hR => ?_⟩
  obtain ⟨T, h1, h2⟩ := hA C lam R c B t S Rm hl ht hR
  refine ⟨T, h1, h2.trans ?_⟩
  have : (2 : ℝ) ^ (ε * (K : ℝ) ^ 2 * lam c) ≤ (2 : ℝ) ^ (ε' * (K : ℝ) ^ 2 * lam c) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by gcongr)
  gcongr

/-- Brute force is correct with ε = 1/2: it loops over the 2^{(K(K-1)/2)·λ} labellings, and K(K-1)/2
≤ K²/2. -/
public theorem bruteE_correct (K : ℕ) : (bruteE K).Correct K (1 / 2) := by
  refine ⟨3 * K ^ 2 + 3 * K + 13, fun C _ lam R c B t S Rm hl ht hR => ?_⟩
  have h := brute_runs_pow (K := K) (lam := lam) (dflt := nilC) (R := R) (c := c) Rm t S B
    (fun v θ h1 h2 => ⟨(hR v θ h1 h2).1, by
      have := (hR v θ h1 h2).2
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this⟩)
  set m := K * (K - 1) / 2 with hm
  have hm2 : 2 * m ≤ K ^ 2 := by
    have h1 := Nat.mul_div_le (K * (K - 1)) 2
    have h2 : K * (K - 1) ≤ K ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  refine ⟨_, h.mono le_rfl ?_, ?_⟩
  · have hx : size c + B + lam c ≤ (size c + B + lam c) ^ (3 * K ^ 2 + 3 * K + 13) :=
      Nat.le_self_pow (by omega) _
    have hK : size K ≤ K + 1 := by
      have := Nat.size_le.2 (Nat.lt_two_pow_self (n := K))
      simp only [size_nat]; omega
    have h1 : m * lam c ≤ K ^ 2 * lam c := Nat.mul_le_mul_right _ (by omega)
    have h2 : K ≤ K * lam c := Nat.le_mul_of_pos_right _ hl
    have h3 := Nat.mul_le_mul_left (3 * K ^ 2 + 3 * K + 13) hx
    have h4 : 2 * size c + 3 * (m * lam c) + 2 * (B * K) + size K + 10
        ≤ (3 * K ^ 2 + 3 * K + 13) * (size c + B + lam c) := by nlinarith
    omega
  · have hexp : ((m * lam c : ℕ) : ℝ) ≤ 1 / 2 * (K : ℝ) ^ 2 * lam c := by
      have : (2 : ℝ) * m ≤ (K : ℝ) ^ 2 := by exact_mod_cast hm2
      push_cast
      have hl0 : (0 : ℝ) ≤ lam c := Nat.cast_nonneg _
      nlinarith
    have hpow : (2 : ℝ) ^ (m * lam c) ≤ (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hlin : (K : ℝ) * (t + 1) + 1 ≤ (3 * (K : ℝ) ^ 2 + 3 * K + 13) * t := by nlinarith [sq_nonneg (K : ℝ)]
    have hQ : (1 : ℝ) ≤ ((B : ℝ) + lam c) ^ (3 * K ^ 2 + 3 * K + 13) := by
      refine one_le_pow₀ ?_
      have : (1 : ℝ) ≤ lam c := by exact_mod_cast hl
      have : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      linarith
    have hP0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) := by positivity
    push_cast
    calc (2 : ℝ) ^ (m * lam c) * ((K : ℝ) * (t + 1) + 1)
        ≤ (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) * ((3 * (K : ℝ) ^ 2 + 3 * K + 13) * t) :=
          mul_le_mul hpow hlin (by positivity) hP0
      _ = (3 * (K : ℝ) ^ 2 + 3 * K + 13) * (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) * 1 * t := by ring
      _ ≤ (3 * (K : ℝ) ^ 2 + 3 * K + 13) * (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) *
            ((B : ℝ) + lam c) ^ (3 * K ^ 2 + 3 * K + 13) * t := by gcongr

end Groundwork.Prog
