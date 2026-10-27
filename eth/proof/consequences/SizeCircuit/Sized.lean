/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.Defs
import SizeCircuit.Gamma
import GraphProblems.Sized
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: «Corollary 6 then counts …»

Proof of `StSizedBy` of proof/consequences/SizeCircuit/Defs.lean: for every procedure E that serves
for #max(w,3)-SAT with a small enough exponent, the machine `sizedBy gates E` (ONE call of E on ψ ∧
Γ) returns the number of satisfying assignments of ψ with exactly s true variables within c'·2^{δn}
steps. The paper: «All these formulas have O(n) variables, so Corollary 6, applied with a small
enough value in place of δ, gives time O(2^{δn}).»

The number is right by `stGammaCount`; ψ ∧ Γ has width at most max(w,3) and N ≤ (a+1)·(n+1)
variables by `stGamma`; so δ_E·N ≤ δ·(n+1). Three small facts come from
proof/consequences/GraphProblems/Sized.lean (`cntN_dedup`, `cntN_le`, `ofWord_binary`: striking out
repeated clauses keeps the count, the count is at most 2^N, and a number written in N + 1 bits reads
back as itself). They do not use the other machine of that file (`GraphProblems.sized`, through
blocks). -/

public section

namespace SizeCircuit

open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

/-- Γ has the variables x₀ … xₙ₋₁ among its variables. -/
theorem le_numVars (gates : ℕ → ℕ → List GateD) (n s : ℕ) : n ≤ numVars gates n s := by
  unfold numVars
  split_ifs <;> omega

/-- Γ has at most (a+1)·(n+1) variables. -/
theorem numVars_le {gates : ℕ → ℕ → List GateD} {a : ℕ} (hT : TestsSize gates a) (n s : ℕ) : numVars gates n s ≤ (a + 1) * (n + 1) := by
  unfold numVars
  split_ifs with h0
  · exact Nat.zero_le _
  · exact (stGamma gates a hT n s (by omega)).2.1

/-- Γ is a 3-CNF on its variables, also for n = 0. -/
theorem shaped_gamma {gates : ℕ → ℕ → List GateD} {a : ℕ} (hT : TestsSize gates a) (n s : ℕ) : Shaped 3 (numVars gates n s) (gamma gates n s) := by
  unfold numVars gamma
  split_ifs with h0 hs
  · intro C hC
    exact absurd hC List.not_mem_nil
  · intro C hC
    rw [List.mem_singleton.1 hC]
    exact ⟨by simp, fun l hl => absurd hl List.not_mem_nil⟩
  · exact (stGamma gates a hT n s (by omega)).1

/-- **`StSizedBy`.** Let gates test the size with at most a·(n+1) gates and let E serve as the
procedure for #max(w,3)-SAT with an exponent δ_E ≥ 0 such that δ_E·(a+1) ≤ δ. Then `sizedBy gates E`
returns, on (n in unary, s, ψ) for s ≤ n and ψ of width at most w on x₀ … xₙ₋₁, the number of
satisfying assignments of ψ with exactly s true variables, within c'·2^{δn} steps and on states of
size at most c'·(n + number of clauses + 2)^{c'}. -/
theorem stSizedBy : StSizedBy := by
  intro gates a hT w δ δE hδ hδE hle E c hE
  obtain ⟨c₁, hc₁⟩ := exists_nat_ge ((c : ℝ) * (2 : ℝ) ^ δ)
  obtain ⟨C', hC'⟩ : ∃ C', C' = c₁ + c * (a + 3) ^ c + c := ⟨_, rfl⟩
  have k1 : c₁ ≤ C' := by rw [hC', Nat.add_assoc]; exact Nat.le_add_right _ _
  have k2 : c * (a + 3) ^ c ≤ C' := by rw [hC']; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have k3 : c ≤ C' := by rw [hC']; exact Nat.le_add_left _ _
  refine ⟨C', fun n s ψ _ hψ => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = numVars gates n s := ⟨_, rfl⟩
  have hNle : N ≤ (a + 1) * (n + 1) := hN ▸ numVars_le hT n s
  have hnN : n ≤ N := hN ▸ le_numVars gates n s
  have hshape : ∀ C ∈ (ψ ++ gamma gates n s).dedup, C.length ≤ max w 3 ∧ ∀ l ∈ C, l.1 < N := by
    intro C hC
    rcases List.mem_append.1 (List.mem_dedup.1 hC) with h | h
    · obtain ⟨h1, h2⟩ := hψ C h
      exact ⟨h1.trans (le_max_left _ _), fun l hl => lt_of_lt_of_le (h2 l hl) hnN⟩
    · obtain ⟨h1, h2⟩ := shaped_gamma hT n s C h
      exact ⟨h1.trans (le_max_right _ _), fun l hl => hN ▸ h2 l hl⟩
  obtain ⟨T, hr, hTb⟩ := hE N _ hshape (List.nodup_dedup _)
  have hin : withGamma gates (List.replicate n (), s, ψ) = (List.replicate N (), (ψ ++ gamma gates n s).dedup) := by
    rw [withGamma, hN]
    simp only [List.length_replicate]
  have hcount : cntN N (ψ ++ gamma gates n s) = cntS n s ψ := by
    rw [hN]
    exact stGammaCount gates a hT n s ψ fun C hC => (hψ C hC).2
  rw [← hin] at hr
  have h2 := Stepped.mapOut_runs (f := ofWord) (Stepped.mapIn_runs hr)
  rw [cntN_dedup, ofWord_binary (cntN_le _ _), hcount] at h2
  refine ⟨T, h2.mono le_rfl ?_, ?_⟩
  · obtain ⟨X, hX⟩ : ∃ X, X = n + ψ.length + 2 := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    have h3 : N + 2 ≤ (a + 3) * X := by
      have e1 : (a + 1) * (n + 1) ≤ (a + 1) * X := Nat.mul_le_mul_left _ (by omega)
      have e2 : (a + 3) * X = (a + 1) * X + 2 * X := by ring
      omega
    calc c * (N + 2) ^ c ≤ c * ((a + 3) * X) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
      _ = c * (a + 3) ^ c * X ^ c := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ C' * X ^ C' := Nat.mul_le_mul k2 (Nat.pow_le_pow_right hX1 k3)
  · have hN' : (N : ℝ) ≤ ((a : ℝ) + 1) * ((n : ℝ) + 1) := by exact_mod_cast hNle
    have h1 : δE * N ≤ δ * n + δ := by
      calc δE * N ≤ δE * (((a : ℝ) + 1) * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hN' hδE
        _ = δE * ((a : ℝ) + 1) * ((n : ℝ) + 1) := by ring
        _ ≤ δ * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = δ * n + δ := by ring
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := by positivity
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δE * N) := hTb
      _ ≤ c * (2 : ℝ) ^ (δ * n + δ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two h1) (Nat.cast_nonneg c)
      _ = c * (2 : ℝ) ^ δ * (2 : ℝ) ^ (δ * n) := by
        rw [Real.rpow_add two_pos]
        ring
      _ ≤ c₁ * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc₁ hp
      _ ≤ C' * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 k1) hp

end SizeCircuit
