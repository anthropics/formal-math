/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Mach.Defs
import SparsificationLemma.Geo.S
import SparsificationLemma.Mach.Len
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Parts (a) to (d) of the theorem on sparsification `SparsABCD` of Mach/Defs.lean, on a Turing machine
This four-part form, for k-CNFs, is not stated in the paper; it belongs to Lemma 4, Appendix C and
Step 5 of Appendix D.
`sparsABCD` derives `SparsABCD` from `Prints`, the statement that one machine prints the outputs of
the sparsification with the thresholds given by τ = 2^(4s+17) (a threshold of the sparsification,
not the τ of Definition 2) within C₀·(length of the input + 2^k)^C₀·2^(C₀·⌊n/2^s⌋) steps.
The machine is the same, and C = C₀ + 81. Let s = `precE C k ε`, the larger of `s0U k` and
⌈log₂⌈C/ε⌉⌉, and B = Ck/ε.
From C/ε ≤ 2^s we get n/2^s ≤ εn, which gives (a) by `Geo.StThmS`, and C₀·⌊n/2^s⌋ ≤ εn, which gives
(d). Part (b), and that the outputs are k-CNFs without repeated clauses, are in `Geo.StThmS`.
For (c): 2^(s0U k) ≤ 4k² and 2^⌈log₂⌈C/ε⌉⌉ ≤ 4C/ε, and both are at most 4B²/C. So 81·2^s ≤ 4B²,
hence 2^(4s+17) = (2^s)^4·2^17 ≤ (2^25/3^16)·B^8 ≤ B^8 and (2^(4s+17))^(2k) ≤ B^(16k). -/

public section

namespace SparsificationLemma.Mach

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

/-- 2^(s0U k) ≤ 4k² for k ≥ 1. -/
theorem two_pow_s0U_le {k : ℕ} (hk : 1 ≤ k) : 2 ^ s0U k ≤ 4 * k ^ 2 := by
  have hpos : 0 < Nat.size k := Nat.size_pos.2 hk
  obtain ⟨j, hj⟩ : ∃ j, Nat.size k = j + 1 := ⟨Nat.size k - 1, by omega⟩
  have h1 : 2 ^ j ≤ k := Nat.lt_size.1 (by omega)
  have h2 : 2 ^ s0U k = 4 * (2 ^ j) ^ 2 := by rw [s0U, hj]; ring
  rw [h2]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)

/-- 2^⌈log₂ N⌉ ≤ 2N for N ≥ 1. -/
theorem two_pow_clog_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ Nat.clog 2 N ≤ 2 * N := by
  rcases Nat.eq_or_lt_of_le hN with h | h
  · rw [← h]; simp
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : 0 < Nat.clog 2 N := Nat.clog_pos (by norm_num) h
    obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 N = j + 1 := ⟨Nat.clog 2 N - 1, by omega⟩
    rw [hj] at h1 ⊢
    simp only [Nat.pred_succ] at h1
    rw [pow_succ]
    omega

/-- C/ε ≤ 2^s for s = `precE C k ε`. -/
theorem div_le_two_pow_precE (C k : ℕ) (ε : ℚ) : (C : ℝ) / (ε : ℝ) ≤ (2 : ℝ) ^ precE C k ε := by
  have h1 : (C : ℚ) / ε ≤ (⌈(C : ℚ) / ε⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ⌈(C : ℚ) / ε⌉₊ ≤ 2 ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ := Nat.le_pow_clog (by norm_num) _
  have h3 : 2 ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ 2 ^ precE C k ε := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have h4 : (C : ℚ) / ε ≤ ((2 ^ precE C k ε : ℕ) : ℚ) := h1.trans (by exact_mod_cast h2.trans h3)
  have h5 : (((C : ℚ) / ε : ℚ) : ℝ) ≤ (((2 ^ precE C k ε : ℕ) : ℚ) : ℝ) := by exact_mod_cast h4
  simpa using h5

/-- C·2^s ≤ 4·(Ck/ε)² for s = `precE C k ε`, if C ≥ 1, k ≥ 1 and ε ∈ (0,1]. -/
theorem two_pow_precE_le {C k : ℕ} {ε : ℚ} (hC : 1 ≤ C) (hk : 1 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (C : ℝ) * (2 : ℝ) ^ precE C k ε ≤ 4 * ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ 2 := by
  have hCR : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hA : (C : ℝ) ≤ (C : ℝ) / (ε : ℝ) := by rw [le_div_iff₀ h0R]; nlinarith
  have hB : (C : ℝ) * (k : ℝ) / (ε : ℝ) = (C : ℝ) / (ε : ℝ) * (k : ℝ) := by ring
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
  rw [hB, mul_pow]
  rcases le_total (s0U k) (Nat.clog 2 ⌈(C : ℚ) / ε⌉₊) with h | h
  · rw [precE, max_eq_right h]
    have hq : 0 < (C : ℚ) / ε := by positivity
    have hN : 1 ≤ ⌈(C : ℚ) / ε⌉₊ := Nat.ceil_pos.2 hq
    have a1 := two_pow_clog_le hN
    have a2 : (⌈(C : ℚ) / ε⌉₊ : ℚ) < (C : ℚ) / ε + 1 := Nat.ceil_lt_add_one hq.le
    have a3 : (⌈(C : ℚ) / ε⌉₊ : ℝ) < (C : ℝ) / (ε : ℝ) + 1 := by exact_mod_cast a2
    have a4 : (2 : ℝ) ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ 2 * (⌈(C : ℚ) / ε⌉₊ : ℝ) := by exact_mod_cast a1
    generalize (C : ℝ) / (ε : ℝ) = A at *
    have a5 : (2 : ℝ) ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ 4 * A := by linarith
    calc (C : ℝ) * (2 : ℝ) ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ A * (4 * A) := mul_le_mul hA a5 (by positivity) (by linarith)
      _ = 4 * (A ^ 2 * 1) := by ring
      _ ≤ 4 * (A ^ 2 * (k : ℝ) ^ 2) := by gcongr
  · rw [precE, max_eq_left h]
    have a1 : (2 : ℝ) ^ s0U k ≤ 4 * (k : ℝ) ^ 2 := by exact_mod_cast two_pow_s0U_le hk
    generalize (C : ℝ) / (ε : ℝ) = A at *
    have a2 : (C : ℝ) ≤ A ^ 2 := by nlinarith
    calc (C : ℝ) * (2 : ℝ) ^ s0U k ≤ A ^ 2 * (4 * (k : ℝ) ^ 2) := mul_le_mul a2 a1 (by positivity) (by positivity)
      _ = 4 * (A ^ 2 * (k : ℝ) ^ 2) := by ring

/-- Part (c): 2^(2k(4s+17)) ≤ (Ck/ε)^(16k) for s = `precE C k ε`, if C ≥ 81, k ≥ 1 and ε ∈ (0,1]. -/
theorem two_pow_betaU_le {C k : ℕ} {ε : ℚ} (hC : 81 ≤ C) (hk : 1 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (2 : ℝ) ^ betaU k (precE C k ε) ≤ ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ (16 * k) := by
  have hCR : (81 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hs := two_pow_precE_le (by omega : 1 ≤ C) hk h0 h1
  generalize (C : ℝ) * (k : ℝ) / (ε : ℝ) = B at *
  generalize precE C k ε = s at *
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hs' : (2 : ℝ) ^ s ≤ 4 / 81 * B ^ 2 := by nlinarith
  have hB8 : 0 ≤ B ^ 8 := by positivity
  have e1 : (2 : ℝ) ^ (4 * s + 17) ≤ B ^ 8 := by
    calc (2 : ℝ) ^ (4 * s + 17) = ((2 : ℝ) ^ s) ^ 4 * 2 ^ 17 := by rw [pow_add, pow_mul']
      _ ≤ (4 / 81 * B ^ 2) ^ 4 * 2 ^ 17 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.le hs' 4) (by positivity)
      _ = 33554432 / 43046721 * B ^ 8 := by ring
      _ ≤ B ^ 8 := by linarith
  calc (2 : ℝ) ^ betaU k s = ((2 : ℝ) ^ (4 * s + 17)) ^ (2 * k) := by rw [betaU, ← pow_mul]; congr 1; ring
    _ ≤ (B ^ 8) ^ (2 * k) := pow_le_pow_left₀ (by positivity) e1 _
    _ = B ^ (16 * k) := by rw [← pow_mul]; congr 1; ring

/-- c·⌊n/2^s⌋ ≤ εn, if c ≤ C, C/ε ≤ 2^s and ε > 0. -/
theorem mul_div_le_eps {c C n s : ℕ} {ε : ℝ} (hc : c ≤ C) (h0 : 0 < ε) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    ((c * (n / 2 ^ s) : ℕ) : ℝ) ≤ ε * (n : ℝ) := by
  have hcR : (c : ℝ) ≤ (C : ℝ) := by exact_mod_cast hc
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have h1 : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ s := by
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := 2 ^ s)
    simpa using this
  have h2 : (C : ℝ) ≤ ε * (2 : ℝ) ^ s := by rwa [div_le_iff₀ h0, mul_comm] at hs
  have h3 : (C : ℝ) * ((n : ℝ) / (2 : ℝ) ^ s) ≤ ε * (n : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h4 : (0 : ℝ) ≤ ((n / 2 ^ s : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_mul]
  exact (mul_le_mul hcR h1 h4 (Nat.cast_nonneg _)).trans h3

/-- The theorem on sparsification, parts (a) to (d), from `Geo.StThmS` (the theorem for the
thresholds with τ = 2^(4s+17)) and `Prints`. -/
theorem sparsABCD_of (hS : StThmS) (hP : Prints) : SparsABCD := by
  obtain ⟨M, C₀, hfin, hM⟩ := hP
  refine ⟨M, C₀ + 81, hfin, fun k n ε φ hk h0 h1 hφ hne => ?_⟩
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have hs0 : s0U k ≤ precE (C₀ + 81) k ε := le_max_left _ _
  have hsC := div_le_two_pow_precE (C₀ + 81) k ε
  have hc := two_pow_betaU_le (C := C₀ + 81) (by omega) hk h0 h1
  generalize hs : precE (C₀ + 81) k ε = s at *
  obtain ⟨-, g2, g3, -, g5, g6⟩ := hS k n s (Decode.toN φ) hk hs0 (isKCNF_toN hφ.1 hne)
  refine ⟨outTau k n (tauOf s) (Decode.toN φ), _, hM k n s φ hk hs0 hφ hne, g2, ?_, g5, fun Ψ hΨ v => ?_, ?_⟩
  · refine g3.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    have h2 : ((C₀ + 81 : ℕ) : ℝ) ≤ (ε : ℝ) * (2 : ℝ) ^ s := by rwa [div_le_iff₀ h0R, mul_comm] at hsC
    have h3 : (1 : ℝ) ≤ ((C₀ + 81 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ C₀ + 81)
    rw [div_le_iff₀ hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · calc (occN Ψ v : ℝ) ≤ ((2 ^ betaU k s : ℕ) : ℝ) := by exact_mod_cast g6 Ψ hΨ v
      _ = (2 : ℝ) ^ betaU k s := by push_cast; rfl
      _ ≤ _ := hc
  · have hL : (1 : ℝ) ≤ ((encIn s k φ).length : ℝ) + 2 ^ k := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      linarith [Nat.cast_nonneg (α := ℝ) (encIn s k φ).length]
    have e1 : ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) := by
      have := mul_div_le_eps (c := C₀) (C := C₀ + 81) (n := n) (s := s) (by omega) h0R hsC
      calc ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) = (2 : ℝ) ^ (((C₀ * (n / 2 ^ s) : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
    have e2 : (((encIn s k φ).length : ℝ) + 2 ^ k) ^ C₀ ≤ (((encIn s k φ).length : ℝ) + 2 ^ k) ^ (C₀ + 81) :=
      pow_le_pow_right₀ hL (by omega)
    have e3 : (C₀ : ℝ) ≤ ((C₀ + 81 : ℕ) : ℝ) := by exact_mod_cast (by omega : C₀ ≤ C₀ + 81)
    calc ((C₀ * ((encIn s k φ).length + 2 ^ k) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
        = (C₀ : ℝ) * (((encIn s k φ).length : ℝ) + 2 ^ k) ^ C₀ * ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((C₀ + 81 : ℕ) : ℝ) * (((encIn s k φ).length : ℝ) + 2 ^ k) ^ (C₀ + 81) * (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) :=
        mul_le_mul (mul_le_mul e3 e2 (by positivity) (by positivity)) e1 (by positivity) (by positivity)

/-- The theorem on sparsification, parts (a) to (d), from `Prints`, the statement that one machine
prints the outputs (proved as `prints` in Mach/Main.lean). -/
theorem sparsABCD (hP : Prints) : SparsABCD := sparsABCD_of stThmS hP

end SparsificationLemma.Mach
