/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FreeCode.Defs
import FreeCode.Code
import SplitSat.Leaf
import ToTuring.Machine.EndTM
import Mathlib.Tactic

/-! # Definition 6 with the code that does not depend on k: from a procedure on (n in unary, formula) to a Turing machine on codes

No sentence of the paper stands behind this file; the paper fixes no code and counts operations.
* `stBehindReader` (= `FreeCode.StBehindReader`): a procedure that decides w-SAT on (N in unary,
  formula), put behind any reader of the code, decides w-SAT on codes, within the same number of
  steps and the same sizes.
* `overhead_le`: for a k-CNF on n variables with code x, and states of size at most c·(n+2)^c, the
  factor (|x| + S + 1)^q of `SplitSat.Simulates` is at most a constant times a power of n + 2.
* `decidesTM_of_simulates`: if the machine decides w-SAT on codes with the exponent δ/2, every
  Turing machine that simulates it decides w-SAT within ⌊C·2^{δn}⌋ steps. The computation is that of
  `SplitSat.decidesTM_of_simulates`, for this code. -/

public section

namespace FreeCode

open Groundwork Groundwork.Prog Paper SplitSat

/-- **For every reader and every procedure D** that decides w-SAT on (N in unary, formula) with the
exponent δ: D behind the reader decides w-SAT on the code, within the same number of steps. This is
the statement `FreeCode.StBehindReader`. -/
theorem stBehindReader : StBehindReader := fun dec hdec w D δ c h n φ h3 => by
  obtain ⟨T, b, r, hb, hT⟩ := h n (Decode.toN φ) (fun E hE => by
    obtain ⟨⟨C, hC, hl⟩, h'⟩ := Decode.mem_toN hE
    exact ⟨hl ▸ h3.1 C hC, h'⟩) (nodup_toN h3.2)
  refine ⟨T, b, Stepped.mapIn_runs ?_, hb.trans (Decode.satN_toN φ), hT⟩
  rw [hdec n φ]
  exact r

/-- `DecidesFree Ms w δ c` stays true when δ and c are made larger. -/
theorem decidesFree_mono {Ms : StepMachine (List Bool) Bool} {w : ℕ} {δ δ' : ℝ} {c c' : ℕ} (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesFree Ms w δ c) :
    DecidesFree Ms w δ' c' := by
  intro n φ h3
  obtain ⟨T, b, r, hb, hT⟩ := h n φ h3
  refine ⟨T, b, r.mono le_rfl (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hc)), hb, hT.trans ?_⟩
  have h1 : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have h2 : (2 : ℝ) ^ (δ * n) ≤ (2 : ℝ) ^ (δ' * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)

/-- The factor of the simulation that is polynomial: for the code x of a k-CNF on n variables and S =
c·(n+2)^c, (|x| + S + 1)^q ≤ (2^k·(k+1) + 2 + c)^q·(n+2)^((k+1+c)·q). -/
theorem overhead_le {k n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF k φ) (c q : ℕ) :
    ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q ≤ (2 ^ k * (k + 1) + 2 + c) ^ q * (n + 2) ^ ((k + 1 + c) * q) := by
  have h1 := length_enc_succ_le h3
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ k * (k + 1) + 2 := ⟨_, rfl⟩
  rw [← hA] at h1 ⊢
  have e1 : (n + 2) ^ (k + 1) ≤ (n + 2) ^ (k + 1 + c) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (n + 2) ^ c ≤ (n + 2) ^ (k + 1 + c) := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : A * (n + 2) ^ (k + 1) ≤ A * (n + 2) ^ (k + 1 + c) := Nat.mul_le_mul_left _ e1
  have e4 : c * (n + 2) ^ c ≤ c * (n + 2) ^ (k + 1 + c) := Nat.mul_le_mul_left _ e2
  have e5 : (A + c) * (n + 2) ^ (k + 1 + c) = A * (n + 2) ^ (k + 1 + c) + c * (n + 2) ^ (k + 1 + c) := by ring
  calc ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q ≤ ((A + c) * (n + 2) ^ (k + 1 + c)) ^ q := Nat.pow_le_pow_left (by omega) q
    _ = (A + c) ^ q * (n + 2) ^ ((k + 1 + c) * q) := by rw [mul_pow, ← pow_mul]

/-- A machine that decides k-SAT on codes in time t decides it in every larger time. -/
theorem decidesTM_mono {k : ℕ} {M : Turing.TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (ht : ∀ n, t n ≤ t' n) (h : SatFree.DecidesTM k M t) :
    SatFree.DecidesTM k M t' := fun n φ h3 => by
  obtain ⟨b, hb, ⟨ev⟩⟩ := h n φ h3
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (ht n)⟩⟩⟩

/-- If Ms decides w-SAT on codes with the exponent δ/2 and the constant c, and the Turing machine M
simulates Ms with polynomial overhead, then M decides w-SAT on codes within ⌊C·2^{δn}⌋ steps, for
some C ≥ c. -/
theorem decidesTM_of_simulates {w : ℕ} {δ : ℝ} (hδ : 0 < δ) {Ms : StepMachine (List Bool) Bool} {M : Turing.TM2ComputableAux Bool Bool} {q c : ℕ}
    (hs : Simulates M Ms q) (h : DecidesFree Ms w (δ / 2) c) : ∃ C : ℕ, c ≤ C ∧ SatFree.DecidesTM w M fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨G, hG⟩ : ∃ G, G = (2 ^ w * (w + 1) + 2 + c) ^ q := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((w + 1 + c) * q) hδ2
  refine ⟨q * (c + 1) * (G * C₁) + c, Nat.le_add_left _ _, fun n φ h3 => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n φ h3
  obtain ⟨ev⟩ := hs _ b T _ hr
  have hpow := overhead_le h3 c q
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q := ⟨_, rfl⟩
  rw [← hY, ← hG] at hpow
  rw [← hY] at ev
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hCn := hC₁ n
  rw [← hE] at hCn hT
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hle : q * (T + 1) * Y ≤ ⌊((q * (c + 1) * (G * C₁) + c : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * E := by nlinarith
    have h2 : (Y : ℝ) ≤ (G : ℝ) * (C₁ * E) := by
      have h5 : (Y : ℝ) ≤ (G : ℝ) * ((n : ℝ) + 2) ^ ((w + 1 + c) * q) := by exact_mod_cast hpow
      exact h5.trans (mul_le_mul_of_nonneg_left hCn (Nat.cast_nonneg _))
    have h7 : (2 : ℝ) ^ (δ * n) = E * E := by
      rw [hE, ← Real.rpow_add two_pos]; congr 1; ring
    have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have hEE : (0 : ℝ) ≤ E * E := by positivity
    push_cast
    rw [h7]
    calc (q : ℝ) * ((T : ℝ) + 1) * (Y : ℝ) ≤ (q : ℝ) * (((c : ℝ) + 1) * E) * ((G : ℝ) * (C₁ * E)) := by gcongr
      _ = ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁)) * (E * E) := by ring
      _ ≤ ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁) + c) * (E * E) := mul_le_mul_of_nonneg_right (by linarith) hEE
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩

end FreeCode
