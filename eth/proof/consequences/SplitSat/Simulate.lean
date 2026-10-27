/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import CountKSat.Host
import ToTuring.Machine.EndTM
import ToTuring.Poly.Basic
import WidthK.Decode
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 5: from steps to time

No sentence of the paper stands behind this file; the paper counts operations. `exists_simulates`: a
machine cut into polynomial-time steps, with a bit as result, is simulated by a Turing machine of
Mathlib with finite alphabets, in the sense of `SplitSat.Simulates`: the overhead is
q·(T+1)·(|x|+S+1)^q.
This is the host for a word as output (`CountKSat.stHostW`) on the machine that returns its bit as a
word of one bit.
`decidesTM_of_simulates`: if the machine decides k-SAT with the exponent δ/2, every Turing machine
that simulates it decides k-SAT within ⌊C·2^{δn}⌋ steps. The code of an instance has length below
(k·2^k+1)·(n+2)^(k+1), so the overhead is a polynomial in n, which is at most a constant times
2^{(δ/2)n}. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping

/-- `Decides M k δ c` stays true when δ and c are made larger. -/
theorem decides_mono {M : StepMachine (List Bool) Bool} {k : ℕ} {δ δ' : ℝ} {c c' : ℕ} (hδ : δ ≤ δ') (hc : c ≤ c') (h : Decides M k δ c) :
    Decides M k δ' c' := by
  intro n φ h3
  obtain ⟨T, b, r, hb, hT⟩ := h n φ h3
  refine ⟨T, b, r.mono le_rfl (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hc)), hb, hT.trans ?_⟩
  have h1 : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have h2 : (2 : ℝ) ^ (δ * n) ≤ (2 : ℝ) ^ (δ' * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)

/-- A machine cut into polynomial-time steps, from words to a bit, is simulated with polynomial
overhead by a Turing machine of Mathlib with finite alphabets. -/
theorem exists_simulates (Ms : StepMachine (List Bool) Bool) (hp : PolyTimeSteps Ms) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M Ms q := by
  obtain ⟨h⟩ := hp
  have := IsPolyT.mapOut (M := Ms) (f := fun b : Bool => [b]) (by fun_prop)
  obtain ⟨N, q, hfin, hN⟩ := stHostW (Stepped.mapOut Ms fun b : Bool => [b])
  exact ⟨N, q, hfin, fun x b T S hr => hN x T S [b] (Stepped.mapOut_runs hr)⟩

/-- If Ms decides k-SAT with the exponent δ/2 and the constant c, and the Turing machine M simulates
Ms with polynomial overhead, then M decides k-SAT within ⌊C·2^{δn}⌋ steps, for some C ≥ c. -/
theorem decidesTM_of_simulates {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {Ms : StepMachine (List Bool) Bool} {M : Turing.TM2ComputableAux Bool Bool} {q c : ℕ}
    (hs : Simulates M Ms q) (h : Decides Ms k (δ / 2) c) : ∃ C : ℕ, c ≤ C ∧ SatK.DecidesTM k M fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = k * 2 ^ k + 1 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 1) ^ q * a ^ ((c + 1) * q) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((k + 1) * ((c + 1) * q)) hδ2
  refine ⟨q * (c + 1) * (G * C₁) + c, Nat.le_add_left _ _, fun n φ h3 => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n φ h3
  obtain ⟨ev⟩ := hs _ b T _ hr
  obtain ⟨X, hX⟩ : ∃ X, X = (SatK.enc k φ).length + 1 := ⟨_, rfl⟩
  have hXa : X ≤ a * (n + 2) ^ (k + 1) := by rw [hX, ha]; exact DecodeK.length_enc_succ_le h3
  have hX1 : 1 ≤ X := by omega
  have hbase : (SatK.enc k φ).length + c * ((SatK.enc k φ).length + 1) ^ c + 1 ≤ (c + 1) * X ^ (c + 1) := by
    rw [← hX]
    have e1 : X ≤ X ^ (c + 1) := Nat.le_self_pow (by omega) _
    have e2 : X ^ c ≤ X ^ (c + 1) := Nat.pow_le_pow_right hX1 (by omega)
    have e3 : c * X ^ c ≤ c * X ^ (c + 1) := Nat.mul_le_mul_left _ e2
    have e4 : (c + 1) * X ^ (c + 1) = c * X ^ (c + 1) + X ^ (c + 1) := by ring
    omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ((SatK.enc k φ).length + c * ((SatK.enc k φ).length + 1) ^ c + 1) ^ q := ⟨_, rfl⟩
  have hpow : Y ≤ G * (n + 2) ^ ((k + 1) * ((c + 1) * q)) := by
    rw [hY, hG]
    calc ((SatK.enc k φ).length + c * ((SatK.enc k φ).length + 1) ^ c + 1) ^ q ≤ ((c + 1) * X ^ (c + 1)) ^ q := Nat.pow_le_pow_left hbase q
      _ = (c + 1) ^ q * X ^ ((c + 1) * q) := by rw [mul_pow, ← pow_mul]
      _ ≤ (c + 1) ^ q * (a * (n + 2) ^ (k + 1)) ^ ((c + 1) * q) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hXa _)
      _ = (c + 1) ^ q * a ^ ((c + 1) * q) * (n + 2) ^ ((k + 1) * ((c + 1) * q)) := by rw [mul_pow, ← pow_mul, mul_assoc]
  rw [← hY] at ev
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hCn := hC₁ n
  rw [← hE] at hCn hT
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hle : q * (T + 1) * Y ≤ ⌊((q * (c + 1) * (G * C₁) + c : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * E := by nlinarith
    have h2 : (Y : ℝ) ≤ (G : ℝ) * (C₁ * E) := by
      have h5 : (Y : ℝ) ≤ (G : ℝ) * ((n : ℝ) + 2) ^ ((k + 1) * ((c + 1) * q)) := by exact_mod_cast hpow
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

end SplitSat
