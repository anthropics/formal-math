/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Mach.Defs
import SparsificationLemma.Mach.Cert
import SparsificationLemma.Mach.Len
import CountKSatRate.Pad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # One machine prints the outputs of the sparsification

`prints : Prints` (proof/sparsification/SparsificationLemma/Mach/Defs.lean): one multi-stack Turing
machine of Mathlib with finite alphabets and one constant C, for all widths k ≥ 1 and all precisions
s ≥ `s0U k`, and every k-CNF φ without an empty clause. Started on 1^s 0 1^k 0 code(φ), it halts
with
the code of the list of outputs of the sparsification run with its parameter τ = 2^(4s+17), as in
`Prints` (this τ is not the τ of Definition 2), within C·(length of the input + 2^k)^C·2^(C·⌊n/2^s⌋)
steps, where n is the number of variables of φ.
The machine is the padding machine `CountKSatRate.stPaddedW` for the function `BL` of (input, pad)
and the exponent `eL` (proof/sparsification/SparsificationLemma/Mach/Walk.lean). Both are
polynomial-time (proof/sparsification/SparsificationLemma/Mach/Cert.lean), and `BL` writes the
outputs (proof/sparsification/SparsificationLemma/Mach/Len.lean). The machine takes at most q·(|x| +
2^(eL x) + 1)^q steps; `time_le` compares this with the bound: 2^(eL x) = 2^⌊n/2^s⌋·2^k·(2^b)³·512,
where b is the number of binary digits of |x|, and 2^b ≤ 2|x|. -/

public section

namespace SparsificationLemma.Mach

open Groundwork CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

/-- 2 to the number of binary digits of N ≥ 1 is at most 2N. -/
theorem two_pow_size_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ Nat.size N ≤ 2 * N := by
  have h1 : 0 < Nat.size N := Nat.size_pos.2 hN
  have h2 : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.1 (by omega)
  obtain ⟨z, hz⟩ : ∃ z, Nat.size N = z + 1 := ⟨Nat.size N - 1, by omega⟩
  rw [hz] at h2 ⊢
  rw [pow_succ]
  simp only [Nat.add_sub_cancel] at h2
  omega

/-- The time of the padding machine is within the bound of the statement, with C = q·4097^q + 4q. -/
theorem time_le (q a k : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    q * (N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1) ^ q ≤ (q * 4097 ^ q + 4 * q) * (N + 2 ^ k) ^ (q * 4097 ^ q + 4 * q) * 2 ^ ((q * 4097 ^ q + 4 * q) * a) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = N + 2 ^ k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ a := ⟨_, rfl⟩
  have hK1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hA1 : 1 ≤ A := hA ▸ Nat.one_le_two_pow
  have hY1 : 1 ≤ Y := by omega
  have hZ : 2 ^ Nat.size N ≤ 2 * Y := (two_pow_size_le hN).trans (by omega)
  have e0 : 2 ^ (a + k + 3 * Nat.size N + 9) = A * 2 ^ k * (2 ^ Nat.size N) ^ 3 * 512 := by
    rw [pow_add, pow_add, pow_add, Nat.mul_comm 3, pow_mul, ← hA]
    norm_num
  have h1 : A * 2 ^ k * (2 ^ Nat.size N) ^ 3 * 512 ≤ A * Y * (2 * Y) ^ 3 * 512 := by gcongr; omega
  have e1 : A * Y * (2 * Y) ^ 3 * 512 = 4096 * (Y ^ 4 * A) := by ring
  have h2 : Y ≤ Y ^ 4 * A := (Nat.le_self_pow (by norm_num) Y).trans (Nat.le_mul_of_pos_right _ hA1)
  have h3 : N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1 ≤ 4097 * (Y ^ 4 * A) := by omega
  have e2 : (4097 * (Y ^ 4 * A)) ^ q = 4097 ^ q * Y ^ (4 * q) * 2 ^ (q * a) := by
    rw [mul_pow, mul_pow, ← pow_mul, hA, ← pow_mul, Nat.mul_comm a q, Nat.mul_assoc]
  rw [← hY]
  calc q * (N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1) ^ q ≤ q * (4097 * (Y ^ 4 * A)) ^ q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 q)
    _ = q * 4097 ^ q * Y ^ (4 * q) * 2 ^ (q * a) := by rw [e2]; ring
    _ ≤ _ := by
      refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right hY1 (Nat.le_add_left _ _))) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ?_))
      exact (Nat.le_mul_of_pos_right q (Nat.pow_pos (by norm_num))).trans (Nat.le_add_right _ _)

/-- **One machine prints the outputs.** One machine and one constant C for all widths k ≥ 1 and all
precisions s ≥ `s0U k`, and every k-CNF φ without an empty clause: on 1^s 0 1^k 0 code(φ) it halts
with the code of the list of outputs of the sparsification
run with its parameter τ = 2^(4s+17) (as in `Prints`; not the τ of Definition 2) within C·(length of
the input + 2^k)^C·2^(C·⌊n/2^s⌋) steps, where n is the number of variables of φ. -/
theorem prints : Prints := by
  obtain ⟨M, q, hfin, hM⟩ := stPaddedW eL BL Cert.polyT_eL Cert.polyT_BL
  refine ⟨M, q * 4097 ^ q + 4 * q, hfin, fun k n s φ hk hs hφ hnil => ?_⟩
  obtain ⟨ev⟩ := hM (encIn s k φ)
  rw [BL_eq k n s φ hk hs hφ hnil, eL_encIn s k n φ hk hφ.1] at ev
  have hN : 1 ≤ (encIn s k φ).length := by rw [length_encIn]; omega
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (time_le q (n / 2 ^ s) k hN)⟩⟩

end SparsificationLemma.Mach
