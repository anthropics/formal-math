/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCountedStatement
import GeneralPieces.DefGenPieces.ToPure
import Mathlib.Tactic

/-! # Pieces on counted operations: first facts

The number of operations `steps` and the bound `room` on the states grow with c and with λ. From
this: pieces with parameters (ρ, c) are pieces with parameters (ρ', c') for ρ ≤ ρ' < 1 and c ≤ c',
with the same algorithm (`growWithTheParameters`).
Clauses (a), (b) and the sizes of (c) give the pure form `Pieces.Family.Is` (`toPure`): a sum over
the words of n bits is a sum over the functions from {0, …, n − 1} to the bits. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-! ### The bounds grow -/

/-- 2^{cλ} grows with c. -/
theorem steps_le_of_le {c c' : ℕ} (lam : ℕ) (h : c ≤ c') : steps c lam ≤ steps c' lam :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

/-- 2^{cλ} grows with λ. -/
theorem steps_le_of_length_le (c : ℕ) {lam lam' : ℕ} (h : lam ≤ lam') : steps c lam ≤ steps c lam' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h)

/-- (2λ)^c grows with c, for λ ≥ 1. -/
theorem pow_two_mul_le {c c' lam : ℕ} (hl : 1 ≤ lam) (h : c ≤ c') : (2 * lam) ^ c ≤ (2 * lam) ^ c' :=
  Nat.pow_le_pow_right (by omega) h

/-- The bound on the states grows with c, for λ ≥ 1. -/
theorem room_le_of_le {c c' lam : ℕ} (hl : 1 ≤ lam) (h : c ≤ c') : room c lam ≤ room c' lam :=
  Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add (steps_le_of_le lam h) (pow_two_mul_le hl h)) 8) (Nat.add_le_add_right (pow_two_mul_le hl h) 8)

/-- The bound on the states grows with λ. -/
theorem room_le_of_length_le (c : ℕ) {lam lam' : ℕ} (h : lam ≤ lam') : room c lam ≤ room c lam' :=
  have h1 : (2 * lam) ^ c ≤ (2 * lam') ^ c := Nat.pow_le_pow_left (by omega) c
  Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add (steps_le_of_length_le c h) h1) 8) (Nat.add_le_add_right h1 8)

/-! ### The oracle -/

/-- The oracle answers only for λ ≥ 1, and then with the right answer. -/
theorem oracle_eq_some {D : Data} {g : List Unit × Question} {a : Answer} (h : D.oracle g = some a) : 1 ≤ g.1.length ∧ D.answer g.1.length g.2 = some a := by
  unfold Data.oracle at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-! ### Growing parameters -/

/-- Clauses (a), (b) and the sizes of (c) only weaken when ρ or c grows. -/
theorem Data.Is.grow {D : Data} {ρ ρ' : ℝ} {c c' : ℕ} (h : D.Is ρ c) (hρ : ρ ≤ ρ') (hρ' : ρ' < 1) (hc : c ≤ c') : D.Is ρ' c' :=
  have hp : ∀ lam, 1 ≤ lam → (2 : ℤ) ^ (2 * lam) ^ c ≤ 2 ^ (2 * lam) ^ c' := fun _ hl => pow_le_pow_right₀ (by norm_num) (pow_two_mul_le hl hc)
  { rho_ge := h.rho_ge.trans hρ
    rho_lt := hρ'
    c_pos := h.c_pos.trans hc
    d_pos := h.d_pos
    sum := h.sum
    row := h.row
    col := h.col
    caps := fun lam hl i hi => (h.caps lam hl i hi).trans (by
      have h0 := GeneralPieces.DefGenPieces.logb_nonneg hl
      have h1 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
      have h2 : (c : ℝ) ≤ c' := by exact_mod_cast hc
      have h3 : 4 * ρ * lam ≤ 4 * ρ' * lam := mul_le_mul_of_nonneg_right (by linarith) h1
      have h4 : (c : ℝ) * Real.logb 2 (2 * lam) ≤ c' * Real.logb 2 (2 * lam) := mul_le_mul_of_nonneg_right h2 h0
      linarith)
    card := fun lam hl => (h.card lam hl).trans (pow_two_mul_le hl hc)
    size_d := fun lam hl => (h.size_d lam hl).trans_le (hp lam hl)
    size_I := fun lam hl i hi => (h.size_I lam hl i hi).trans_le (hp lam hl)
    size_A := fun lam hl i hi x y u v => (h.size_A lam hl i hi x y u v).trans_le (hp lam hl)
    size_f := fun lam hl i hi tr side z θ hθ => (h.size_f lam hl i hi tr side z θ hθ).trans_le (hp lam hl) }

/-- An algorithm within 2^{cλ} operations is one within 2^{c'λ} operations, for c ≤ c'. -/
theorem Computes.grow {Alg : Stepped (List Unit × Question) Answer} {D : Data} {c c' : ℕ} (h : Computes Alg D c) (hc : c ≤ c') : Computes Alg D c' :=
  fun g a hg => (h g a hg).mono (steps_le_of_le _ hc) (room_le_of_le (oracle_eq_some hg).1 hc)

/-- `GrowWithTheParameters`: pieces with parameters (ρ, c) are pieces with parameters (ρ', c') for ρ
≤ ρ' < 1 and c ≤ c'. -/
theorem growWithTheParameters : GrowWithTheParameters := fun _ _ _ _ _ _ hρ hρ' hc h =>
  ⟨h.is.grow hρ hρ' hc, h.polyTimeSteps, h.computes.grow hc⟩

/-! ### The pure form -/

/-- `ToPure`: clauses (a), (b) and the sizes of (c) as pure mathematics. -/
theorem toPure : ToPure := fun D _ _ h lam hl =>
  { d_pos := h.d_pos lam hl
    sum_eq := h.sum lam hl
    row := fun i hi => ⟨fun z θ => D.fn lam false false i z (bitsOf θ), fun z θ => D.fn lam false true i z (bitsOf θ),
      fun z z' => (h.row lam hl i hi z.1 z.2 z'.1 z'.2).trans (GeneralPieces.DefGenPieces.sum_bitsOf (n := (D.fam lam).crow i) fun θ => D.fn lam false false i z θ * D.fn lam false true i z' θ).symm,
      fun z θ => h.size_f lam hl i hi false false z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ)),
      fun z θ => h.size_f lam hl i hi false true z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ))⟩
    col := fun i hi => ⟨fun z θ => D.fn lam true false i z (bitsOf θ), fun z θ => D.fn lam true true i z (bitsOf θ),
      fun z z' => (h.col lam hl i hi z.1 z'.1 z.2 z'.2).trans (GeneralPieces.DefGenPieces.sum_bitsOf (n := (D.fam lam).ccol i) fun θ => D.fn lam true false i z θ * D.fn lam true true i z' θ).symm,
      fun z θ => h.size_f lam hl i hi true false z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ)),
      fun z θ => h.size_f lam hl i hi true true z _ (mem_words.2 (GeneralPieces.Trim.length_bitsOf θ))⟩
    caps := h.caps lam hl
    card_I := h.card lam hl
    abs_d := h.size_d lam hl
    abs_I := h.size_I lam hl
    abs_A := h.size_A lam hl }

end PiecesCounted
