/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FreeCode.Defs
import WidthK.Decode
import Mathlib.Tactic

/-! # Definition 6 with the code that does not depend on k: one literal, and the length of the code

No sentence of the paper stands behind this file: the paper fixes no code.
* `slotDec_encLit`: the bits of a literal, read as a number (`ofWord`) and then as a literal
  (`Decode.slotDec`), give the literal back. The number of a literal is below 2^(⌊log₂ 2n⌋+1), so
  its bits determine it.
* `stLength` (= `FreeCode.StLength`): the code of a k-CNF on n variables has length below (2^k·(k+1) + 2)·(n+2)^(k+1).
  It uses that a k-CNF in which no clause is written twice has at most (2n+1)^k clauses
  (`DecodeK.IsKCNF.length_le`).
The first three lemmas repeat, for a literal rather than an optional literal, lemmas of
proof/machines/StepMachines/Prog/Decode.lean that are not visible outside that file; so do
`takeWhile_header` and `dropWhile_header` in Reader.lean. -/

public section

namespace FreeCode

open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

/-- The ℓ lowest binary digits of y, lowest first, are its bits number 0 to ℓ − 1. -/
theorem toWord_eq (ℓ y : ℕ) : toWord ℓ y = (List.range ℓ).map y.testBit := by
  induction ℓ generalizing y with
  | zero => rfl
  | succ ℓ ih =>
    rw [toWord, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.testBit_zero]
    · refine List.map_congr_left fun i _ => ?_
      simp [Nat.testBit_succ]

/-- The number of a literal on n variables is below 2^(⌊log₂ 2n⌋+1). -/
theorem slot_lt {n : ℕ} (l : Lit n) : slot (some l) < 2 ^ (Nat.log2 (2 * n) + 1) := by
  refine lt_of_le_of_lt ?_ Nat.lt_log2_self
  obtain ⟨i, b⟩ := l
  have := i.2
  cases b <;> simp only [slot, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The number of a literal, read as a literal, gives the literal back, with its variable as a
number. -/
theorem slotDec_slot {n : ℕ} (l : Lit n) : slotDec (slot (some l)) = some (l.1.val, l.2) := by
  obtain ⟨i, b⟩ := l
  cases b
  · simp [slotDec, slot]
  · simp [slotDec, slot]
    omega

/-- The bits of a literal are the ⌊log₂ 2n⌋ + 1 lowest binary digits of its number. -/
theorem encLit_eq {n : ℕ} (l : Lit n) : SatFree.encLit l = toWord (Nat.log2 (2 * n) + 1) (slot (some l)) := by
  rw [toWord_eq, SatFree.encLit]

/-- A literal is written with ⌊log₂ 2n⌋ + 1 bits. -/
theorem length_encLit {n : ℕ} (l : Lit n) : (SatFree.encLit l).length = Nat.log2 (2 * n) + 1 := by
  simp [SatFree.encLit]

/-- The bits of a literal, read as a number and then as a literal, give the literal back. -/
theorem slotDec_encLit {n : ℕ} (l : Lit n) : slotDec (ofWord (SatFree.encLit l)) = some (l.1.val, l.2) := by
  rw [encLit_eq, ofWord_toWord (slot_lt l), slotDec_slot]

/-- A clause of s literals is written with 2 + s·(⌊log₂ 2n⌋ + 2) bits. -/
theorem length_encClause {n : ℕ} (C : List (Lit n)) : (SatFree.encClause C).length = 2 + C.length * (Nat.log2 (2 * n) + 2) := by
  have h : (C.flatMap fun l => true :: SatFree.encLit l).length = C.length * (Nat.log2 (2 * n) + 2) := by
    induction C with
    | nil => simp
    | cons l C ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, ih, length_encLit]
      ring
  simp only [SatFree.encClause, List.length_cons, List.length_append, h, List.length_nil]
  omega

/-- The clauses of a formula with at most k literals per clause are written with at most m·(2 +
k·(⌊log₂ 2n⌋ + 2)) bits, m the number of clauses. -/
theorem length_clauses_le {k n : ℕ} (φ : CNF n) (h : ∀ C ∈ φ, C.length ≤ k) :
    (φ.flatMap SatFree.encClause).length ≤ φ.length * (2 + k * (Nat.log2 (2 * n) + 2)) := by
  induction φ with
  | nil => simp
  | cons C φ ih =>
    have h1 := ih fun D hD => h D (List.mem_cons_of_mem _ hD)
    have h2 : C.length * (Nat.log2 (2 * n) + 2) ≤ k * (Nat.log2 (2 * n) + 2) := Nat.mul_le_mul_right _ (h C List.mem_cons_self)
    obtain ⟨X, hX⟩ : ∃ X, X = 2 + k * (Nat.log2 (2 * n) + 2) := ⟨_, rfl⟩
    rw [← hX] at h1 ⊢
    have e : (φ.length + 1) * X = φ.length * X + X := by ring
    rw [List.flatMap_cons, List.length_append, List.length_cons, length_encClause, e]
    omega

/-- The length of the code, plus one, of a k-CNF on n variables is at most (2^k·(k+1) + 2)·(n+2)^(k+1). -/
theorem length_enc_succ_le {k n : ℕ} {φ : CNF n} (h : SatK.IsKCNF k φ) : (SatFree.enc φ).length + 1 ≤ (2 ^ k * (k + 1) + 2) * (n + 2) ^ (k + 1) := by
  have h1 := length_clauses_le φ h.1
  have h2 : φ.length ≤ 2 ^ k * (n + 2) ^ k := by
    calc φ.length ≤ (2 * n + 1) ^ k := DecodeK.IsKCNF.length_le h
      _ ≤ (2 * (n + 2)) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * (n + 2) ^ k := mul_pow _ _ _
  have h3 : 2 + k * (Nat.log2 (2 * n) + 2) ≤ (k + 1) * (n + 2) := by
    have a1 : k * (Nat.log2 (2 * n) + 2) ≤ k * (n + 2) := Nat.mul_le_mul_left _ (by have := bitLen_le n; omega)
    have a2 : (k + 1) * (n + 2) = k * (n + 2) + (n + 2) := by ring
    omega
  have h4 : φ.length * (2 + k * (Nat.log2 (2 * n) + 2)) ≤ 2 ^ k * (k + 1) * (n + 2) ^ (k + 1) := by
    calc φ.length * (2 + k * (Nat.log2 (2 * n) + 2)) ≤ 2 ^ k * (n + 2) ^ k * ((k + 1) * (n + 2)) := Nat.mul_le_mul h2 h3
      _ = 2 ^ k * (k + 1) * (n + 2) ^ (k + 1) := by ring
  have h5 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h6 : (2 ^ k * (k + 1) + 2) * (n + 2) ^ (k + 1) = 2 ^ k * (k + 1) * (n + 2) ^ (k + 1) + 2 * (n + 2) ^ (k + 1) := by ring
  simp only [SatFree.enc, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- The length of the code of a k-CNF on n variables is polynomial in n, for fixed k: the statement
`FreeCode.StLength`. -/
theorem stLength : StLength := fun k => ⟨2 ^ k * (k + 1) + 2, k + 1, fun _ _ h => length_enc_succ_le h⟩

end FreeCode
