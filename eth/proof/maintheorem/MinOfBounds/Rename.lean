/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MinOfBounds.Defs
public import VariableBound.Paper.Rename.Math
public import VariableBound.Paper.Rename.Compact
import VariableBound.Paper.Rename.Code
import WidthK.Decode
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup

/-! # Corollary 11 from Theorem A (c) and Theorem D (b): the renaming

This file proves the renaming to the paper's convention: the variables that occur are renamed to
x_1, …, x_n, in time polynomial in the length of the formula.

* `renamedCode_eq`: the bit string `MinOfBounds.renamedCode k φ` is `SatM.enc k (ren φ)`, where
  `VariableBound.Rename.ren φ` is the formula φ with every variable replaced by its position in the
  list of the variables that occur.
* `renamedCodeIsTheCodeOfARenaming`: the properties of `ren φ` that the proof uses; each of them is
  a theorem of proof/variables/VariableBound/Paper/Rename/Math.lean.
* `renamingFrontEndExists`: the polynomial-time function is `VariableBound.Rename.rencC` of
  proof/variables/VariableBound/Paper/Rename/Compact.lean.
* `numOcc_le_mul`: n ≤ m·k, because every variable that occurs stands in one of the m clauses, which
  have at most k literals each.
* `renamedCodeIsPolynomial`: the code of the renamed formula is at most twice as long as the compact
  code. It has k + n + 2 + m·k·(⌊log₂(2n)⌋ + 1) bits and the compact code has k + w + 2 + m·k·w bits
  with w = ⌊log₂(2V)⌋ + 1; here n ≤ V and n ≤ m·k. -/

public section

namespace MinOfBounds

open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

/-- The code of the renamed formula is `SatM.enc k (ren φ)`. No hypothesis on k or φ. -/
theorem renamedCode_eq (k : ℕ) {V : ℕ} (φ : CNF V) : renamedCode k φ = SatM.enc k (ren φ) := by
  rw [renamedCode, ← encN_toN, toN_ren, renF, ← length_occL, List.map_const']

/-- The formula φ' is `VariableBound.Rename.ren φ`. -/
theorem renamedCodeIsTheCodeOfARenaming : RenamedCodeIsTheCodeOfARenaming := fun k _ φ =>
  ⟨ren φ, renamedCode_eq k φ, toN_ren φ, nodup_occL _, fun _ => ⟨exists_of_mem_occL φ, fun ⟨_, hi, ho⟩ => hi ▸ (val_mem_occL φ).2 ho⟩,
    length_ren φ, isKCNF_ren φ, allOccur_ren φ, numSat_ren φ⟩

/-- The function `VariableBound.Rename.rencC` is polynomial-time and renames the variables that
occur. -/
theorem rencC_renames : RenamesTheVariablesThatOccur rencC := fun k _ φ hk hφ => (rencC_encC φ hk hφ.1).trans (renamedCode_eq k φ).symm

/-- There is a polynomial-time function that renames the variables that occur:
`VariableBound.Rename.rencC`. -/
theorem renamingFrontEndExists : RenamingFrontEndExists := ⟨rencC, rencC_polyT, rencC_renames⟩

/-- A list of m clauses with at most k literals each has at most m·k literals. -/
theorem length_literals_le {k : ℕ} (ψ : List (List (ℕ × Bool))) (h : ∀ C ∈ ψ, C.length ≤ k) : (ψ.flatMap fun C => C.map fun l => l.1).length ≤ ψ.length * k := by
  induction ψ with
  | nil => simp
  | cons C ψ ih =>
    have h1 := h C List.mem_cons_self
    have h2 := ih fun D hD => h D (List.mem_cons_of_mem _ hD)
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, Nat.succ_mul]
    omega

/-- n ≤ m·k: in a formula with m clauses of at most k literals each, at most m·k variables occur. -/
theorem numOcc_le_mul {k V : ℕ} (φ : CNF V) (h : ∀ C ∈ φ, C.length ≤ k) : numOcc φ ≤ φ.length * k := by
  have h1 : ∀ C ∈ toN φ, C.length ≤ k := fun C hC => by
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    rw [List.length_map]
    exact h C' hC'
  have h2 : (toN φ).length = φ.length := List.length_map _
  rw [← length_occL, ← h2]
  exact (List.dedup_sublist _).length_le.trans (length_literals_le _ h1)

/-- The code of the renamed formula is at most twice as long as the compact code, for a formula with
at most k literals in every clause. -/
theorem length_renamedCode_le {k V : ℕ} (φ : CNF V) (h : ∀ C ∈ φ, C.length ≤ k) : (renamedCode k φ).length ≤ 2 * (encC k φ).length := by
  have h1 := numOcc_le_mul φ h
  have h2 : Nat.log2 (2 * numOcc φ) ≤ Nat.log2 (2 * V) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.mul_le_mul_left _ (numOcc_le φ))
  have h3 : φ.length * (k * (Nat.log2 (2 * numOcc φ) + 1)) ≤ φ.length * (k * (Nat.log2 (2 * V) + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.succ_le_succ h2))
  have h4 : φ.length * k ≤ φ.length * (k * (Nat.log2 (2 * V) + 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  rw [renamedCode_eq, lengthEncC, SatM.enc, List.length_append, List.length_replicate, List.length_cons, DecodeK.length_enc, length_ren]
  omega

/-- The number a is 2. -/
theorem renamedCodeIsPolynomial : RenamedCodeIsPolynomial :=
  ⟨2, fun _ _ φ _ hφ => (length_renamedCode_le φ hφ.1).trans (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _))⟩

end MinOfBounds
