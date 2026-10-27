/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import OccurM.TiedDefs
public import VariableBound.Paper.Rename.Math
import VariableBound.Paper.Rename.Code
import VariableBound.Paper.Rename.Cert
import Mathlib.SetTheory.Cardinal.Finite

/-! # The preparation

Before the network of a formula is built, the variables that occur are numbered; in the proof of
Theorem A (d) they are renamed as in Section 2, in time polynomial in m log n. This development has
two programs for it, `VariableBound.Rename.rencC` for the compact code and
`VariableBound.Rename.renc` for the code with N in unary, and the formula
`VariableBound.Rename.ren φ`, whose code both return. Here their properties are collected in the
form of `OccurM.Prepares`.

* `prepares_rencC`, `prepares_renc`: the renamed formula that `Prepares` and `PreparesUnary` ask for
  is `ren φ`. `preparation`: the two, and that both programs are polynomial-time.
* `ClausesOccur.someVariableOccurs`: a formula with at least two clauses, none written twice,
  contains a variable. -/

public section

namespace OccurM

open Groundwork MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)

/-- The program for the compact code numbers the variables that occur; it returns the code of
`ren φ`. -/
theorem prepares_rencC : Prepares rencC := fun _ _ φ hk hφ =>
  ⟨ren φ, isKCNF_ren φ hφ, allOccur_ren φ, length_ren φ, numSat_ren φ, rencC_encC φ hk hφ.1⟩

/-- The program for the code with N in unary numbers the variables that occur; it returns the code
of `ren φ`. -/
theorem prepares_renc : PreparesUnary renc := fun _ _ φ hk hφ =>
  ⟨ren φ, isKCNF_ren φ hφ, allOccur_ren φ, length_ren φ, numSat_ren φ, renc_enc φ hk hφ.1⟩

/-- The two named preparations number the variables that occur, and they are polynomial-time. -/
theorem preparation : PreparationStmt := ⟨prepares_rencC, rencC_polyT, prepares_renc, renc_polyT⟩

end OccurM

namespace ClausesOccur

open MainTheoremForms
open Sat3 (CNF)

/-- A formula with at least two clauses, none written twice, contains a variable: its first two
clauses differ, so one of them is not empty. -/
theorem someVariableOccurs : SomeVariableOccursStmt := by
  intro N φ hnd hlen
  obtain ⟨a, b, t, rfl⟩ : ∃ a b t, φ = a :: b :: t := by
    match φ, hlen with
    | [], h => exact absurd h (by simp)
    | [_], h => exact absurd h (by simp)
    | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩
  have hab : a ≠ b := fun h => by simp [h] at hnd
  obtain ⟨C, hC, l, hl⟩ : ∃ C ∈ a :: b :: t, ∃ l, l ∈ C := by
    rcases a with _ | ⟨l, a⟩
    · rcases b with _ | ⟨l, b⟩
      · exact absurd rfl hab
      · exact ⟨l :: b, by simp, l, by simp⟩
    · exact ⟨l :: a, by simp, l, by simp⟩
  have : Nonempty {i : Fin N // Occurs (a :: b :: t) i} := ⟨⟨l.1, C, hC, l, hl, rfl⟩⟩
  exact Nat.card_pos

end ClausesOccur
