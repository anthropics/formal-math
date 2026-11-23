/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Blocks
import Nc.Cut.Units
import Nc.Cut.Play
import Mathlib
import Nc.LowDegree
import Nc.Tape.Run
import Nc.Tape.Refine

/-!
# The cut: definitions

An automaton (`mu`, `i`, `e`) with tapes `S` and one input, `K` blocks of `T` steps. Parties: the blocks
(`Fin.castAdd K κ`) and `K` input parties (`Fin.natAdd K κ`), which hold the parts of the input, `ℓ` letters each.
The input is treated as one more tape (`none`), written by the input parties and read by the blocks.
All segments written by party `a` and read by party `b` are put into one string, which is cut into units.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A K U0 E U1 : ℕ}

section Start

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T ub : ℕ) {c : ℕ} (cb : Option Γ → Fin c → Bool)

/-- The segments on all tapes (the tape `none` is the input) as one word with separators. -/
noncomputable def joinSeg (X : Option S → List Γ) : List (Option Γ) :=
  (univ : Finset (Option S)).toList.flatMap fun s => (X s).map some ++ [none]

/-- The string from one party to another. -/
noncomputable def strOf (X : Option S → List Γ) : List Bool := bitsOf cb (joinSeg X)

/-- What a block emits, if `R s b` is what it writes for party `b` on tape `s` and `C s b` what it reads from
party `b` on tape `s`. -/
def vec (R C : Option S → Fin A → List Γ) : Ch S Unit → List Γ
  | .tp s b => if b then cat (C (some s)) else cat (R (some s))
  | .inp _ => cat (C none)

open Classical in
/-- The weight of what party `p` writes and reads: a block from state `q κ` to `q (κ + 1)`, or an input party with
its part of the input. -/
noncomputable def partyW (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) : F :=
  Fin.addCases (motive := fun _ => F)
    (fun κ => if ∀ b, R none b = [] then blockW mu T (q κ.castSucc) (q κ.succ) (vec R C) else 0)
    (fun κ => if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1 else 0) p

/-- The row data of a party on a tape: whether it writes nothing on the tape, the first and the last party that
reads what it writes (if it writes nothing: twice the last party of the rows before). -/
abbrev RowData (A : ℕ) := Bool × Fin A × Fin A

/-- The segments written by a party on a tape are as the row data say. -/
def RowOk (d : RowData A) (X : Fin A → List Γ) : Prop :=
  if d.1 then ∀ b, X b = [] else X d.2.1 ≠ [] ∧ X d.2.2 ≠ [] ∧ ∀ b, X b ≠ [] → d.2.1 ≤ b ∧ b ≤ d.2.2

/-- The last party of the row before (0 for the first row). -/
def prevHi (ρ : Fin A → RowData A) (p : Fin A) : ℕ :=
  if h : p.1 = 0 then 0 else (ρ ⟨p.1 - 1, by omega⟩).2.2.1

/-- The row data on all tapes are those of a staircase. -/
def ValidRows (ρ : Option S → Fin A → RowData A) : Prop :=
  ∀ s p, if (ρ s p).1 then (ρ s p).2.1.1 = prevHi (ρ s) p ∧ (ρ s p).2.2.1 = prevHi (ρ s) p
    else prevHi (ρ s) p ≤ (ρ s p).2.1.1 ∧ (ρ s p).2.1 ≤ (ρ s p).2.2

/-- The parts of a word: `ℓ` letters each. -/
def parts (ℓ : ℕ) (u : List Γ) (κ : Fin K) : List Γ := (u.drop (κ.1 * ℓ)).take ℓ

end Start

section Moves

variable {I : Type} {lam : ℕ} (lab : I → Fin lam → Bool)

/-- The string on a side: for every block the label and the string of the law. -/
def sideString {B : ℕ} (len : I → ℕ) (i : Fin B → I) (g : ∀ k, Fin (len (i k)) → Bool) : List Bool :=
  (List.ofFn fun k => List.ofFn (lab (i k)) ++ List.ofFn (g k)).flatten

end Moves

end Nc.Cut
