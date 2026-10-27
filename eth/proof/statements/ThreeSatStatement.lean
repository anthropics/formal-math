/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Computability.TuringMachine.Computable

/-! # ETH for 3-SAT on Mathlib Turing machines (Definition 6): `s₃TM` > 0, the infimum of the δ for which some machine decides 3-SAT in time O(2^{δn})

The Exponential Time Hypothesis for 3-SAT, on Mathlib's own Turing machines (`Turing.FinTM2`:
finitely many stacks).
`Sat3.ETH_TM` says: `s₃TM` > 0, where `s₃TM` is the infimum of the δ for which 3-SAT on n variables
is in time O(2^{δn}).
The end theorem, `MainResults.ethIsFalse` in Solution.lean, is `¬ Sat3.ETH_TM`. This file has
definitions only and imports Mathlib only. -/

@[expose] public section

namespace Sat3

open Turing
open scoped NNReal ENNReal

/-! ### 3-SAT and how an instance is written on the tape -/

/-- A literal on x₀ … xₙ₋₁: a variable, and the value of it that makes the literal true. -/
abbrev Lit (n : ℕ) : Type := Fin n × Bool

/-- A clause is the OR of a list of literals; a formula is the AND of a list of clauses. -/
abbrev CNF (n : ℕ) : Type := List (List (Lit n))

/-- Some assignment makes a literal of every clause true. -/
def Satisfiable {n : ℕ} (φ : CNF n) : Prop := ∃ a : Fin n → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2

/-- An instance of 3-SAT: at most 3 literals per clause, and no clause written twice, so that its
length is bounded in terms of n.
(A Mathlib machine must halt with only its output on its stacks, so it has to pop all of its input,
except perhaps the last
symbol. If clauses could be repeated, no time bound in n alone could hold, and the hypothesis below
would be trivially true.) -/
def Is3CNF {n : ℕ} (φ : CNF n) : Prop := (∀ C ∈ φ, C.length ≤ 3) ∧ φ.Nodup

/-- A slot of a clause as a number: 0 = no literal, 2i+1 = ¬xᵢ, 2i+2 = xᵢ. -/
def slot {n : ℕ} : Option (Lit n) → ℕ
  | none => 0
  | some l => 2 * l.1.val + 1 + l.2.toNat

/-- As a bit string: 1ⁿ 0, then 3 slots per clause, ⌊log₂ (2n)⌋ + 1 bits per slot, low bit first. -/
def enc {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit

/-! ### Time on a Turing machine -/

/-- `M`, started on an instance's code, halts within `t n` steps with the bit «satisfiable» as
output. One step (`TM2.step`) runs
the statement (`TM2.Stmt`) at the current label as far as a `goto` or `halt`: perhaps several pushes
and pops, but a bounded
number for a fixed machine, which has finitely many labels. -/
def DecidesTM (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((enc φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))

/-- «3-SAT is in time O(2^{δn})» on Turing machines: one machine, finite alphabets, one constant. -/
def InTimeTM (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
    DecidesTM M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊

/-- The infimum of the δ for which 3-SAT is in time O(2^{δn}) on Turing machines (∞ if there is no
such δ). -/
noncomputable def s₃TM : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTimeTM δ), (δ : ℝ≥0∞)

/-- The Exponential Time Hypothesis (item 3 of Theorem 1 of Impagliazzo, Paturi, JCSS 62 (2001)), on
Turing machines. -/
def ETH_TM : Prop := 0 < s₃TM

end Sat3
