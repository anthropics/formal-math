/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
public import CountKSat.Defs
public import Eight.SecProof_NetworkDefs
public import StepMachines.Prog.Decode
public import ToTuring.PolyT

/-! # Variables that do not occur: «Z·2^{n'}» (definitions and statements only)

The paper uses one fact in three places. Section 6: «Φ has Z·2^{n'} satisfying assignments, where n'
of the n variables do not occur in Φ».
Appendix C: an output in which v of the n variables occur «has Z·2^{n−v} satisfying assignments».
After Corollary 11: the same with N − n.
Here Z is, as in Section 6, «the number of assignments of the variables occurring in Φ that satisfy
Φ» (`Eight.numSat Φ`), and the number of satisfying assignments on x₀ … xₙ₋₁ is
`CountKSat.cntN n Φ`, the form in which the counting programs of this development speak.
A formula is a list of clauses, a clause a list of literals (variable, value that makes the literal
true), with natural numbers as variables (`Groundwork.Prog.Fml`).

For formulas with variables in `Fin N` the identity is stated in MainTheoremFormsStatement.lean and
proved in proof/variables/VariableBound/Paper/Rename/Math.lean. This file adds the form for
programs, the bridge between the two forms (`StSameAsFin`),
and the certificate that the factor is computed in polynomial time when n is given in unary
(`StTimesFreeCert`).
This file has no theorem: every statement is a `def St… : Prop`; proof/consequences/Occ/Main.lean
proves them. -/

@[expose] public section

namespace Occ

open Groundwork Groundwork.Prog CountKSat

/-- All variables of Φ are among x₀ … xₙ₋₁. -/
def Below (n : ℕ) (Φ : Fml) : Prop := ∀ C ∈ Φ, ∀ l ∈ C, l.1 < n

/-- v: the number of variables that occur in Φ. -/
def numOcc (Φ : Fml) : ℕ := (Eight.occurring Φ).card

/-- At most n variables occur in a formula on x₀ … xₙ₋₁. -/
def StNumOccLe : Prop := ∀ (n : ℕ) (Φ : Fml), Below n Φ → numOcc Φ ≤ n

/-- **«Z·2^{n'}».** A formula on x₀ … xₙ₋₁ in which v variables occur has Z·2^{n−v} satisfying
assignments, Z the number of assignments of the occurring variables that satisfy it. No condition on
the width or on the number of clauses:
with no clauses, Z = 1 and v = 0, and the number is 2^n. -/
def StCountOcc : Prop := ∀ (n : ℕ) (Φ : Fml), Below n Φ → cntN n Φ = Eight.numSat Φ * 2 ^ (n - numOcc Φ)

/-- With no clauses the number is 2^n. -/
def StCountNil : Prop := ∀ n : ℕ, cntN n [] = 2 ^ n

/-- If every one of x₀ … xₙ₋₁ occurs, the two ways of counting agree. -/
def StCountAllOccur : Prop := ∀ (n : ℕ) (Φ : Fml), Below n Φ → (∀ i < n, ∃ C ∈ Φ, ∃ l ∈ C, l.1 = i) → cntN n Φ = Eight.numSat Φ

/-- The two vocabularies of this development say the same: for a formula with variables in `Fin N`,
read with numbers as variables (`Decode.toN`), v and Z are `MainTheoremForms.numOcc` and
`MainTheoremForms.numSatOcc` of MainTheoremFormsStatement.lean. -/
def StSameAsFin : Prop := ∀ (N : ℕ) (φ : Sat3.CNF N), numOcc (Decode.toN φ) = MainTheoremForms.numOcc φ ∧ Eight.numSat (Decode.toN φ) = MainTheoremForms.numSatOcc φ

/-- The last step of a program that has computed Z for the formula Φ on n variables: from ((n in
unary, Φ), Z) the number Z·2^{n−v}. -/
def timesFree (q : (List Unit × Fml) × ℤ) : ℕ := q.2.toNat * 2 ^ (q.1.1.length - numOcc q.1.2)

/-- That step is polynomial-time. -/
def StTimesFreeCert : Prop := PolyT timesFree

/-- v in unary is computed in polynomial time. -/
def StNumOccCert : Prop := PolyT fun Φ : Fml => List.replicate (numOcc Φ) ()

end Occ
