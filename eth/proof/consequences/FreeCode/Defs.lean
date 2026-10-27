/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatFreeCodeStatement
public import SplitSat.Defs
public import PaddedDescent.BrutePad

/-! # Definition 6 and Corollary 5 with the code that does not depend on k: which machines stand behind the sentences (definitions and statements only)

`KSatFreeCodeStatement.lean` has the paper's sentences; a sentence «there is a machine …» reads the
same whichever way it was proved. Here each is tied to a named machine cut into steps:
* a reader `dec` of the code (`Reads dec`: the code of φ on n variables is read as (n in unary, φ
  with numbers as variables)); `StReader`: there is a polynomial-time one. `Reads` fixes the reader
  on every code, so nothing depends on which one is taken;
* «Trying all assignments»: `bruteCore` behind the reader (`StBrute`);
* «Theorem 2 gives s_3 = 0»: `SplitSat.core3 ℓ τ`, the machine of Theorem 2 in its decision form
  without its own reader, behind the reader (`StTiedThree`);
* «s_3 = 0 implies s_k = 0 …; the reduction (sparsify, then split every long clause …)»:
  `SplitSat.reduceCore` on `core3`, behind the reader (`StTied`).
This file has no theorem. -/

@[expose] public section

namespace FreeCode

open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat

/-- `dec` reads the code: the code of φ on n variables as (n in unary, φ with numbers as variables).
Nothing is asked on other words. -/
def Reads (dec : List Bool → List Unit × Fml) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), dec (SatFree.enc φ) = (List.replicate n (), Decode.toN φ)

/-- There is a polynomial-time reader. -/
def StReader : Prop := ∃ dec : List Bool → List Unit × Fml, PolyT dec ∧ Reads dec

/-- The length of the code of a k-CNF on n variables is polynomial in n, for fixed k. -/
def StLength : Prop := ∀ k : ℕ, ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ → (SatFree.enc φ).length + 1 ≤ a * (n + 2) ^ d

/-- The machine Ms, cut into steps, decides w-SAT on the code that does not depend on k, with the
exponent δ and the constant c: on the code of a w-CNF φ on n variables it ends within c·2^{δn}
steps, on states of size at most c·(n+2)^c, with the bit «φ is satisfiable». -/
def DecidesFree (Ms : StepMachine (List Bool) Bool) (w : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF w φ →
  ∃ (T : ℕ) (b : Bool), Ms.Runs (SatFree.enc φ) T (c * (n + 2) ^ c) b ∧ (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- **For EVERY reader and EVERY procedure D** that decides w-SAT on (N in unary, formula) with the
exponent δ (`SplitSat.DecidesW`): D behind the reader decides w-SAT on the code, within the same
number of steps. -/
def StBehindReader : Prop := ∀ (dec : List Bool → List Unit × Fml), Reads dec → ∀ (w : ℕ) (D : StepMachine (List Unit × Fml) Bool) (δ : ℝ) (c : ℕ), DecidesW w D δ c → DecidesFree (Stepped.mapIn dec D) w δ c

/-- Exhaustive search on (n in unary, formula): for each number y < 2^n test in one step whether the
assignment that gives xᵢ the i-th binary digit of y satisfies the formula; add up; answer
«satisfiable» if the sum is positive. -/
def bruteCore : StepMachine (List Unit × Fml) Bool :=
  Stepped.mapOut (Stepped.sumRange (fun p : List Unit × Fml => 2 ^ p.1.length) (Stepped.ofFun fun q : (List Unit × Fml) × ℕ => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ))) fun v => decide (0 < v)

/-- **«Trying all assignments».** There are a polynomial-time reader and ONE Turing machine with
finite alphabets such that (1) `bruteCore` behind the reader ITSELF has polynomial-time steps and
decides k-SAT, for every k, within c·2^n steps, on states of size at most c·(n+2)^c, with c
depending on k; (2) the Turing machine simulates it with polynomial overhead; (3) the Turing machine
decides k-SAT, for every k, within c·(n+2)^c·2^n steps, with c depending on k. -/
def StBrute : Prop := ∃ (dec : List Bool → List Unit × Fml) (M : Turing.TM2ComputableAux Bool Bool) (q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec bruteCore) ∧
  (∀ k : ℕ, ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ (T : ℕ) (b : Bool), (Stepped.mapIn dec bruteCore).Runs (SatFree.enc φ) T (c * (n + 2) ^ c) b ∧ (b = true ↔ Sat3.Satisfiable φ) ∧ T ≤ c * 2 ^ n) ∧
  Simulates M (Stepped.mapIn dec bruteCore) q ∧ ∀ k : ℕ, ∃ c : ℕ, SatFree.DecidesTM k M fun n => c * (n + 2) ^ c * 2 ^ n

/-- **«Theorem 2 gives s_3 = 0».** For every δ > 0 there are a polynomial-time reader, ℓ, τ such
that (1) the machine of Theorem 2 in its decision form (`core3 ℓ τ`) behind the reader ITSELF has
polynomial-time steps and decides 3-SAT with the exponent δ; (2) a Turing machine with finite
alphabets simulates it with polynomial overhead; (3) that Turing machine decides 3-SAT within
⌊c·2^{δn}⌋ steps. -/
def StTiedThree : Prop := ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (core3 ℓ τ)) ∧ DecidesFree (Stepped.mapIn dec (core3 ℓ τ)) 3 δ c ∧
  Simulates M (Stepped.mapIn dec (core3 ℓ τ)) q ∧ SatFree.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

/-- **Corollary 5, tied to the reduction.** For every k ≥ 3 and δ > 0 there are a polynomial-time
reader, τ, ℓ₃, τ₃ such that (1) the reduction (sparsify at width k with the parameter τ, split every
long clause, ask the machine of Theorem 2 in its decision form) behind the reader ITSELF has
polynomial-time steps and decides k-SAT with the exponent δ; (2) a Turing machine with finite
alphabets simulates it with polynomial overhead;
(3) that Turing machine decides k-SAT within ⌊c·2^{δn}⌋ steps. (Without (1), a machine that runs the
    reduction and another machine for k-SAT side by side would meet (2) and (3), and only the
    correctness of the reduction would be needed, not its running time.) -/
def StTied : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) ∧ DecidesFree (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) k δ c ∧
  Simulates M (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) q ∧ SatFree.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

end FreeCode
