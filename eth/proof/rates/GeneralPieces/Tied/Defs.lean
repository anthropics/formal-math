/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.Defs
public import ClauseBound.Gen.Pick
public import ClauseBound.Alg.Top
public import PaddedDescent.Pad

/-! # Parts (b) and (c) of Theorem A, for named programs: definitions and statements only

`AppRunningTime.PartB` and `SatM.CountInRate` say "there is a program" and "there is a machine";
they do not name the recursion, so by their wording they say nothing about the route of a proof. The
statements of this file name
the programs: the recursion `solveG` on the schedule of display (40) with the x₀ of the theorem,
every step of which meets the hypotheses of case (ii) of Lemma 8, and the top
level `AM` with its exponent `eM`, run on that recursion. These statements name the programs and
their parameters; a statement cannot name a proof. That the proof given in this folder goes through
case (ii) of
Lemma 8 is seen in the proofs (`GeneralPieces.Level.child_spec2` calls
`GeneralPieces.Level.cases_ii` and `GeneralPieces.grouping_general`).
The program `runB` and the exponent `needB` are functions of the programs of the pieces and of x₀
only:
«The algorithm uses … neither ρ nor e_ℓ.» Nothing is proved here. -/

@[expose] public section

namespace GeneralPieces

/-- The least integer x₀ ≥ 18 with 2^x₀ ≥ c + 5. -/
def x₀Of (c : ℕ) : ℕ := max 18 (Nat.clog 2 (c + 5))

end GeneralPieces

namespace GeneralPieces.Tied

open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen Turing

/-- The program of part (b), a function of (pad, ℓ in unary, instance): with K the number of rows of
the instance, `ClauseBound.Gen.Pick.pick` builds the schedule of the largest level with at most K
nodes, and `solveG` descends
along it. The ℓ of the input is not read. -/
def runB (P : PiecesF) (x₀ : ℕ) (p : U × U × PInst) : ℤ :=
  solveG P p.1 (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.2.length (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.1 p.2.2

/-- The logarithm of the number of units that the pad must have at level ℓ. -/
def needB (P : PiecesF) (x₀ l lam B : ℕ) : ℕ := needG P (K x₀ l) lam B 1 1 (sched P x₀ l)

/-- Part (b) for the named program. -/
structure PartB (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) : Prop where
  /-- the program is polynomial-time in (pad, ℓ, instance) -/
  poly : PolyT (runB P x₀)
  /-- on a (K_ℓ, λ)-clique it is the recursion on the schedule of display (40), from K_ℓ nodes down
  to K₀ nodes (`sched P x₀ ℓ` is, by definition, the list step ℓ−1, …, step 0) -/
  sched_eq : ∀ (pad lu : U) (l lam B : ℕ) (I : PInst), WFe (K x₀ l) lam B I → runB P x₀ (pad, lu, I) = solveG P pad (K x₀ 0) (sched P x₀ l) I
  /-- the step from K_{ℓ+1} = g_ℓ² nodes to K_ℓ nodes has the numbers of display (40) -/
  step_eq : ∀ l, (step P x₀ l).K = K x₀ l ∧ (step P x₀ l).p = g x₀ l ∧ (step P x₀ l).d = g x₀ l ∧ zetaOf (step P x₀ l) = zeta l
  /-- and meets the hypotheses of case (ii) of Lemma 8 (fields `dvd` and `hoeffding` of `LevelOK2`)
  at every label length -/
  caseII : ∀ l lam, 1 ≤ lam → LevelOK2 P (step P x₀ l) lam
  /-- the program returns the value of the clique if the pad has 2^needB units -/
  value : ∀ (pad : U) (l lam B : ℕ) (I : PInst), 1 ≤ lam → 1 ≤ B → WFe (K x₀ l) lam B I → 2 ^ needB P x₀ l lam B ≤ pad.length →
    runB P x₀ (pad, List.replicate l (), I) = zval (K x₀ l) I
  /-- 2^needB ≤ 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ + B))^{C₀K_ℓ²} -/
  rate : ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
    (needB P x₀ l lam B : ℝ) ≤ e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + C₀ * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))

/-- The bound in m for the named top level: the function `AM S pick` of (input, pad) and the
exponent `eM S pick` of the input, for an algorithm S for cliques and a way to pick its level. -/
structure TopM {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (r : ℕ → ℝ) : Prop where
  /-- both are polynomial-time -/
  poly_A : PolyT (AM S pick)
  poly_e : PolyT (eM S pick)
  /-- the function returns the number of satisfying assignments, in n + 1 bits, if the pad has 2^eM
  units -/
  correct : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ → ∀ pad : U, 2 ^ eM S pick (SatM.enc k φ) ≤ pad.length →
    AM S pick (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
  /-- the exponent is O(k·m·r(m)), the O not depending on k -/
  rate : ∃ G : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
    (eM S pick (SatM.enc k φ) : ℝ) ≤ G * ((k : ℝ) * φ.length * r φ.length)
  /-- one machine computes, on every input x, the named function at (x, 2^{eM x} units) within
  q·(|x| + 2^{eM x} + 1)^q steps, and it counts within C·2^{C·k·m·r(m)} steps -/
  machine : ∃ (N : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
      (some ((AM S pick (x, pad (eM S pick x))).map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ eM S pick x + 1) ^ q))) ∧
    SatM.CountsTM N (SatM.bound r C)

/-- Part (c), first sentence, for the named programs: the top level in m, run on the recursion of
part (b) for the pieces P with the schedule of display (40) for x₀. -/
def PartCm (P : PiecesF) (ρ : ℝ) (x₀ : ℕ) : Prop := TopM (solverOf P) (Pick.pick P x₀) (SatM.rPow (AppRunningTime.alpha' ρ))

end GeneralPieces.Tied
