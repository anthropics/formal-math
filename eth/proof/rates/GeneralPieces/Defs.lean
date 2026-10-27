/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Appendix A, with case (ii) of Lemma 8: definitions and interface statements

Here the programs of the recursion are analysed as in the paper: groups of exactly g/K nodes,
Hoeffding's inequality for sampling without replacement, and every x₀ ≥ 18 with 2^x₀ ≥ c + 5.
Nothing is proved and nothing is assumed in this file:
`St… : Prop` are statements; one file proves each, and a file that needs one takes it as a
hypothesis. -/

@[expose] public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen

/-- The existence claim in the proof of Lemma 8, case (ii): if K divides g, every node shares at
most P bits in all and at most P/g bits with any other node,
and 2ζ²g ≥ K·ln(2gK), then some grouping has exactly g/K nodes in every group and, for any two
different groups, the sum Y of c_ab over a in one and b in the other is < (U + 2ζgP)/K². Here U =
Σ_a Σ_{b ≠ a} c_ab. -/
def StCaseII : Prop := ∀ (K g : ℕ) (c : Fin g → Fin g → ℕ) (P ζ : ℝ), 2 ≤ K → 2 ≤ g → K ∣ g → 0 < ζ → ζ ≤ 1 → 0 < P →
  (∀ a, ∑ b ∈ univ.erase a, (c a b : ℝ) ≤ P) → (∀ a b, a ≠ b → (c a b : ℝ) ≤ P / g) →
  (K : ℝ) * Real.log (2 * g * K) ≤ 2 * ζ ^ 2 * g →
  ∃ χ : Fin g → Fin K, (∀ γ, #{a | χ a = γ} = g / K) ∧
    ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) <
      ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2

/-- ζ of a step, 3/(2D). With it, the error term 3p²M/(D·K²) of the label length one level down
(`lamNextG`; M = d²·m·λ, so that p·M is the paper's P) is 2ζ·p·(pM)/K², the paper's 2ζgP/K². -/
noncomputable def zetaOf (s : Step) : ℝ := 3 / (2 * (s.D : ℝ))

/-- What the proof needs of one step at the label length lam: the pieces are pieces there, K ≥ 2
divides p, the condition of case (ii) of Lemma 8 holds with ζ = `zetaOf s`,
the grid is square, and the total of every pattern is at most the program's bound: `ubarG`, or
2·`ebarG` for a pattern with `s.thin && colSide` true. -/
structure LevelOK2 (P : PiecesF) (s : Step) (lam : ℕ) : Prop where
  spec : P.Spec s.h lam
  two_le : 2 ≤ s.K
  two_le_p : 2 ≤ s.p
  D_ge : 2 ≤ s.D
  dvd : s.K ∣ s.p
  hoeffding : (s.K : ℝ) * Real.log (2 * s.p * s.K) ≤ 2 * zetaOf s ^ 2 * s.p
  square : s.thin = false → s.p = s.d
  a_pos : s.thin = true → 1 ≤ s.a
  ubar : ∀ y < nPat P s lam, (s.thin && colSide P s lam y) = false →
    totalG P s.p s.d (!s.thin && colSide P s lam y) s.h lam y ≤ ubarG P s lam
  ebar : ∀ y < nPat P s lam, (s.thin && colSide P s lam y) = true → totalG P s.p s.d true s.h lam y ≤ 2 * ebarG s lam

/-- One level: if the step is in order (`LevelOK2`) and the pad is long enough, d^{|R|} times the
value of the instance is an integer plus the sum of the values of the instances one level down;
these are well
formed with label length `lamNextG` and bound `bNextG`, there are at most `nPat` of them, and the
integer is bounded. -/
def StExpandG2 (P : PiecesF) : Prop := ∀ (pad : U) (s : Step) (lam B : ℕ) (I : PInst), LevelOK2 P s lam → WFe (s.p * s.d) lam B I → BudG P pad.length s lam →
  (P.d s.h lam : ℤ) ^ nRectG s.p s.d * zval (s.p * s.d) I = (expandG P pad s I).1 + ((expandG P pad s I).2.map (zval s.K)).sum ∧
  (∀ J ∈ (expandG P pad s I).2, WFe s.K (lamNextG P s lam) (bNextG P s lam B) J) ∧
  (expandG P pad s I).2.length ≤ nPat P s lam ∧
  (expandG P pad s I).1.natAbs ≤ 2 ^ (Nat.size (nPat P s lam) + Nof s lam + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam + 1))

/-- The schedule is a chain of steps p·d → K that ends at K₀ nodes, and every step is in order
(`LevelOK2`) at its label length. -/
def ChainG2 (P : PiecesF) (K₀ : ℕ) : ℕ → ℕ → List Step → Prop
  | Kup, _, [] => Kup = K₀
  | Kup, lam, s :: r => Kup = s.p * s.d ∧ LevelOK2 P s lam ∧ ChainG2 P K₀ s.K (lamNextG P s lam) r

/-- All levels: if every step of the schedule is in order and the pad is long enough, `solveG`
returns the value of the instance. -/
def StSolveG2 (P : PiecesF) : Prop := ∀ (pad : U) (K₀ : ℕ) (sched : List Step) (Kup lam B : ℕ) (I : PInst),
  ChainG2 P K₀ Kup lam sched → FitsG P pad.length Kup lam B 1 1 sched → WFe Kup lam B I → solveG P pad K₀ sched I = zval Kup I

/-- Every step of the schedule is in order at every label length, for pieces whose numbers of bits
are at most 2λ and every x₀ of Theorem A. -/
def StChain2 : Prop := ∀ (P : PiecesF) (ρ : ℝ) (c x₀ : ℕ), Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
  ∀ l lam, 1 ≤ lam → ChainG2 P (K x₀ 0) (K x₀ l) lam (sched P x₀ l)

/-- Part (b) of Theorem A as an inequality for the exponent of the pad, for every x₀ ≥ 18 with 2^x₀
≥ c + 5; C₀ depends on c only. -/
def StRate2 : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
  ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
    (needG P (K x₀ l) lam B 1 1 (sched P x₀ l) : ℝ) ≤
      e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + C₀ * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))

/-- Parts (a) and (b) in the form that the top levels use, for every x₀ of Theorem A. (Here C₀ may
depend on P, ρ and x₀; `StRate2` gives one that depends on c only.) -/
def StSeq2 : Prop := ∀ (P : PiecesF) (ρ : ℝ) (c x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
  ∃ C₀ : ℕ, ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, ∀ l, Q.idx l = idx P x₀ l

end GeneralPieces
