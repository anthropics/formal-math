/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Tied.Defs
public import GeneralPieces.DefGenPieces.Progs

/-! # Part (c), first sentence, of the theorem on the general recursion, and the bound in m, for named programs, from pieces as the appendix defines them: definitions and statements only

`AppRunningTime.ThmRunningTime` and `AppRunningTime.BoundInM` say "there is a program" and "there is
a machine". The statements of this file name the programs. `ThmRunningTimeCm` is part (c), first
sentence, for the recursion on the
schedule of display (40), for EVERY x₀ of the theorem; `BoundInM` is the bound in m for the top
level in m (`AM`, `eM`) on that recursion, with the least x₀ of the theorem, on programs for the
pieces of Appendix B.
What they pin down. `BoundInM` names the algorithm (`solveG` on the schedule of display (40), `AM`),
not the argument of case (ii) of the lemma on groupings with explicit cost: it leaves the constant c
free.
The argument of case (ii) is what `GeneralPieces.StCaseII` and
`GeneralPieces.StSolveG2` (whose `ChainG2` has no counting condition) are about. `ThmRunningTimeCm`
speaks of every x₀ ≥ 18 with 2^x₀ ≥ c + 5.
Nothing is proved in this file; the two operations on programs that it names, `GeneralPieces.trimV`
("we may and do assume c^row, c^col ≤ 2λ") and `GeneralPieces.atZero` (the form that the recursion
reads), are defined in the imported file
`proof/rates/GeneralPieces/DefGenPieces/Progs.lean`, which holds definitions only. -/

@[expose] public section

namespace GeneralPieces.Tied

open Groundwork PaddedDescent.F ClauseBound.Alg AppRunningTime

/-- (P, A, val) are the pieces of the proof of the theorem on pieces with ρ = 1/√2, with the
constant c: the body of `AppRunningTime.ThmHalfPieces`, word for word. -/
def IsPiecesB (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ) : Prop := IsPieces (1 / Real.sqrt 2) c P A val ∧
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    P.cnt 0 lam = 4 * AppHalfPieces.hOf lam + 1 ∧ P.d 0 lam = (AppHalfPieces.hOf lam).factorial ∧
    ∀ i < P.cnt 0 lam, (∀ x y u v, (A lam i x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu ((i : ℤ) - 2 * AppHalfPieces.hOf lam) x y u v) ∧
      P.cap false 0 lam i = Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) ((i : ℤ) - 2 * AppHalfPieces.hOf lam)) ∧
      P.cap true 0 lam i = Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) ((i : ℤ) - 2 * AppHalfPieces.hOf lam))

/-- The programs that the recursion runs on, for pieces (P, val) with the constant c. -/
def recOf (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) : PiecesF := atZero (trimV P val c) c 1

/-- Part (c), first sentence, for the named programs: for all pieces with parameters (ρ, c) and
every x₀ ≥ 18 with 2^x₀ ≥ c + 5, `PartCm` holds of the top level in m on the recursion on these
pieces. -/
def ThmRunningTimeCm : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ), IsPieces ρ c P A val →
  18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → PartCm (recOf P val c) ρ x₀

/-- The bound in m for the named programs: for some programs (P, val) for the pieces of Appendix B,
with a constant c, the top level in m on the recursion for `recOf P val c` with x₀ = `x₀Of c` is
polynomial-time, counts
the satisfying assignments once the pad has 2^eM units, has eM = O(km/√(log m)), and one machine
computes it on every input and so counts within C·2^{C·km/√(log₂(m+2))} steps. -/
def BoundInM : Prop := ∃ (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ), IsPiecesB c P A val ∧
  PartCm (recOf P val c) (1 / Real.sqrt 2) (x₀Of c)

end GeneralPieces.Tied
