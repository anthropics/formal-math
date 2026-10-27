/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import OccurM.TiedDefs
import OccurM.Arith
import OccurM.Top
import GeneralPieces.Main
import GeneralPieces.Tied.Bound
import GeneralPieces.Num.PartD
import GeneralPieces.Num.Asymptotic

/-! # Theorem A (c), first sentence, and the bound in m of the Main Theorem, for formulas over arbitrary names

The route, as in the paper:

1. `countsFromPiecesTied`: part (c), first sentence, for the named programs (given programs for the
   pieces, from which the machine is built). `GeneralPieces.thmRunningTimeCm_tied` gives it on
   formulas in which every variable occurs (the network of the formula, case (i) of Lemma 8, the
   algorithm of
   part (b)), and `topOccurOfTop` puts the preparation in front. 0 ≤ α' ≤ 1 because ½ ≤ ρ < 1.
2. `untie`: from the named programs to «there is a machine», with the least x₀ of Theorem A.
3. `ClausesOccur.countsFromPieces`: Theorem A (c), first sentence, by 1 and 2.
4. `ClausesOccur.boundInClausesFrom`, `boundInClauses`: «With Theorem A this gives the exponent
   log(1/ρ) = ½ of log m, that is, the bound in m of the Main Theorem», from Theorem B and 3.
5. `boundInClausesTied`: the same for the named programs. `ClausesOccur.runningTimesFromPieces`:
   Theorem A as a whole, the other parts from `AppRunningTime.thmRunningTime`. -/

public section

namespace ClausesOccur

open Turing MainTheoremForms

/-- For every machine and every constant, the bound in m of the Main Theorem is `CountsFor` at α =
½. -/
theorem boundInClausesIsHalf : BoundInClausesIsHalfStmt := by
  intro M C
  have e : ∀ k m : ℕ, expClauses (1 / 2) k m = expM k m := expHalf
  unfold BoundInClausesFor CountsFor timeClauses
  simp only [e]

end ClausesOccur

namespace OccurM

open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur

/-- Theorem A (c), first sentence, for the named programs: the preparation, then the top level in m
on the recursion of part (b). -/
theorem countsFromPiecesTied : CountsFromPiecesTied := fun ρ c x₀ P A val h hx hc =>
  topOccurOfTop _ _ _ _ (GeneralPieces.PartD.alpha_mem ρ h.rho_ge h.rho_lt).1 (GeneralPieces.PartD.alpha_mem ρ h.rho_ge h.rho_lt).2 (GeneralPieces.thmRunningTimeCm_tied ρ c x₀ P A val h hx hc)

/-- The bound in m of the Main Theorem for the named programs, on programs for the pieces of
Appendix B; α' = log √2 = ½. -/
theorem boundInClausesTied : BoundInClausesTied := by
  obtain ⟨c, P, A, val, hB, hC⟩ := GeneralPieces.boundInM_tied AppRunningTime.thmHalfPieces
  unfold GeneralPieces.Tied.PartCm AppRunningTime.alpha' at hC
  rw [GeneralPieces.Asymptotic.alpha_half] at hC
  obtain ⟨t1, t2⟩ := topOccurOfTop _ _ _ _ (by norm_num) (by norm_num) hC
  exact ⟨c, P, A, val, hB, t1, t2⟩

/-- From the forms for the named programs (the tied forms: the machine is built from given programs
for the pieces) to the forms with «there is a machine»: the machine and the constant are those of
the field `machine`; x₀ is the least one of Theorem A. -/
theorem untie : UntieStmt := by
  refine ⟨fun h => ⟨fun ρ c hE => ?_, fun ρ c hE => ?_⟩, fun h => ?_⟩
  · obtain ⟨P, A, val, hP⟩ := hE
    obtain ⟨M, -, C, hfin, -, hM⟩ := (h ρ c (GeneralPieces.x₀Of c) P A val hP (GeneralPieces.x₀Of_ge c) (GeneralPieces.x₀Of_pow c)).1.machine
    exact ⟨M, C, hfin, hM⟩
  · obtain ⟨P, A, val, hP⟩ := hE
    obtain ⟨M, -, C, hfin, -, hM⟩ := (h ρ c (GeneralPieces.x₀Of c) P A val hP (GeneralPieces.x₀Of_ge c) (GeneralPieces.x₀Of_pow c)).2.machine
    exact ⟨M, C, hfin, hM⟩
  · obtain ⟨c, P, A, val, -, t, -⟩ := h
    obtain ⟨M, -, C, hfin, -, hM⟩ := t.machine
    exact ⟨M, C, hfin, (boundInClausesIsHalf M C).2 hM⟩

end OccurM

namespace ClausesOccur

open Turing MainTheoremForms

/-- Theorem A (c), first sentence. -/
theorem countsFromPieces : CountsFromPieces := (OccurM.untie.1 OccurM.countsFromPiecesTied).1

/-- The same with N in unary in the input. -/
theorem countsUnaryFromPieces : CountsUnaryFromPieces := (OccurM.untie.1 OccurM.countsFromPiecesTied).2

/-- «With Theorem A this gives …»: from Theorem B and the first sentence of Theorem A (c) to the
bound in m; α' = log √2 = ½. -/
theorem boundInClausesFrom : BoundInClausesFromStmt := by
  intro hB hC
  obtain ⟨c, P, A, val, h, -⟩ := hB
  obtain ⟨M, C, hfin, hM⟩ := hC _ c ⟨P, A, val, h⟩
  unfold AppRunningTime.alpha' at hM
  rw [GeneralPieces.Asymptotic.alpha_half] at hM
  exact ⟨M, C, hfin, (boundInClausesIsHalf M C).2 hM⟩

/-- After Theorem B: the bound in m of the Main Theorem. -/
theorem boundInClauses : BoundInClauses := boundInClausesFrom AppRunningTime.thmHalfPieces countsFromPieces

/-- Theorem A, with the first sentence of (c) as printed. -/
theorem runningTimesFromPieces : RunningTimesFromPieces :=
  ⟨AppRunningTime.thmRunningTime.a, AppRunningTime.thmRunningTime.b, countsFromPieces, AppRunningTime.thmRunningTime.c_n, AppRunningTime.thmRunningTime.d⟩

end ClausesOccur
