/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
public import ThreeSumApsp.Programs.Sec2.Theorem5.Solver
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.BandCounters
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Binomials
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Coefficients
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Digits
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Subsets
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Codes
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Gather
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Sort

/-!
# Theorem 5: the program

The list of the procedures of Theorem 5's program, in the order of their numbers.  An entry is the
specification of a procedure together with a bound on its time, a constant times a shape.  In every
program that begins with this list, the procedures that the shared stage calls meet their entries
with the constant cShared5 (sharedCallees_of_prefix), and those that the solver calls with the
constant cMain5 (mainCallees_of_prefix).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The program of Theorem 5.  The numbers of the procedures begin with 1; number 0 is empty. -/
def program5 : Program :=
  [.skip, sharedBody, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
   digitsBody, coefBody, bandArrayBody, encStepBody, encodeBody pEncStep pEncode, encodeBandsBody,
   Wanted.wantedBody, countSortBody, sortWantedBody, segBoundsBody, unionBody, pickBody, prunedBody,
   runTilesBody, reportBody, fillBody, copyBody, gatherBody, thm5Body]

/-- The program has 26 procedures. -/
theorem length_program5 : program5.length = 26 := rfl

/-- A procedure of program5 is a procedure, with the same number, of every program that begins with
program5. -/
theorem at_prefix {p : ℕ} {body : Stmt} (h : program5[p]? = some body) (R : Program) :
    (program5 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-! ## All entries -/

/-- The constant of the procedures that the shared stage calls. -/
def cShared5 : ℕ := 2000

/-- The constant of the procedures that the solver calls. -/
def cMain5 : ℕ := 12 * cShared5 + 600 + 5560

/-- The procedures that the shared stage calls meet their entries. -/
theorem sharedCallees_of_prefix (R : Program) (lim : Limits) (std : Std lim) :
    SharedCallees lim (program5 ++ R) cShared5 where
  pow := pow_entry std (at_prefix rfl R) (by decide)
  binom := binom_entry std (at_prefix rfl R) (by decide)
  sqrt := sqrt_entry (at_prefix rfl R) (by decide)
  coef := coef_entry std (at_prefix rfl R) (by decide)
  subsets := subsets_entry std (at_prefix rfl R) (by decide)
  counters := counters_entry std (at_prefix rfl R) (by decide)
  digits := digits_entry std (at_prefix rfl R) (by decide)
  bandsL := encodeBandsL_entry std (at_prefix rfl R) (bandArrayL_entry std (at_prefix rfl R))
    (encodeL_entry std (at_prefix rfl R) (at_prefix rfl R)) (by decide)
  bandsR := encodeBandsR_entry std (at_prefix rfl R) (bandArrayR_entry std (at_prefix rfl R))
    (encodeR_entry std (at_prefix rfl R) (at_prefix rfl R)) (by decide)

/-- **The procedures that the solver calls meet their entries**, in every program that begins with
program5. -/
theorem mainCallees_of_prefix (R : Program) (lim : Limits) (std : Std lim) :
    MainCallees lim (program5 ++ R) cMain5 where
  shared := shared_entry std (at_prefix rfl R) (sharedCallees_of_prefix R lim std) (by decide)
  wanted := wanted_entry std (at_prefix rfl R) (by decide)
  sort := sortWanted_entry std (at_prefix rfl R) (at_prefix rfl R) (at_prefix rfl R) (by decide)
  gather := gather_entry std (at_prefix rfl R) (by decide)
  tiles := runTiles_entry std (at_prefix rfl R)
    (pruned_entry std (at_prefix rfl R) (at_prefix rfl R) (at_prefix rfl R) (at_prefix rfl R)
      (at_prefix rfl R)) (by decide)
  report := report_entry std (at_prefix rfl R) (by decide)

end Light.Sec2
