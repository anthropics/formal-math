/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInKStatement
public import RecursionWithPieces.Defs
public import UniformInK.Top.Defs
import RecursionWithPieces.Master
import GeneralPieces.Main
import GeneralPieces.Tied.Bound
import GeneralPieces.Top.CaseI
import GeneralPieces.Num.TopDisplay
import GeneralPieces.Num.PartAUse
import GeneralPieces.ThmRunningTime
import ClauseBound.Alg.Need
import SparsifyThenCount.Main
import SparsifyThenCount.PlanUsed
import SparsifyThenCount.Correct
import SparsifyThenCount.CorrectB
import SparsifyThenCount.Tied
import VariableBound.MainPrinted
import VariableBound.Printed.Tied
import VariableBound.Paper.Decide
import VariableBound.StepParity
import VariableBound.Family.Main
import VariableBound.Field.Family
import VariableBound.Params.Spec
import VariableBound.Params.Ineq
import VariableBound.Search.Correct
import VariableBound.Net.Main
import VariableBound.Net.Ev
import VariableBound.Count.Correct
import VariableBound.Top.Budget
import VariableBound.Top.ArithPlan
import StepSparsify.WalkCount
import StepSparsify.CalServes
import UniformInK.Top.Correct
import UniformInK.Top.CorrectB
import UniformInK.Top.Leaves
import ClauseBound.MainBoth
import ClauseBound.Both.TimeM
import ClauseBound.Alg.TopVal
import ClauseBound.Alg.Decode
import CountKSatRate.Pad
import CountKSatRate.Brute

/-! # The end theorems for the function for Theorem 1 on the recursion of Appendix A with the pieces of Appendix B

**What is proved.**
* `RecursionWithPieces.tiedAt_of`, and in the form of a statement of
  proof/variables/RecursionWithPieces/Defs.lean
  `RecursionWithPieces.tiedEvery : StepSparsify.Serves Θ Lc → TiedEvery Θ`: for thresholds Θ that
  serve and for all (c, P₀, A, val) that are the pieces of Appendix B
  (`GeneralPieces.Tied.IsPiecesB`), the seven statements of
  `TiedAt Θ c P₀ A val`.
* `RecursionWithPieces.tiedAll : StepSparsify.Serves Θ Lc → TiedAll Θ`: with the theorem on pieces
  with ρ = 1/√2 (`AppRunningTime.thmHalfPieces`), which says that such c, P₀, A, val exist.
* `RecursionWithPieces.tiedAllCal : TiedAllCal`: this for `StepSparsify.thCal`, the thresholds θ_0 =
  2, θ_c = α·β_c, which we take to be Calabro's (the paper does not print them, and they were not
  checked against Calabro's dissertation), with α = ⌈2(k−1)²ε⁻¹⌈log₂(32(k−1)²/ε)⌉⌉, for max(k, 3) in
  place of k and ε = 2^(−s);
  these thresholds serve by `StepSparsify.servesCal`.
* A corollary of `tiedAllCal` that names no function: `SatM.targetUniform_all`. By its statement it
  shows nothing about the route; `tiedAllCal` does.

**How the pieces are put together.**
* Appendix B: `AppRunningTime.thmHalfPieces` gives the pieces. Appendix A:
  `GeneralPieces.par_of_isPieces` («we may and do assume»), `GeneralPieces.seq_of_pick` (the
  recursion on the schedule of display (40) is a solver with a sequence of levels; every step by
  case (ii) of the
  lemma on groupings with explicit cost), `GeneralPieces.thmRunningTime_b_tied`,
  `GeneralPieces.thmRunningTime_c_m_tied` (parts (b) and (c), first sentence).
* Three statements are proved in proof/rates/GeneralPieces. Each is a hypothesis of the step that
  uses it, and each is about the top levels, where a network on 3K⁸ nodes is rebalanced to K nodes
  and handed to the solver for cliques. The
  paper does this by case (i) of the lemma on groupings with explicit cost; and so do the proofs
  used here (proof/rates/GeneralPieces/Top/CaseI.lean).
  1. `ClauseBound.Alg.StValS` (the solver returns the value of any network; Step 4 of Appendix D;
     hypothesis of `VariableBound.Net.Ev.stEvD`): here `GeneralPieces.Top.stValS2`.
  2. `ClauseBound.Alg.StCountG` (the same for the network of a k-CNF, in the algorithm for the bound
     in m; hypothesis of `ClauseBound.Alg.TopVal.stCorrectM`): here `GeneralPieces.Top.stCountG2`.
  3. `ClauseBound.Alg.StTopArith` (the exponent of the algorithm for the bound in m; hypothesis of
     `ClauseBound.Both.TimeM.stTimeM`): here `GeneralPieces.TopDisplay.stTopArith2`, through the
     display in the proof of Theorem A(c) (the bound on the logarithm of the number of operations).
  So the theorems from these three up to the merged function (`evAB`, `evXFAB`, `countAB`,
  `correctDGAB`, `correctBDGAB`, `algAB`) are proved here.
* Steps 1 to 3 (Lemmas 12 and 13, the search, the networks), the walk with the thresholds Θ, the
  certificates of polynomial time, the merge of the exponents and the arithmetic of Steps 4 to 6 are
  those of proof/variables/VariableBound, proof/sparsification/StepSparsify and
  proof/variables/SparsifyThenCount.
* Step 6 for this solver: `master_of_isPiecesB` (proof/variables/RecursionWithPieces/Master.lean).
  The padding machine: `VariableBound.tied_of_alg`. The plan is used:
  `SparsifyThenCount.stPlanUsed`, `SparsifyThenCount.stRateZero`.

**What it does not say.** What the module comment of proof/variables/RecursionWithPieces/Defs.lean
lists. -/

public section

namespace RecursionWithPieces

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks ClauseBound.TopN UniformInK VariableBound VariableBound.Decide SparsifyThenCount GeneralPieces

/-! ### Step 4 through case (i) of the lemma on groupings with explicit cost, and what rests on it -/

/-- Steps 3 and 4: one evaluation is the right side of the display of Step 1 of Appendix D that
gives X(𝓛) and F(𝓛) modulo powers of 2, under the hypotheses of `VariableBound.Net.StEvD`. The value
of each network comes from the solver by case (i) of the lemma on groupings with explicit cost
(`GeneralPieces.Top.stValS2`). -/
theorem evAB : Net.StEvD := Net.Ev.stEvD Top.stValS2 Net.Main.presents Net.Main.total Net.Main.size

/-- The programs compute X(𝓛), and F(𝓛) if X(𝓛) = 0, under the hypotheses of
`VariableBound.Net.StEvXF`; from `evAB`. -/
theorem evXFAB : Net.StEvXF := Net.Ev.stEvXF evAB VariableBound.xf VariableBound.residues Net.Main.chks

/-- Steps 1 to 4: the count of one sparse formula is right (`VariableBound.StCountD`); from
`evXFAB`. -/
theorem countAB : StCountD :=
  stCountD evXFAB Net.Main.fit Net.Main.tbMax Net.Main.nPrMax stSearchD (Fld.stFamD lemFamily) stParamSpec paramIneq product emptyList

/-- For thresholds that serve and every polynomial-time solver with a sequence of levels, the
function `ADG Θ` for the bound in n is right on every k-CNF, for every k ≥ 1 and every n, when the
pad has length at least 2^(eD …);
from `countAB`. -/
theorem correctDGAB : StCorrectDG := stCorrectDG countAB (stBudgetD stLeavesU) stRoundsDG StepSparsify.stWalkCountG Decode.stDecM stBruteC stDecU

/-- For thresholds that serve and every polynomial-time solver with a sequence of levels, the merged
function `ABDG Θ` is right on every k-CNF, for every k ≥ 1 and every n, when the pad has length at
least 2^(eBD …); from
`correctDGAB`, with the network of the formula in the algorithm for the bound in m rebalanced by
case (i) (`GeneralPieces.Top.stCountG2`). -/
theorem correctBDGAB : StCorrectBDG :=
  stCorrectBDG correctDGAB (TopVal.stCorrectM Decode.stDecM (Top.stCountG2 TopVal.stSatPresentsK)) (stAllOccU Decode.stDecM) Decode.stDecM

/-- For thresholds Θ that serve (with the bound Lc) and every solver with a sequence of levels,
under the hypotheses of `VariableBound.StEndS`: the merged function `ABDG Θ` and the exponent
function `eBD` are an algorithm for the two rates; from
`correctBDGAB`, with the exponent of the algorithm for the bound in m bounded through the display in
the proof of Theorem A(c) (the bound on the logarithm of the number of operations)
(`GeneralPieces.TopDisplay.stTopArith2`). -/
theorem algAB (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (hΘ : StepSparsify.Serves Θ Lc) : StAlgSG Θ :=
  stAlgSG correctBDGAB certBDGc expBDc timeDGc (TimeM.stTimeM TopDisplay.stTopArith2) Θ Lc hΘ

/-! ### The end theorems -/

/-- For thresholds Θ that serve (with the bound Lc) and (c, P₀, A, val) that are the pieces of
Appendix B: the seven statements of `TiedAt`. -/
theorem tiedAt_of {Θ : ℕ → ℕ → ℕ → ℕ} {Lc : ℕ → ℕ → ℕ} (hΘ : StepSparsify.Serves Θ Lc) {c : ℕ} {P₀ : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ}
    (h : Tied.IsPiecesB c P₀ A val) : TiedAt Θ c P₀ A val := by
  have hA : Alg (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) (fnAll Θ P₀ val c) (expAll P₀ val c) := master_of_isPiecesB (algAB Θ Lc hΘ) h
  obtain ⟨C₀, hC⟩ := thmRunningTime_b_tied c
  exact ⟨h, ⟨C₀, hC _ _ P₀ A val h.1 (x₀Of_ge c) (x₀Of_pow c)⟩, thmRunningTime_c_m_tied h.1, hA, tied_of_alg stPaddedW hA PolyT.id' (rN_nonneg _) (rPow_nonneg _),
    tied_of_alg stPaddedW hA polyT_bitOf (rN_nonneg _) (rPow_nonneg _), stPlanUsed _ _ _ _ _ _ _ hA stRateZero⟩

/-- For thresholds Θ that serve (with the bound Lc): `TiedEvery Θ`, the seven statements of `TiedAt`
for all (c, P₀, A, val) that are the pieces of Appendix B. This is `tiedAt_of` in the form of a
statement of proof/variables/RecursionWithPieces/Defs.lean. -/
theorem tiedEvery (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (hΘ : StepSparsify.Serves Θ Lc) : TiedEvery Θ := fun _ _ _ _ h => tiedAt_of hΘ h

/-- `TiedEvery Θ` and the theorem on pieces with ρ = 1/√2, both hypotheses, give `TiedAll Θ`. -/
theorem tiedAll_of_tiedEvery {Θ : ℕ → ℕ → ℕ → ℕ} (h : TiedEvery Θ) (hB : AppRunningTime.ThmHalfPieces) : TiedAll Θ :=
  let ⟨c, P₀, A', val, hp⟩ := thmHalfPieces_iff.1 hB
  ⟨c, P₀, A', val, h c P₀ A' val hp⟩

/-- For thresholds Θ that serve (with the bound Lc): `TiedAll Θ`. The constant c and the programs
for the pieces are those of `AppRunningTime.thmHalfPieces`; the statement does not name them. -/
theorem tiedAll (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (hΘ : StepSparsify.Serves Θ Lc) : TiedAll Θ := tiedAll_of_tiedEvery (tiedEvery Θ Lc hΘ) AppRunningTime.thmHalfPieces

/-- **The end theorem, tied to its function.** There are a constant c and programs (P₀, val) for the
pieces of Appendix B such that: the recursion of Appendix A on them, on the schedule of display (40)
with the least x₀ of the theorem on the
general recursion, satisfies parts (b) and (c), first sentence, of that theorem; the function
`fnAll StepSparsify.thCal`, which sparsifies with the thresholds `StepSparsify.thCal`
(proof/variables/RecursionWithPieces/Defs.lean says what they are), counts each output by Steps 1 to
4 of Appendix D (`VariableBound.countD`) on that recursion,
with the level chosen by the named program `pickAB`, and is merged with the algorithm for the bound
in m on the same recursion, is with the exponent function `expAll` an algorithm for the rates of
Theorem 1; one machine puts out its value
on every input, with the pad of 2^(expAll x) units, and counts within the three bounds; a second
machine does the same for «some bit is 1»; and for every width and all large n the plan is used. The
statement fixes what the machines put out
and a bound on their steps, not the steps themselves; it names the algorithm and does not force the
argument by which the groupings exist, nor the way in which a network at the top level is handed to
the solver. The constant c and the programs are existentially quantified. What differs from the
printed text is listed in
proof/variables/RecursionWithPieces/Defs.lean. -/
theorem tiedAllCal : TiedAllCal := tiedAll _ _ StepSparsify.servesCal

end RecursionWithPieces

namespace SatM

/-- A corollary of `RecursionWithPieces.tiedAllCal`. One machine and one constant for all k ≥ 1: #k-SAT
on n ≥ 1 variables in time 2^{O(k²·n·log log n/√(log n))}; with m ≥ 1 clauses in which all variables
occur, in time 2^{O(k·m/√(log m))}; and, on n ≥ 1
variables that all occur, in time 2^{O(min of the two exponents)}. The statement names none of the
objects of proof/variables/RecursionWithPieces. -/
theorem targetUniform_all : TargetUniform :=
  let ⟨_, _, _, _, h⟩ := RecursionWithPieces.tiedAllCal
  VariableBound.count_of_tied h.counts

end SatM

namespace MainTheoremForms

open CountKSatRate ClauseBound.Alg

end MainTheoremForms

namespace RecursionWithPieces

open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen GeneralPieces MainTheoremForms

end RecursionWithPieces
