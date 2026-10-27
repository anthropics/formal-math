/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthVariableBoundStatement
public import ClauseBound.Both.Defs
public import ClauseBound.Gen.Defs
import ClauseBound.Both.TimeM
import ClauseBound.Both.End
import ClauseBoundStatement
import ClauseBound.Inst.Half
import all ClauseBound.ParityChecks.MasterOL
import all ClauseBound.TopN.Arith
import all ClauseBound.TopN.Gen
import ClauseBound.ParityChecks.TopOL
import ClauseBound.ParityChecks.CertTopOL
import ClauseBound.ParityChecks.CertOL
import ClauseBound.ParityChecks.BudgetOL
import ClauseBound.ParityChecks.ArithOL
import ClauseBound.TopN.Budget
import ClauseBound.TopN.Walk
import ClauseBound.Gen.End
import ClauseBound.Gen.Chain
import ClauseBound.Gen.Rate
import ClauseBound.Gen.Pick
import ClauseBound.Gen.Seq
import ClauseBound.Inst.HalfEnd
import ClauseBound.Inst.CertHalf
import ClauseBound.Alg.Enum
import ClauseBound.Alg.Grid
import ClauseBound.Alg.Level
import ClauseBound.Alg.Descend
import ClauseBound.Alg.Need
import ClauseBound.Alg.NeedC
import ClauseBound.Alg.CertEnum
import ClauseBound.Alg.CertGridG
import ClauseBound.Alg.CertLevel
import ClauseBound.Alg.CertTopNet
import ClauseBound.Alg.Decode
import ClauseBound.Alg.TopVal
import ClauseBound.Alg.CertTop
import ClauseBound.Alg.TopArith
import PaddedDescent.Col.CertG
import PaddedDescent.F.CertMark
import CountKSatRate.Tree
import CountKSatRate.Walk
import CountKSatRate.Pad
import CountKSatRate.Brute
import CountKSatRate.Stack
import CountKSat.InOut

/-! # Two rates of the bounds in n and in m are nonnegative

Two lemmas: the rate `SatK.rN 1 α n` = log₂ log₂(n+4)/(log₂(n+4))^α, of a bound in the number n of
variables, and the rate `SatM.rPow α m` = 1/(log₂(m+2))^α, of a bound in the number m of clauses,
are nonnegative for every real α. -/

public section

namespace ClauseBound.Both

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN ClauseBound.ParityChecks

/-- log₂ log₂(n+4)/(log₂(n+4))^α ≥ 0. -/
theorem rN_nonneg (α : ℝ) (n : ℕ) : 0 ≤ SatK.rN 1 α n := by
  unfold SatK.rN
  have h1 := one_le_loglog n
  have h2 := two_le_log n
  exact div_nonneg (by rw [pow_one]; linarith) (Real.rpow_nonneg (by linarith) _)

/-- 1/(log₂(m+2))^α ≥ 0. -/
theorem rPow_nonneg (α : ℝ) (m : ℕ) : 0 ≤ SatM.rPow α m := by
  unfold SatM.rPow
  exact div_nonneg zero_le_one (Real.rpow_nonneg (by linarith [ClauseBound.Gen.End.one_le_log m]) _)

end ClauseBound.Both

namespace SatK

end SatK
