/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import CountKSatRate.Leaf
import all CountKSat.Top.Count
import all ClauseBound.ParityChecks.TopOL

/-! # Two lemmas on the function for the bound in n

If 2^β ≤ n + 1, then, since β ≥ k, k ≤ ⌊log₂(n+1)⌋, so that the cut-off `kcU` of the width does
nothing (`kcU_eq`).
With a pad of at least 2^n units, exhaustive counting on the decoded formula (`StBruteC`, `StDecU`)
returns the number of satisfying assignments (`brute_eq`). -/

namespace UniformInK.Correct

open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open PaddedDescent.F.Mark (WfL occ nSat)

/-- If 2^β ≤ n + 1, the cut-off of the width does nothing. -/
theorem kcU_eq {k n s : ℕ} (h : 2 ^ betaU k s ≤ n + 1) : kcU k n = k := by
  refine min_eq_left (Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_right (by norm_num) ?_) h))
  unfold betaU
  nlinarith [Nat.zero_le (k * s)]

/-- With a pad of at least 2^n units, exhaustive counting on the decoded formula returns the number
of satisfying assignments. -/
theorem brute_eq (hBr : StBruteC) (hDU : StDecU) {k n : ℕ} (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) (w : U) (hw : 2 ^ n ≤ w.length) :
    ((rng w (2 ^ n)).filter fun y => satAt (Decode.toN φ) y).length = SatK.numSat φ := by
  have h := hBr k n φ hk hφ w hw
  rw [bruteN, nK, hDU k n φ hk hφ.1] at h
  simpa using h

end UniformInK.Correct

namespace UniformInK

open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL UniformInK.Correct
open PaddedDescent.F.Mark (WfL occ nSat)

end UniformInK
