/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.Solver
public import ThreeSumApsp.Programs.Sec2.Theorem5.Program

/-!
# The running-time claim "Theorem 5" for the light model, for the program of Theorem 5

programThin is program5 followed by regimeBody (the test whether an instance is in the regime of
Theorem 5), thinBruteBody (the brute force, for the instances outside it) and thinBody (the solver
for all instances). claim_theorem_5: it solves the thin matrix product on all instances, and for D ≥
4 a power of four, N ≥ D^18, w ≤ N²/√D and entries of at most N^c its time is at most a constant
times N² log² D / D^{1/18}. This is thin_claim for the program and the solver of Theorem 5.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- The program of the thin matrix product on all instances. -/
def programThin : Program := program5 ++ [regimeBody, thinBruteBody, thinBody]

/-- **Theorem 5**, for programs of the light language. -/
theorem claim_theorem_5 : Claim.Theorem_5 lightModel :=
  thin_claim length_program5 rfl fun R => thm5_spec (mainCallees_of_prefix R)

end Light.Sec2
