/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.Program
public import ThreeSumApsp.RunningTimes.FromClaims
public import ThreeSumApsp.RunningTimes.Sec3.Corollary15_16.Layout

/-!
# Theorem 5 on the word RAM

The route.  The solver of Section 2.4.4 is a procedure of the light language.  "Is solved in time T"
asks for a right answer on every input, so the procedure first tests whether the input is in the
regime of the theorem and falls back on brute force outside it; in the regime its running time obeys
the bound of the theorem (`Light.Sec2.claim_theorem_5`).  An outermost procedure reads the sizes
`N`, `D` and `|W|` from the input layout, forms the bound `N^κ` on the entries, computes the
addresses of the two matrices, of the wanted positions and of the output, and calls the solver; the
compiler turns the program into one for the word RAM (`Light.Sec3.realized_thinProduct`).
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

/-- **Theorem 5**, on the word RAM. -/
theorem wordRam_theorem_5 : Items.Theorem_5 :=
  FromClaims.Theorem5.of_claim Light.lightModel Light.Sec3.realized_thinProduct
    Light.Sec2.claim_theorem_5

end ThreeSumApsp
