/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.RunningTimes.Sec3.Theorem19
public import ThreeSumApsp.RunningTimes.Sec5.Corollary39.MinMaxWeight

/-!
# Corollary 39 on the word RAM

The route, as in the paper: the reduction from `k`-Clique to a triangle problem on `n^{⌊k/3⌋}`
vertices per part, once for each choice of the vertices in the `k mod 3` remaining parts, followed
by Theorem 19. The exponent `k − ε_T ⌊k/3⌋` has `ε_T = 0.0017`, which belongs to the bound of
Theorem 19 using Corollary 26, so that bound is used.  For minimum and maximum weight the triangle
problem is Max-Weight Triangle, which is solved by a search with a solver of Exact Triangle.

The proof has three parts, which `corollary_39_zero_of_theorem_19` and
`corollary_39_min_max_of_theorem_19` put together: the reduction as a program that calls an
arbitrary solver, with its time; the arithmetic of the running times, for every reading of "is
solved in time T"; and the way from programs of the light language to the word RAM.
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

/-- **Corollary 39**, the zero-weight case, on the word RAM. -/
theorem wordRam_corollary_39_zero : Items.Corollary_39_zero :=
  Light.Sec5.corollary_39_zero_of_theorem_19 Light.Sec3.claim_theorem_19_usingCorollary26

/-- **Corollary 39**, the minimum-weight and maximum-weight cases, on the word RAM. -/
theorem wordRam_corollary_39_min_max : Items.Corollary_39_min_max :=
  Light.Sec5.corollary_39_min_max_of_theorem_19 Light.Sec3.claim_theorem_19_usingCorollary26

end ThreeSumApsp
