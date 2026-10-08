/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Corollary15_16.Split
public import ThreeSumApsp.Programs.Sec4.Corollary26.Claim
public import ThreeSumApsp.RunningTimes.FromClaims
public import ThreeSumApsp.RunningTimes.Sec3.Corollary15_16.Layout
public import ThreeSumApsp.TimeClaims.Sec3.Corollary15_16

/-!
# Corollaries 15 and 16 on the word RAM

The route, as in the paper.  The number of triangles through a query pair is an entry of the product
of the two biadjacency matrices, and detection follows from counting.  So Theorem 5 gives the first
case of Corollary 15; splitting the query pairs into pieces gives the general case; and the offline
form of Corollary 26 gives Corollary 16.  These are claims about programs of the light language
(`claim_corollary_15_first`, `claim_corollary_15`, `claim_corollary_16`).  The outermost procedures
for the input layout and the compiler (`Light.Sec3.realized_lopCount`,
`Light.Sec3.realized_lopDetect`, together `lopRealized`) carry them to the word RAM.
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-- Corollary 15, the case of at most `n²/√D` query pairs, for programs of the light language. -/
theorem claim_corollary_15_first : Claim.Corollary_15_first lightModel :=
  Corollary15.first_of_theorem_5 _ Sec2.claim_theorem_5
    claim_lopCountFromThinProduct claim_lopDetectFromCount

/-- Corollary 15, the general case, for programs of the light language. -/
theorem claim_corollary_15 : Claim.Corollary_15_general lightModel :=
  Corollary15.general_of_theorem_5 _ Sec2.claim_theorem_5
    claim_lopCountFromThinProduct claim_lopSplit claim_lopDetectFromCount

/-- Corollary 16 for programs of the light language. -/
theorem claim_corollary_16 : Claim.Corollary_16 lightModel :=
  Corollary16.of_corollary_26 _ Sec4.claim_corollary_26_wanted
    claim_lopCountFromThinProduct claim_lopDetectFromCount

/-- The outermost procedures and the compiler carry the running times of both problems to the word
RAM. -/
theorem lopRealized : FromClaims.LopRealized lightModel :=
  ⟨realized_lopCount, realized_lopDetect⟩

end Light.Sec3

namespace ThreeSumApsp

/-- **Corollary 15**, on the word RAM. -/
theorem wordRam_corollary_15 : Items.Corollary_15 :=
  FromClaims.Corollary15.of_claim _ Light.Sec3.lopRealized Light.Sec3.claim_corollary_15

/-- **Corollary 16**, on the word RAM. -/
theorem wordRam_corollary_16 : Items.Corollary_16 :=
  FromClaims.Corollary16.of_claim _ Light.Sec3.lopRealized Light.Sec3.claim_corollary_16

end ThreeSumApsp
