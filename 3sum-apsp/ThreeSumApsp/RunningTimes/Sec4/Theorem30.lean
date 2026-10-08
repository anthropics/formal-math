/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.OfflineStatement
public import ThreeSumApsp.Programs.Sec4.Theorem30.Program

/-!
# Theorem 30 on the word RAM

The route.  The preprocessing and the query are procedures of the light language, proved against the
paper's definitions (`Light.Sec4.preCoreSpec_all`, `Light.Sec4.queryAtSpec_all`; for the program
`Light.Sec4.program30`: `Light.Sec4.preCore_base58`, `Light.Sec4.queryAt_base58`).  The
preprocessing computes the shared encodings of Section 2 and then, for every tile, the trie of its
boxes, filled by the dynamic program of Lemma 29.  A query forms the sum of Lemma 28: the products
at the leaves of order below `t`, read from the encodings, plus the values of the boxes of the
output string, looked up in the trie of the tile.  The running times are bounded by the two costs of
the theorem, and the numbers and addresses that occur are polynomial in `N` ("Word size").  Two
outermost procedures read the input layout, and the compiler turns them into the two programs of the
data structure (`Light.Sec4.theorem_30_of`).  The offline form (9) preprocesses and then asks one
query for each wanted position (`Light.Sec4.theorem_30_wanted_of`).
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

/-- **Theorem 30**, on the word RAM: the two-stage data structure. -/
theorem wordRam_theorem_30 : Items.Theorem_30 :=
  Light.Sec4.theorem_30_of (P := Light.Sec4.program30) rfl rfl (Light.Sec4.preCore_base58 _)
    (Light.Sec4.queryAt_base58 _)

/-- **Theorem 30**, on the word RAM: the offline form (9). -/
theorem wordRam_theorem_30_wanted : Items.Theorem_30_wanted :=
  Light.Sec4.theorem_30_wanted_of (P := Light.Sec4.program30) rfl rfl (Light.Sec4.preCore_base58 _)
    (Light.Sec4.queryAt_base58 _)

end ThreeSumApsp
