/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Search
public import Eight.ViaGrouping.Keeps
public import Eight.ViaGrouping.Table
public import Eight.ViaGrouping.Main

/-! # Lemma 1 along the printed proof: the bound on steps

The steps of the proof are proved in the files imported here: «A good grouping exists» and the
search (Search.lean), the tables W̃_γ, their bound, the cost of an entry and «the value equals Z»
(Table.lean), the paragraph «Cost»
(Main.lean), polynomial-time steps (Keeps.lean). This file puts them together into a bound on the
steps of the algorithm of the proof (`stLemGrouping`); that these steps take polynomial time is
`stKeeps`. Display.lean, which nothing here imports, says that what `tableM` returns is the display
of W̃_γ in the paper. -/

public section

namespace Eight.ViaGrouping

/-- **Lemma 1 for the algorithm of its proof**: if E evaluates (K, λ)-cliques with the exponent e,
then `netAlg K (3K⁸) E` evaluates networks on [3K⁸] with the exponent e(U + gP/K) + 2gP/K. A bound
on steps; that the steps take polynomial time is `stKeeps`. -/
theorem stLemGrouping : StLemGrouping := stLemGrouping_of stSearch stTable stValue

end Eight.ViaGrouping
