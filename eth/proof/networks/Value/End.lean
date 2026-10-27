/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Value.Clique
public import Value.Joint

/-! # «… so the value equals Z»

Proof of Lemma 1, end of the paragraph «The algorithm». The value of the clique of the groups, as
the network of Definition 3 with two copies of the string on every edge, is
1. a sum over one string per edge of the product of the tables (`StCliqueValue`, the sentence after
   Definition 3);
2. a sum over all z ∈ ∏ S_a and over one string θ_{a,b} per pair {a, b} of nodes in different groups
   (`StJointSum`);
3. after the sum over each θ_{a,b}, the sum that defines Z (`StSumOut`).
`stValueEqualsZOf` puts the three together, `stValueEqualsZ` is the sentence. `stValueOf` and
`stValue` give the step in the form `Eight.ViaGrouping.StValue`, in which the proof of Lemma 1 in
proof/networks/Eight/ViaGrouping takes it. -/

public section

namespace Value

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

/-- «so the value equals Z», from the sentences before it. -/
theorem stValueEqualsZOf : StValueEqualsZOf := by
  intro hC hJ hS C _ g K hK0 Np c N P B τ S h x L hL
  unfold groupClique
  rw [hC K L (display Np c N hK0 x), hJ C g K hK0 Np c N P B τ S h x L hL]
  exact sum_congr rfl fun z hz => hS g K P B N h.is (Paper.grouping hK0 x) z hz

/-- **«… so the value equals Z»**: the clique of the groups, as the network of Definition 3, has the
value of the network N. -/
theorem stValueEqualsZ : StValueEqualsZ := stValueEqualsZOf stCliqueValue stJointSum stSumOut

/-- From «so the value equals Z» for the clique as a network to the form with one string per edge
and the tables `Paper.groupedTables`: back by the sentence after Definition 3, and the tables are
given by the display of W̃_γ. -/
theorem stValueOf : StValueOf := by
  intro hC hV K g hK0 C _ Np c N P B τ S h x L hL
  rw [← hV C g K hK0 Np c N P B τ S h x L hL]
  unfold groupClique
  rw [hC K L (display Np c N hK0 x), Paper.cliqueValue_def]
  exact sum_congr rfl fun Λ hΛ => prod_congr rfl fun γ _ =>
    groupedTables_eq_display h hK0 x L hL γ _ fun γ' hne => mem_words.1 (((mem_tuples _ _ _ _).1 (star_mem hΛ γ) γ').1 hne)

/-- «… so the value equals Z», in the form in which the proof of Lemma 1 takes the step. (A
different declaration from the theorem of the same name in `Eight.ViaGrouping`; it is proved here
without using that theorem.) -/
theorem stValue : Eight.ViaGrouping.StValue := stValueOf stCliqueValue stValueEqualsZ

end Value
