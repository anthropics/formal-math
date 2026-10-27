/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.ArithSched
import PaddedDescent.F.ArithFits
import PaddedDescent.F.ArithTopInv
import PaddedDescent.F.ArithMark

/-! # `StA` and `StAW`: the pad of length 2^(8·(⌊n/2^(sOf n)⌋ + 1)) suffices for everything

`stA : StA` puts together the pieces of the arithmetic that do not know the width of the clauses,
for sOf n ≥ 1: the schedule is a chain; the pad suffices for the
rebalancing of a network of marks at the top and for the whole descent (`NetFits`), for the list of
profiles and for the word of the layers; the number of layers is
large enough (`MarkFits`); the pad suffices for the computation of the schedule. `stAW : StAW` has
what depends on the width k, for sOf n ≥ s0K k: the parameters are large
enough for width k, and the pad suffices for the rounds of the walk through the sparsification tree
and for its stack. No programs occur here: these are statements about
natural numbers. -/

public section

namespace PaddedDescent.F

open Arith

/-- The arithmetic that does not know the width. -/
theorem stA : StA := by
  intro k n F Δ hs hF hk hΔ
  have hY : Ytop (sOf n) ^ 6 ≤ n := Ytop_sOf_pow_le (by norm_num) hs
  have hF' : 2 ^ (8 * Xof (sOf n) n) ≤ F := hF
  have hE := exponents_le hY
  have hn : 6 ≤ n := by
    have h1 := hundred_Ytop_le hY
    have h2 := Ytop_ge (sOf n)
    omega
  have hfits := fits_of_inv (F := F) (e := 8 * Xof (sOf n) n) (Lw := 2 * Lof (sOf n) n) (Zof_ge (sOf n))
    (Zof_le_Qmof k (sOf n) n) (Qmof_lt hk hY) (poly_le hk hY) (by omega)
    (by
      have e : Lof (sOf n) n * (2 * Kseq (depthOf (sOf n)) ^ 2) = 2 * (Lof (sOf n) n * Kseq (depthOf (sOf n)) ^ 2) := by ring
      omega)
    (by omega) (by omega) hF' (depthOf (sOf n)) le_rfl _ _ _ (inv_at_top hk hΔ hY)
  refine ⟨?_, schedLen_le hs (by norm_num) hF⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, layLen_le hs (by norm_num) hF hk hΔ, layers_last hΔ hn, by positivity, le_rfl, clauses_le hΔ _⟩ <;>
    simp only [List.length_replicate]
  · exact chain_schedL _
  · exact le_trans (by norm_num) (Kseq_ge _)
  · exact top_col hY hF'
  · exact top_st hΔ hY hF'
  · exact top_lab hΔ hY hF'
  · exact top_tab hk hΔ hY hF'
  · exact hfits
  · exact nProf_le hs (by norm_num) hF hΔ

/-- The arithmetic that knows the width. -/
theorem stAW : StAW := fun _k _n _F hk hs hF =>
  ⟨le_of_s0K_le hs, leafC_add_two_le hs, top_rounds hs hF, stackLen_le hk hs (by norm_num) hF⟩

end PaddedDescent.F
