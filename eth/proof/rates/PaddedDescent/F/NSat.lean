/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.MarkMath
public import StepMachines.Prog.Count

/-! # The count is positive exactly if the formula is satisfiable -/

namespace PaddedDescent.F.Mark.NSat

open Groundwork Groundwork.Prog

/-- A formula on variables below n has a satisfying assignment of these n variables exactly if it is
satisfiable. -/
public theorem nSat_pos_iff {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) : 0 < nSat n x ↔ Fml.Sat x := by
  unfold nSat Fml.Sat
  rw [Finset.card_pos]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨ext σ, (Finset.mem_filter.1 hσ).2⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun C hC => ?_⟩⟩
    obtain ⟨l, hl, hal⟩ := ha C hC
    refine ⟨l, hl, ?_⟩
    rw [ext, dif_pos (hx C hC l hl)]
    exact hal

/-- The same for the integer that the program compares with 0. -/
public theorem cast_nSat_pos_iff {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) : 0 < (nSat n x : ℤ) ↔ Fml.Sat x := by
  rw [Int.natCast_pos]; exact nSat_pos_iff hx

end PaddedDescent.F.Mark.NSat
