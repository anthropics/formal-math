/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs

/-! # The test whether every variable occurs

`stAllOccU`: on the code of an instance the test `allOccU` says whether every variable occurs. -/

public section

namespace UniformInK.CorrectB

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

end UniformInK.CorrectB

namespace UniformInK

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK.CorrectB

/-- On the code of an instance the test says whether every variable occurs. -/
theorem stAllOccU (hD : StDecM) : StAllOccU := by
  intro k n φ hk hφ
  have hd := (hD k n φ hk hφ.1).2
  unfold allOccU nU
  simp only [hd, List.length_replicate, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq]
  constructor
  · intro h i
    obtain ⟨C, hC, l, hl, hlv⟩ := h i.val i.2
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨C', hC', l', hl', Fin.ext hlv⟩
  · intro h v hv
    obtain ⟨C, hC, l, hl, hlv⟩ := h ⟨v, hv⟩
    exact ⟨_, List.mem_map.2 ⟨C, hC, rfl⟩, _, List.mem_map.2 ⟨l, hl, rfl⟩, by rw [hlv]⟩

end UniformInK
