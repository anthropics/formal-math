/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Defs
import Nc.Tape.Loop
import Nc.Tape.Refine
import Nc.Tape.Task
import Nc.Cut.Defs
import Nc.Cut.Groups
import Nc.Plus.UnitBits
import Nc.Cut.Slp

/-!
# Facts about the routing of units (general moves)
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

variable {F : Type} [CommRing F] {A A' E U0 U1 : ℕ}

section Plan

variable {M : Sys F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1}

theorem mem_newUnits_new {x : Fin E} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ newUnits M x o ↔ ν.1 = x ∧ k ≤ o ν := by
  simp [newUnits]

theorem init_not_mem_newUnitsR {x : Fin E} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∉ newUnits M x o := by
  simp [newUnits]

theorem init_mem_seen0R {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ seen0 n ↔ k.1 < (n a b).1 := by
  simp [seen0]

theorem new_not_mem_seen0R {ν : M.N} {k : Fin U1} : (Uid.new ν k : Uid A U0 M.N U1) ∉ seen0 n := by
  simp [seen0]

theorem mem_seenAt_init {x : ℕ} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ Plan.seenAt n o x ↔ k.1 < (n a b).1 := by
  unfold Plan.seenAt
  rw [Finset.mem_union, init_mem_seen0R]
  constructor
  · rintro (h | h)
    · exact h
    · obtain ⟨x', -, h⟩ := Finset.mem_biUnion.1 h
      exact absurd h init_not_mem_newUnitsR
  · exact Or.inl

theorem mem_seenAt_new {x : ℕ} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ Plan.seenAt n o x ↔ ν.1.1 < x ∧ k ≤ o ν := by
  unfold Plan.seenAt
  rw [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact absurd h new_not_mem_seen0R
    · obtain ⟨x', hx', h⟩ := Finset.mem_biUnion.1 h
      obtain ⟨rfl, h2⟩ := mem_newUnits_new.1 h
      exact ⟨(Finset.mem_filter.1 hx').2, h2⟩
  · rintro ⟨h1, h2⟩
    refine Or.inr (Finset.mem_biUnion.2 ⟨ν.1, ?_, mem_newUnits_new.2 ⟨rfl, h2⟩⟩)
    simpa using h1

/-- The units seen in the end. -/
theorem mem_seen_iff {id : Uid A U0 M.N U1} : id ∈ Plan.seenAt n o E ↔ unum id < ucnt n o id := by
  cases id with
  | init a b k => rw [mem_seenAt_init]; rfl
  | new ν k =>
    rw [mem_seenAt_new]
    constructor
    · rintro ⟨-, h⟩
      exact Nat.lt_succ_of_le h
    · intro h
      exact ⟨ν.1.2, Nat.le_of_lt_succ h⟩

end Plan

end Nc.G
