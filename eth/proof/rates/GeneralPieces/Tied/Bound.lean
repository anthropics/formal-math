/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Tied.BoundDefs
public import GeneralPieces.ThmRunningTime
public import GeneralPieces.Num.Asymptotic
public import GeneralPieces.Half.Main

/-! # Part (c) of Theorem A, first sentence, and the bound in m, for programs fixed by name

`thmRunningTimeCm_tied` is the first sentence of part (c) of Theorem A, as stated in
`Tied/BoundDefs.lean`, for the named programs and every x₀ of the theorem; `thmHalfPieces_iff`
unfolds Theorem B (pieces with ρ = 1/√2).
`boundInM_tied` derives from Theorem B and part (c) the bound in m for the named programs
(`GeneralPieces.Tied.BoundInM`). -/

public section

namespace GeneralPieces

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half

/-- Part (c) of Theorem A, first sentence, for the named programs, for every x₀ of the theorem. -/
theorem thmRunningTimeCm_tied : Tied.ThmRunningTimeCm := fun _ _ _ _ _ _ h hx hc => thmRunningTime_c_m_tied_at h hx hc

/-- Theorem B (pieces with ρ = 1/√2) says that some programs are the pieces of Appendix B. -/
theorem thmHalfPieces_iff : AppRunningTime.ThmHalfPieces ↔ ∃ c P A val, Tied.IsPiecesB c P A val := Iff.rfl

/-- The bound in m for the named programs, from Theorem B (pieces with ρ = 1/√2) and part (c) of
Theorem A. -/
theorem boundInM_tied (hB : AppRunningTime.ThmHalfPieces) : Tied.BoundInM := by
  obtain ⟨c, P, A', val, h, ht⟩ := hB
  exact ⟨c, P, A', val, ⟨h, ht⟩, thmRunningTime_c_m_tied h⟩

end GeneralPieces
