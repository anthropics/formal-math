/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NamesInOrder.Defs
import MinOfBounds.Main
import MinOfBounds.Rename
import MinOfBounds.Arith
import Wrap.Main
import Wrap.Sim
import ToTuring.Closure.Basic
import VariableBound.Paper.Arith

/-! # The general case: a formula with any names
`generalFormFollows`: let N have the bound of the Main Theorem with nothing added, and let N′ run N
behind a front end that renames the variables that occur. The renamed formula has the same k and m,
its n variables all occur, and it has as many satisfying assignments as φ has on the variables that
occur (`MinOfBounds.renamedCodeIsTheCodeOfARenaming`). So N′ runs within q·(bound + L + 1)^q steps,
L the length
of the compact code, which `MinOfBounds.overheadGoesIntoC` turns into the bound for any names plus a
polynomial in L. `generalFormFollowsAsPropositions` uses `MinOfBounds.renamingFrontEndExists` and
`Wrap.everyMachineCanBeWrapped`. -/

public section

namespace NamesInOrder

open Turing Groundwork Wrap TwoMachines MainTheoremForms MinOfBounds
open Sat3 (CNF)

/-- 2^{C·min{a, b}}, rounded down, is at most each of 2^{C·a} and 2^{C·b}, rounded down. -/
theorem timeMin_le (C k m n : ℕ) : timeMin C k m n ≤ timeM C k m ∧ timeMin C k m n ≤ timeN C k n :=
  ⟨Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg C))),
   Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C)))⟩

/-- The general case, first half, for every machine. -/
theorem generalFormFollows : GeneralFormFollows := by
  intro N C hN ren hren N' q hW
  obtain ⟨C', hC'⟩ := overheadGoesIntoC C C q 1
  have hMin : MeetsMinBound N' C' := fun k V φ hk hφ hm hn => by
    obtain ⟨φ', hcode, -, -, -, hlen, hK, hocc, hnum⟩ := renamedCodeIsTheCodeOfARenaming k V φ
    have a := hN k (numOcc φ) φ' hk (hK hφ) (hlen ▸ hm) hn hocc
    unfold CountsWithin at a
    rw [hnum, ← hcode, hlen, ← hren k V φ hk hφ] at a
    have hL : 1 ≤ (encC k φ).length := by
      rw [VariableBound.Rename.lengthEncC]
      omega
    refine Outputs.mono (hW (encC k φ) _ _ a) ?_
    refine le_trans ?_ (hC' k φ.length (numOcc φ) (encC k φ).length (encC k φ).length hk hm hn hL (by simp))
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have h1 := (timeMin_le C k φ.length (numOcc φ)).1
    have h2 := (timeMin_le C k φ.length (numOcc φ)).2
    have : timeMin C k φ.length (numOcc φ) ≤ min (timeM C k φ.length + C * (encC k φ).length ^ C) (timeN C k (numOcc φ)) := le_min (h1.trans (Nat.le_add_right _ _)) h2
    omega
  exact ⟨C', hMin, (minBoundIsTheMainTheorem N' C').1 hMin⟩

/-- So the Main Theorem with nothing added to the bound, for formulas whose variables all occur,
gives the Main Theorem for formulas with any names, with a polynomial in the length of the code
added. -/
theorem generalFormFollowsAsPropositions : GeneralFormFollowsAsPropositions := by
  rintro ⟨N, C, hf, hN⟩
  obtain ⟨ren, hrenP, hren⟩ := renamingFrontEndExists
  obtain ⟨N', q, hf', hW⟩ := everyMachineCanBeWrapped N hf ren id hrenP PolyT.id'
  obtain ⟨C', -, h2⟩ := generalFormFollows N C hN ren hren N' q hW
  exact ⟨N', C', hf', h2⟩

end NamesInOrder
