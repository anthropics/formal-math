/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Price.Hyper

/-!
# The points u/2, u ∈ {-1,0,1}^k, of the cube
-/

namespace Nc.CaseI

open Finset

variable {k : ℕ}

/-- The sign 1 or -1 of a bit. -/
def bsign (b : Bool) : SignType := if b then 1 else -1

/-- The place of u in {-1,0,1}^k: the point u/2 of ℝ^k. -/
noncomputable def half (u : Fin k → SignType) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun x => ((u x : SignType) : ℝ) / 2

theorem half_apply (u : Fin k → SignType) (x : Fin k) : half u x = ((u x : SignType) : ℝ) / 2 := rfl

/-- Opposite vertices of the cube have the distance √k. -/
theorem dist_half_neg (π : Fin k → Bool) :
    dist (half fun x => bsign (π x)) (half fun x => -bsign (π x)) = √k := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h : ∀ x, dist (half (fun x => bsign (π x)) x) (half (fun x => -bsign (π x)) x) ^ 2 = 1 := by
    intro x
    rw [half_apply, half_apply, Real.dist_eq]
    cases π x <;> simp [bsign] <;> norm_num
  simp [h]

end Nc.CaseI
