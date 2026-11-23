/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Vp.Gen
import Nc.Flag.Cases
import Nc.Tower.Tower
import Nc.Tow.FromPrice
import Nc.CaseI.Lower

/-!
# Near pairs and laws at the vertices of the towers
-/

set_option linter.unusedSectionVars false

namespace Nc.Vp

open Finset Nc.Price Nc.Tow Nc.CaseI
open Nc.Tower (U x NN ee tower card_U sum_NN npair npair_sym x_mul_self x_ne_one)

/-- One end of a near pair of U h. -/
abbrev cNear {h : ℕ} [NeZero h] (ν : NN h) : U h := ν.1.2

/-- The other end of a near pair of U h. -/
abbrev dNear {h : ℕ} [NeZero h] (ν : NN h) : U h := x h ν.1.1 * ν.1.2

/-- The laws at the vertices of the tower of U h with parameter n. -/
noncomputable def towFlag {F : Type} [CommRing F] {h : ℕ} [NeZero h]
    (VL : VLaws F (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h2 : 2 ≤ h) (n : ℕ) :
    FlagLaws F (tower h n h2) :=
  VL.toFlag (tower h n h2) (Equiv.refl (U h)) (Equiv.refl (NN h)) fun _ => rfl

end Nc.Vp
