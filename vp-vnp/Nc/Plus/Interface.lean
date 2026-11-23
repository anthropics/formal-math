/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Units with one holder in a group
-/

namespace Nc.Plus

/-- The unit has exactly one holder in the group `g`. -/
def OneIn {A mm : ℕ} {U : Type} (h0 h1 : U → Fin A) (a : Fin A → Fin mm) (g : Fin mm) (id : U) : Prop :=
  (a (h0 id) = g ∧ a (h1 id) ≠ g) ∨ (a (h0 id) ≠ g ∧ a (h1 id) = g)

instance {A mm : ℕ} {U : Type} (h0 h1 : U → Fin A) (a : Fin A → Fin mm) (g : Fin mm) (id : U) :
    Decidable (OneIn h0 h1 a g id) := by unfold OneIn; infer_instance

end Nc.Plus
