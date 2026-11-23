/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Straight-line programs over a small alphabet

A family of functions with values in `Fin D` is computed in `p` steps if there is a list of `p` functions, each an
input coordinate, a constant, or an arbitrary binary operation of two earlier ones, that contains the family.
-/

namespace Nc.Cut

variable {Inp ι : Type} {D : ℕ}

/-- One step of a straight-line program with input coordinates `inp`. -/
def IsSlpStep (inp : ι → Inp → Fin D) (fn : ℕ → Inp → Fin D) (k : ℕ) : Prop :=
  (∃ i, fn k = inp i) ∨ (∃ c, fn k = fun _ => c) ∨
    ∃ i < k, ∃ j < k, ∃ φ : Fin D → Fin D → Fin D, ∀ x, fn k x = φ (fn i x) (fn j x)

end Nc.Cut
