/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Prices

/-!
# Products of wires
-/

namespace Nc.Price

open Ov Ov.Ten Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (F : Spec K I)

section Wires

variable {E : Type} [Fintype E] [DecidableEq E]

/-- A product of wires: one of size n e from a e to b e for every e. -/
def wires (K : Type) [Field K] (a b : E → I) (n : E → ℕ) : Ten K I :=
  Ten.prod fun e => wire K (n e) (a e) (b e)

theorem F_wires (a b : E → I) {n : E → ℕ} (hn : ∀ e, 1 ≤ n e) :
    F.F (wires K a b n) = ∏ e, (n e : ℝ) ^ F.e (a e) (b e) := by
  rw [wires, F.prod]
  exact Finset.prod_congr rfl fun e _ => F.wire_eq _ _ (hn e)

end Wires

end Nc.Price
