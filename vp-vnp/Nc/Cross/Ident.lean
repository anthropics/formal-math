/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cross.Inv
import Nc.Cross.One
import Nc.Cross.Count

/-!
# The states of given size and energy, as words

The index sets of Paper.prop_identity (Paper/Identity.lean).
-/

namespace Nc.Cross

open Finset

/-- The states of size `μ` and energy `e`. -/
def states (μ e : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (pairs e).filter fun s => s.1.card = μ ∧ s.2.card = μ ∧ en s.1 + en s.2 = e

section word

variable {μ e : ℕ}

theorem states_prop (s : ↥(states μ e)) :
    s.1.1.card = μ ∧ s.1.2.card = μ ∧ en s.1.1 + en s.1.2 = e := (mem_filter.1 s.2).2

/-- The word of a state. -/
def word (s : ↥(states μ e)) : Wd μ :=
  (s.1.1.orderEmbOfFin (states_prop s).1, s.1.2.orderEmbOfFin (states_prop s).2.1)

theorem word_strictMono (s : ↥(states μ e)) : StrictMono (word s).1 ∧ StrictMono (word s).2 :=
  ⟨(s.1.1.orderEmbOfFin (states_prop s).1).strictMono, (s.1.2.orderEmbOfFin (states_prop s).2.1).strictMono⟩

theorem word_injective : Function.Injective (word : ↥(states μ e) → Wd μ) := by
  intro s s' h
  have h1 : ((s.1.1 : Finset ℕ) : Set ℕ) = s'.1.1 := by
    rw [← Finset.range_orderEmbOfFin _ (states_prop s).1, ← Finset.range_orderEmbOfFin _ (states_prop s').1]
    exact congrArg Set.range (Prod.ext_iff.1 h).1
  have h2 : ((s.1.2 : Finset ℕ) : Set ℕ) = s'.1.2 := by
    rw [← Finset.range_orderEmbOfFin _ (states_prop s).2.1, ← Finset.range_orderEmbOfFin _ (states_prop s').2.1]
    exact congrArg Set.range (Prod.ext_iff.1 h).2
  exact Subtype.ext (Prod.ext (Finset.coe_injective h1) (Finset.coe_injective h2))

theorem sum_orderEmb (S : Finset ℕ) {k : ℕ} (h : S.card = k) :
    ∑ i, (2 * S.orderEmbOfFin h i + 1) = en S := by
  conv_rhs => rw [en, ← Finset.map_orderEmbOfFin_univ S h, Finset.sum_map]
  rfl

theorem enW_word (s : ↥(states μ e)) : enW (word s) = e := by
  rw [enW, word, sum_orderEmb, sum_orderEmb]
  exact (states_prop s).2.2

theorem enW_swap (w : Wd μ) : enW w.swap = enW w := by
  rw [enW, enW, add_comm]
  rfl

end word

end Nc.Cross
