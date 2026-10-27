/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.IsPoly

/-! `IsPolyT` is closed under the loops of `StepMachines/Prog/Range.lean`, for a polynomial-time
bound `N`. -/

@[expose] public section

namespace Groundwork

namespace IsPolyT

open Stepped

variable {α β γ : Type}

section range

variable [Enc α] {N : α → ℕ}

theorem rangeStart_poly (hN : PolyT N) : PolyT (rangeStart N) := by unfold rangeStart; fun_prop

theorem rangeNext_poly (hN : PolyT N) : PolyT (rangeNext N) := by unfold rangeNext; fun_prop

variable [HasSize α] [Carried α] [Enc β] {M : Stepped (α × ℕ) β} [IsPolyT M]

/-- The general loop: `M` is run on `(a, i)` for `i < N a` and its results are folded by `g`,
starting from `c₀ a`.
It is polynomial-time in every step if `M` is and `N`, `g` and `c₀` are polynomial-time. -/
@[instance_reducible] def foldRange [HasSize γ] [Enc γ] [Carried γ] {g : γ → ℕ → β → γ} {c₀ : α → γ}
    (hN : PolyT N) (hg : PolyT fun p : γ × ℕ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) :
    IsPolyT (foldRange N M g c₀) :=
  foldWhile (rangeStart_poly hN) (rangeNext_poly hN)
    (by unfold rangeG; exact PolyT.comp (g := fun p : γ × (α × ℕ) × β => (p.1, p.2.1.2, p.2.2)) hg (by fun_prop)) hc

/-- The loop that looks for the first `i` whose result satisfies `p`. -/
@[instance_reducible] def firstRange {p : β → Bool} (hN : PolyT N) (hp : PolyT p) : IsPolyT (firstRange N M p) :=
  foldRange hN
    ((by fun_prop : PolyT fun q : Option ℕ × ℕ × β =>
        q.1.elim (if p q.2.2 = true then some q.2.1 else none) fun i => some i).congr
      fun q => by rcases q with ⟨_ | i, y, b⟩ <;> rfl)
    (by unfold noneC; fun_prop)

end range

section rangeInt

variable [HasSize α] [Enc α] [Carried α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} [IsPolyT M]

/-- The loop that adds up the integer results. -/
@[instance_reducible] def sumRange (hN : PolyT N) : IsPolyT (sumRange N M) :=
  foldRange hN (by unfold addG; fun_prop) (by unfold zeroC; fun_prop)

/-- The loop that multiplies the integer results. -/
@[instance_reducible] def prodRange (hN : PolyT N) : IsPolyT (prodRange N M) :=
  foldRange hN (by unfold mulG; fun_prop) (by unfold oneC; fun_prop)

end rangeInt

end IsPolyT

end Groundwork
