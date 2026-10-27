/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Section 3 of the paper, Definition 1: factoring through c bits

This file imports Mathlib only. It renders Definition 1 of the paper as a predicate,
`Paper.FactorsThrough F c`.

**Not on the path to Theorem 2.** In the proof of Theorem 2 the functions Ψ of a network are *defined*
by their factorization
(`Groundwork.Network.Ψ`), so the predicate is never needed there.
-/

@[expose] public section

namespace Paper

open Finset

variable {X X' : Type*}

/-- **Definition 1 of the paper.** The function F : X × X' → ℤ *factors through c bits* if there are
f : X × {0,1}^c → ℤ and
f' : X' × {0,1}^c → ℤ with F(z, z') = ∑_θ f(z, θ) · f'(z', θ), the sum over all θ ∈ {0,1}^c.
Differences from the paper: a bit string of length c is a function `Fin c → Bool`; F takes its two
arguments one after the
other; X and X' need not be finite (the paper assumes that they are, and does not use it in the
definition). -/
def FactorsThrough (F : X → X' → ℤ) (c : ℕ) : Prop :=
  ∃ (f : X → (Fin c → Bool) → ℤ) (f' : X' → (Fin c → Bool) → ℤ),
    ∀ z z', F z z' = ∑ θ : Fin c → Bool, f z θ * f' z' θ

end Paper
