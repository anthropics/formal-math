/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import PiecesStatement
public import ClauseBound.Rec.Window

/-! # Definitions for the blocks of labels: the signs σ_h and the labels on one block

The signs σ_h (`sg`) and the labels on one block (`BLab`).
Definitions only. -/

@[expose] public section

namespace ClauseBound.Rec

open Finset Polynomial Pieces

/-- σ_h = (−1)^{h₁·h₂}. -/
def sg (h : Bool × Bool) : ℤ := if h = (true, true) then -1 else 1

/-- The labels on block b. -/
abbrev BLab (n h : ℕ) (b : Fin (nblk n h)) : Type := {k : Fin n // k.val / h = b.val} → Bool × Bool

end ClauseBound.Rec
