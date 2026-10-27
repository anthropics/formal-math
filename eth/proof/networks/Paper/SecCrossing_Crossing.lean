/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecNetworks_DefFactor
public import NetworkStatements
public import Groundwork.Cross.Cuts
public import Mathlib.Algebra.Polynomial.Coeff
public import StepMachines.Math.CutWord
public import StepMachines.Math.GridArith
public import StepMachines.Prog.CutProg
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # Section 4 of the paper, for a variant with other pieces: notation only

This file belongs to a variant of Section 4 of the paper that the paper does not print. The paper's
Lemma 2 cuts the strings into blocks of 3 bits and uses the eight-square identity, with ρ = 11/12;
the variant works bit by bit, with pieces A_0, …, A_λ and ρ = (log 12)/4.
The file holds only the notation of the variant.

How to read the Lean text.
* A bit is a `Bool` (`false` = 0, `true` = 1). A string in {0,1}^λ is `Bits lam = Fin lam → Bool`;
  `lam` stands for the
  paper's λ (`λ` is a reserved word of Lean), and the positions are t = 0, …, λ − 1 (the paper: 1,
  …, λ).
* ℤ[T] is `Polynomial ℤ`. `T` is the variable, and `C a` is the integer a as a constant polynomial. -/

@[expose] public section

namespace Paper

open Finset
open Groundwork (Bits)

local notation "T" => (Polynomial.X : Polynomial ℤ)
local notation "C" => (Polynomial.C : ℤ →+* Polynomial ℤ)


variable {lam : ℕ}


variable {Z Z' : Type*}


open Groundwork.Grid (sideCut)

end Paper
