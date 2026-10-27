/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Prog
public import StepMachines.Prog.SidePresents
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff

/-! # The cheaper side network has U ≤ Ubar

`min_price_le` bounds the smaller of the prices `priceRow` and `priceCol` of a choice `y` of pieces
(the part of the total U of the row and of the column side network that the rectangles add) by
ρ·g⁴·n + g⁴/2, with ρ = (log₂ 12)/4 ≈ 0.896, not the ρ = 11/12 of Lemma 2. This file proves ρ <
717/800 and
turns the bound into the natural number `Ubar g n`. -/

public section

namespace PaddedDescent.F.Price

open Groundwork Groundwork.Prog Groundwork.Grid

/-- ρ = (log₂ 12)/4 < 717/800, because 12²⁰⁰ < 2⁷¹⁷. -/
theorem rho_lt : ρ < 717 / 800 := by
  have h : Real.logb 2 ((12 : ℝ) ^ 200) < Real.logb 2 ((2 : ℝ) ^ 717) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  unfold ρ
  push_cast at h
  linarith

/-- The cheaper price plus the g²(g−1)n bits of the straight edges is at most the natural number
`Ubar g n`, by `min_price_le` and ρ < 717/800. -/
theorem min_price_nat (g n y : ℕ) : g ^ 2 * (g - 1) * n + min (priceRow g n y) (priceCol g n y) ≤ Ubar g n := by
  have h := min_price_le g n y
  have hρ := rho_lt
  have h0 : (0 : ℝ) ≤ (g : ℝ) ^ 4 * n := by positivity
  have h1 : ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ 717 / 800 * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 4 / 2 := by
    nlinarith
  have h2 : 800 * min (priceRow g n y) (priceCol g n y) ≤ 717 * g ^ 4 * n + 400 * g ^ 4 := by
    have : (800 : ℝ) * ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ 717 * (g : ℝ) ^ 4 * n + 400 * (g : ℝ) ^ 4 := by
      linarith
    exact_mod_cast this
  unfold Ubar
  generalize min (priceRow g n y) (priceCol g n y) = p at h2
  generalize 717 * g ^ 4 * n = A at h2 ⊢
  generalize g ^ 4 = D at h2 ⊢
  omega

/-- The side that `sideCtx` chooses has U ≤ Ubar. -/
theorem U_side_le (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g (decide (priceCol g n y < priceRow g n y)) n Rm y).U ≤ Ubar g n := by
  have h := min_price_nat g n y
  by_cases hlt : priceCol g n y < priceRow g n y
  · rw [decide_eq_true hlt, U_sideN_col]
    rwa [min_eq_right hlt.le] at h
  · rw [decide_eq_false hlt, U_sideN_row]
    rwa [min_eq_left (by omega)] at h

end PaddedDescent.F.Price
