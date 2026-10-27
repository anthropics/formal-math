/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PatternPsi
public import ClauseBound.Gen.Defs
import GeneralPieces.Rec.Chain
import Mathlib.Tactic

/-! # The totals of the two networks of a pattern

Proof of Theorem A (b), the step from ℓ to ℓ + 1: by Definition 7 (b), display (36) in the proof of
Proposition 3 becomes U = min(U^row, U^col) ≤ N/g + |ℛ|(4ρλ + c·log(2λ)) ≤ N(ρ + 1/g) +
(c/4)g⁴log(2λ).
* `capSum_piecesOf`: c^row_i + c^col_i ≤ 4ρλ + c·log(2λ), for the largest of these sums.
* `totalG_lists`: the totals computed from the lists are those computed from the pieces.
* `totalsAre : TotalsAre`: the totals that the solver compares are the totals U of the two networks
  (`ClauseBound.Alg.GridNet.U_gridN`).
* `smallerTotal : SmallerTotal`: the display, for every g ≥ 2: the minimum is at most the average
  (`ClauseBound.Gen.Chain.total_min_le`), clause (b) of Definition 7, and |ℛ| ≤ g⁴/4. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}

/-- c^row_i + c^col_i ≤ 4ρλ + c·log(2λ), for the largest of these sums. -/
theorem capSum_piecesOf (hS : Setting ρ c x₀ D) (h : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) : (capSum (piecesOf D c) h lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := by
  have hne : (range ((piecesOf D c).cnt h lam)).Nonempty := Finset.nonempty_range_iff.2 (Nat.pos_iff_ne_zero.1 (card_I_pos hS.is hlam))
  obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup _ hne fun i => (piecesOf D c).cap false h lam i + (piecesOf D c).cap true h lam i
  unfold capSum
  rw [e]
  exact hS.is.caps lam hlam _ (indexAt_mem D lam (Finset.mem_range.1 hj))

/-- The totals computed from the lists are those computed from the pieces. -/
theorem totalG_lists (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) (p d : ℕ) (tr : Bool) (y : ℕ) :
    totalG (listsAsPieces (listsOf D lam)) p d tr 0 lam y = totalG (piecesOf D c) p d tr 0 lam y := by
  obtain ⟨h1, h2⟩ := listsAgree D c lam (hS.short lam)
  exact totalG_congr h1 (h1.trans_ge (card_I_pos hS.is hlam)) (fun tr j hj => h2 tr j (hj.trans_eq h1)) p d tr y

/-- **The totals that the solver compares are the totals U of the two networks.** -/
theorem totalsAre : TotalsAre := by
  intro ρ c x₀ D hS g lam y tr W _ hlam
  rw [totalG_lists hS hlam]
  exact U_gridN (piecesOf D c) [()] g g tr 0 lam y fun w θ => W w.val (List.ofFn θ).flatten

/-- **U = min(U^row, U^col) ≤ N/g + |ℛ|(4ρλ + c·log(2λ)) ≤ N(ρ + 1/g) + (c/4)g⁴log(2λ).** -/
theorem smallerTotal : SmallerTotal := by
  intro ρ c x₀ D hS g lam y hg hlam _
  rw [totalG_lists hS hlam, totalG_lists hS hlam, ← GeneralPieces.Chain.total_eq_min]
  have h1 : ((totalG (piecesOf D c) g g (decide (totalG (piecesOf D c) g g true 0 lam y < totalG (piecesOf D c) g g false 0 lam y)) 0 lam y : ℕ) : ℝ) ≤
      ((g * (g - 1) * g * lam + nRectG g g * capSum (piecesOf D c) 0 lam : ℕ) : ℝ) :=
    Nat.cast_le.2 (ClauseBound.Gen.Chain.total_min_le (piecesOf D c) g 0 lam y (card_I_pos hS.is hlam))
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  -- «N/g»: the straight edges
  have hs : ((g * (g - 1) * g * lam : ℕ) : ℝ) ≤ (g : ℝ) ^ 3 * lam := by
    have : g * (g - 1) * g * lam ≤ g ^ 3 * lam := by
      calc g * (g - 1) * g * lam ≤ g * g * g * lam := by gcongr; exact Nat.sub_le _ _
        _ = g ^ 3 * lam := by ring
    exact_mod_cast this
  -- «|ℛ|(4ρλ + c·log(2λ))», and |ℛ| ≤ g⁴/4
  have hcap := capSum_piecesOf hS 0 hlam
  have h0 : 0 ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := le_trans (Nat.cast_nonneg _) hcap
  have hR : (nRectG g g : ℝ) ≤ (g : ℝ) ^ 4 / 4 := by
    have : ((4 * nRectG g g : ℕ) : ℝ) ≤ ((g ^ 4 : ℕ) : ℝ) := by exact_mod_cast ClauseBound.Gen.Rate.four_nRect_le g
    push_cast at this
    linarith
  have h2 : (nRectG g g : ℝ) * capSum (piecesOf D c) 0 lam ≤ (g : ℝ) ^ 4 / 4 * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) :=
    mul_le_mul hR hcap (Nat.cast_nonneg _) (by positivity)
  have e1 : (g : ℝ) ^ 4 * lam * (ρ + 1 / g) + (c : ℝ) / 4 * (g : ℝ) ^ 4 * Real.logb 2 (2 * lam) =
      (g : ℝ) ^ 3 * lam + (g : ℝ) ^ 4 / 4 * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by
    field_simp
    ring
  rw [e1]
  refine h1.trans ?_
  rw [Nat.cast_add, Nat.cast_mul (nRectG g g)]
  exact add_le_add hs h2

end ExplicitCost
