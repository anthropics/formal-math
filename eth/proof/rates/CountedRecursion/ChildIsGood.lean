/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CallFacts
import Mathlib.Tactic

/-! # A call is good

`childIsGoodFrom : ChildIsGoodFrom`. Proof of Theorem A (b): Case (ii) of Lemma 8 applies to the
network with the smaller total (with B₁ in the role of B), so the lemma's L satisfies K²L ≤ U + 2ζN +
K² ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K². Proof of Lemma 8: the (K, L)-clique with the tables W̃_γ has
the value of the network, and |W̃_γ| < 2^{B'}.
The clauses, in the order of the statement:
* the level, L and B' are read off the context (`at_call`);
* the callee is well formed: L ≥ 1, B' ≥ 1, and |W̃_γ| < 2^{B'} is the second half of
  `EntryCostExplicit`;
* its value is that of the clique of the groups (`child_value`), which is that of the network
  (`ValueIsKept`);
* U is the smaller of the two totals (`TotalsAre`, `total_direction`), which is bounded by
  `SmallerTotal`; then `LabelBound`. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- U = min(U^row, U^col) ≤ … ≤ N(ρ + 1/g) + (c/4)g⁴log(2λ), for the network that the solver takes. -/
theorem callNet_total_le (hT : TotalsAre) (hSm : SmallerTotal) {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {a : Ctx} (f : TableQuery → Option Ans) {l y : ℕ} (hl : cLev a = l + 1) (hlam : 1 ≤ cLam a)
    (hy : y < #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l)) :
    ((callNet D c x₀ l a f y).U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * cLam a * (ρ + 1 / Levels.Gen.g x₀ l) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) := by
  have hg2 := (level_numbers hS.x₀_ge l).2.2
  have e : (callNet D c x₀ l a f y).U = min (totalG (listsAsPieces (listsOf D (cLam a))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (cLam a) y)
      (totalG (listsAsPieces (listsOf D (cLam a))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (cLam a) y) :=
    (hT ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hg2 hlam).trans (total_direction D x₀ a.1 hl y)
  rw [e]
  exact hSm ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) y hg2 hlam hy

/-- **A call is good**, from Lemma 8 up to the call, its L, the bound on the entries, the fact that
the value of the clique is that of the network, and the printed steps on the network with the
smaller total. -/
theorem childIsGoodFrom : ChildIsGoodFrom := by
  intro hG hL hE hV hBN hT hSm hC hLB ρ c x₀ D hS Bound a a' f l hF hl hc
  obtain ⟨y, x, h⟩ := at_call hG hL hC hBN hS hF hl hc
  obtain ⟨c₁, hE⟩ := entryCost_cast hE
  obtain ⟨hK2, hKg, hg2⟩ := level_numbers hS.x₀_ge l
  obtain ⟨hlam, -, -, -⟩ := fits_succ hF hl
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  have hpY : pY (parentOf a') = y := by rw [h.parent]; rfl
  have hpK : pK (parentOf a') = Levels.Gen.K x₀ (cLev a') := by
    rw [h.parent, h.lev]
    exact length_unary _
  refine ⟨h.lev, ⟨?_, ?_, groupTables D c (parentOf a') (cLam a') (readTables f), ?_, ?_⟩, ?_, ?_, ?_, h.bits⟩
  · rw [h.lam]
    exact h.L_pos
  · rw [h.bits]
    exact (Nat.mul_pos (Nat.pow_pos (by omega)) h.is.B_pos).trans_le (Nat.le_add_left _ _)
  · intro w hw z hz
    rw [h.lev] at hw hz
    rw [h.lam] at hz
    rw [h.parent, h.lam, h.bits]
    unfold callParent
    rw [groupTables_mkParent]
    beta_reduce
    rw [dif_pos hw]
    exact (hE _ _ _ (nParts_self _ _) _ (callNet D c x₀ l a f y) _ _ 1 hKg h.is le_rfl x h.x_lt _ (h.L_le.trans (Nat.le_mul_of_pos_left _ (by norm_num))) (h.few _) (h.short _) ⟨w, hw⟩ z hz).2
  · change answersOf (pK (parentOf a')) (cLam a') _ = _
    rw [hpK]
  · rw [hpY, nPatterns_readyOf D x₀ a.1 hl]
    exact h.y_lt
  · rw [hpY, child_value D c x₀ Bound a' f (congrArg (Levels.Gen.K x₀) h.lev) h.parent h.lam hK0]
    exact congrArg Sum.inl (groupClique_value hV hK0 (callNet D c x₀ l a f y) h.is x _ (h.short hK0))
  · rw [h.lam]
    exact hLB ρ c x₀ l (cLam a) _ hS.is.rho_ge hS.x₀_ge hlam (callNet_total_le hT hSm hS f hl hlam h.y_lt)

end ExplicitCost
