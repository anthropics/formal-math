/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CallLemma
import Mathlib.Tactic

/-! # What is known at a call

«Case (ii) of Lemma 8 applies to the network with the smaller total (with B₁ in the role of B).» A
call that the specification permits (`spec.Child`) goes to the context that the solver makes from
the number y of a pattern and the first grouping x that the test of Lemma 8 accepts. `at_call`
collects what follows, for the use of `childIsGoodFrom` and `procedureCostFrom`:
the parts of the callee's context (ℓ, L, B' and the parent); the network of the pattern is a network
with the parameters P = g³λ and B₁; the input that the procedure writes from the parent belongs to
it; x has at most 2g/K nodes in every group and Y_{γ,γ'} ≤ L; 1 ≤ L ≤ gP. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The network with the smaller total of the pattern number y, for the instance (a, f) of the level
ℓ + 1. -/
@[expose] noncomputable def callNet (D : PiecesCounted.Data) (c x₀ l : ℕ) (a : Ctx) (f : TableQuery → Option Ans) (y : ℕ) : Net (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) :=
  patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)

/-- The L of Lemma 8 for it: ⌈(U + 2ζgP)/K²⌉ with ζ = 2^{−ℓ−5}, P = g³λ. -/
@[expose] noncomputable def callL (D : PiecesCounted.Data) (c x₀ l : ℕ) (a : Ctx) (f : TableQuery → Option Ans) (y : ℕ) : ℕ :=
  AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (callNet D c x₀ l a f y).U

/-- The parent in the context of the callee. -/
@[expose] def callParent (D : PiecesCounted.Data) (x₀ l : ℕ) (a : Ctx) (y x : ℕ) : Parent :=
  mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) (direction (readyOf D x₀ a.1, y)) y x

/-- What is known of the callee a' of the instance (a, f) of the level ℓ + 1, for the pattern number
y and the grouping number x. -/
structure AtCall (D : PiecesCounted.Data) (c x₀ l : ℕ) (a a' : Ctx) (f : TableQuery → Option Ans) (y x : ℕ) : Prop where
  y_lt : y < #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l)
  x_lt : x < Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l
  lev : cLev a' = l
  lam : cLam a' = callL D c x₀ l a f y
  bits : cB a' = bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))
  parent : parentOf a' = callParent D x₀ l a y x
  is : (callNet D c x₀ l a f y).Is (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))
  data : netData c (callParent D x₀ l a y x) =
    ((unary (Levels.Gen.K x₀ l), unary (Levels.Gen.g x₀ l)), netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))
  few : ∀ (hK0 : 0 < Levels.Gen.K x₀ l) (γ : Fin (Levels.Gen.K x₀ l)),
    Levels.Gen.K x₀ l * #{v : Fin (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) | Paper.grouping hK0 x v = γ} ≤ 2 * Levels.Gen.g x₀ l
  short : ∀ (hK0 : 0 < Levels.Gen.K x₀ l) (γ γ' : Fin (Levels.Gen.K x₀ l)), γ ≠ γ' → Y (callNet D c x₀ l a f y).c (Paper.grouping hK0 x) γ γ' ≤ callL D c x₀ l a f y
  L_pos : 1 ≤ callL D c x₀ l a f y
  L_le : callL D c x₀ l a f y ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)

/-- **A permitted call**: the callee belongs to a pattern y and to the first grouping x that the
test of Lemma 8 accepts on the network with the smaller total, and all of `AtCall` holds. -/
theorem at_call (hG : GroupingWithCall) (hL : LabelLengthIsL) (hC : CaseTwoApplies) (hBN : BothNetworks) {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {Bound : Ctx → Prop} {a a' : Ctx}
    {f : TableQuery → Option Ans} {l : ℕ} (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hc : (spec D c x₀ Bound).Child a f a') : ∃ y x : ℕ, AtCall D c x₀ l a a' f y x := by
  obtain ⟨-, y, x, hy, hfind, rfl⟩ := hc
  obtain ⟨hK2, hKg, hg2⟩ := level_numbers hS.x₀_ge l
  obtain ⟨hlam, hB1, hW, -⟩ := fits_succ hF hl
  have hl' : hLev a.1 = l + 1 := hl
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  rw [nPatterns_readyOf D x₀ a.1 hl'] at hy
  rw [rK_readyOf D x₀ a.1 hl', rG_readyOf D x₀ a.1 hl'] at hfind
  obtain ⟨C₂, hBN⟩ := hBN c
  have hb := fun x' (hx' : x' < Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) =>
    hBN ρ x₀ D hS (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) y x' 0 (cLam a) (direction (readyOf D x₀ a.1, y)) (readTables f) hg2 hKg hlam le_rfl hB1 hW hy hx'
  obtain ⟨hIs, -, hdata0, -⟩ := hb 0 (Nat.pow_pos hK0)
  have hpar : ∀ x', parentAt (readyOf D x₀ a.1, y) x' = callParent D x₀ l a y x' := fun x' => parentAt_readyOf D x₀ a.1 hl' y x'
  have hin : searchInput c (readyOf D x₀ a.1, y) = ((1, 2 ^ (l + 5)), ((unary (Levels.Gen.K x₀ l), unary (Levels.Gen.g x₀ l)),
      netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := by
    have e : hLev (rHead (readyOf D x₀ a.1, y).1) + 4 = l + 5 := by
      change hLev a.1 + 4 = l + 5
      omega
    unfold searchInput
    rw [hpar, e]
    exact congrArg (Prod.mk (1, 2 ^ (l + 5))) hdata0
  rw [hin] at hfind
  obtain ⟨hx, h1, h2, h3⟩ := firstGrouping_cast hG hL (nParts_self _ _) hK0 (callNet D c x₀ l a f y) hK2 hg2 Nat.one_le_two_pow hIs
    (hC ρ c x₀ D hS l (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hlam hy) hfind
  have hU : (callNet D c x₀ l a f y).U ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) :=
    (netTotal_le _ hIs).trans_eq (by rw [nParts_self])
  obtain ⟨hL1, hL2⟩ := Lof_bounds (b := 2 ^ (l + 5)) hK2 (by omega) hIs.P_pos Nat.one_le_two_pow hU
  refine ⟨y, x, hy, hx, ?_, ?_, ?_, hpar x, hIs, (hb x hx).2.2.1, fun _ => h1, fun _ => h2, hL1, hL2⟩
  · change (a.1.1.tail).length = l
    have e : a.1.1.length = l + 1 := hl
    rw [List.length_tail, e]
    rfl
  · change (unary (labelLength (searchInput c (readyOf D x₀ a.1, y)))).length = _
    rw [length_unary, hin]
    exact h3
  · change (unary (bitsOut (inK (searchInput c (readyOf D x₀ a.1, y))) (inG (searchInput c (readyOf D x₀ a.1, y))) (inP (searchInput c (readyOf D x₀ a.1, y))) (inB (searchInput c (readyOf D x₀ a.1, y))))).length = _
    rw [length_unary, hin]
    change bitsOut (unary _).length (unary _).length (unary _).length (unary _).length = _
    simp only [length_unary]

end ExplicitCost
