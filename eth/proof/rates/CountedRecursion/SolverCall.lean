/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverPattern
import Mathlib.Tactic

/-! # The call for one pattern

* `child_eq`: the context of the call for the pattern y and the grouping x, written out: (ℓ, L, B')
  with the parent (K_ℓ, g_ℓ, λ, B, the lists, the direction, y, x).
* `child_size`: the context of each call is small: its size is bounded by the sizes of what the
  solver holds and of the number of patterns, and by K^g, g, gP and B'.
* `pattern_run`: the run for one pattern. With the calls answered as the specification says, at the
  price tc, `patternValue c` returns Z_ι within C·K^g + tc + 2 operations; and |Z_ι| ≤ 2^{gP +
  g²B₁}. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

/-- The context of the call for the pattern y and the grouping x. -/
theorem child_eq (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hy : y < nPatterns (readyOf D x₀ a.1)) (x : ℕ) :
    child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)) =
      ((unary l, unary (labelLength (searchInput c (readyOf D x₀ a.1, y))), unary (bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))), some (mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) (direction (readyOf D x₀ a.1, y)) y x)) := by
  obtain ⟨-, hsi, -, -⟩ := pattern_input hLL hBN hS hF hl hy
  have h1 : inK (searchInput c (readyOf D x₀ a.1, y)) = Levels.Gen.K x₀ l := by rw [hsi]; exact length_unary _
  have h2 : inG (searchInput c (readyOf D x₀ a.1, y)) = Levels.Gen.g x₀ l := by rw [hsi]; exact (length_unary _).trans (nParts_self _ _)
  have h3 : inP (searchInput c (readyOf D x₀ a.1, y)) = (Levels.Gen.g x₀ l ^ 3 * cLam a) := by rw [hsi]; exact length_unary _
  have h4 : inB (searchInput c (readyOf D x₀ a.1, y)) = (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) := by rw [hsi]; exact length_unary _
  have ht : a.1.1.tail = unary l := by
    rw [← unary_length_eq a.1.1.tail, List.length_tail]
    show unary (cLev a - 1) = _
    rw [hl]
    rfl
  refine Prod.ext (Prod.ext ht (Prod.ext rfl ?_)) (congrArg some (parentAt_readyOf D x₀ a.1 hl y x))
  show unary (bitsOut (inK (searchInput c (readyOf D x₀ a.1, y))) (inG (searchInput c (readyOf D x₀ a.1, y))) (inP (searchInput c (readyOf D x₀ a.1, y))) (inB (searchInput c (readyOf D x₀ a.1, y)))) = _
  rw [h1, h2, h3, h4]

/-- The size of a string of units. -/
theorem size_units (u : List Unit) : size u = 2 * u.length + 1 := by
  have h := size_unary' u.length
  rwa [unary_length_eq] at h

/-- The context of a call has size at most twice the size of what the solver holds and of the number
of patterns, plus the size of K^g, plus 2g, plus 6gP (twice the bound 3gP on L), plus 2B', plus 12. -/
theorem child_size (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (Bound : Ctx → Prop) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (a' : Ctx) (hC : (spec D c x₀ Bound).Child a f a') :
    size a' ≤ (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12) := by
  obtain ⟨-, y, x, hy, hfind, rfl⟩ := hC
  obtain ⟨-, -, -, hL3⟩ := pattern_input hLL hBN hS hF hl hy
  have hx : x < Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := by
    have h := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    rwa [rK_ready D x₀ a.1 hl, rG_ready D x₀ a.1 hl] at h
  rw [child_eq hLL hBN hS hF hl hy x]
  have s1 := size_le_of_le hx.le
  have s2 := size_le_of_le hy.le
  have s3 : size (readyOf D x₀ a.1) = size a.1.1 + (size a.1.2.1 + size a.1.2.2) + (size (unary (2 ^ (3 * (hLev a.1 - 1) + x₀))) + size (unary (Levels.Gen.K x₀ (hLev a.1 - 1)))) + size (listsOf D (cLam a)).1 +
      size (D.fam (cLam a)).d + size (listsOf D (cLam a)).2.1 + size (listsOf D (cLam a)).2.2 := rfl
  have s5 : hLev a.1 - 1 = l := by
    have : hLev a.1 = l + 1 := hl
    omega
  rw [s5, size_units, size_units, size_units, size_unary', size_unary'] at s3
  have s6 : a.1.2.1.length = cLam a := rfl
  have s7 : a.1.2.2.length = cB a := rfl
  have s8 : a.1.1.length = l + 1 := hl
  have hsz : size (((unary l, unary (labelLength (searchInput c (readyOf D x₀ a.1, y))), unary (bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))), some (mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) (direction (readyOf D x₀ a.1, y)) y x)) : Ctx) =
      size (unary l) + (size (unary (labelLength (searchInput c (readyOf D x₀ a.1, y)))) + size (unary (bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))))) + ((size (unary (Levels.Gen.K x₀ l)) + size (unary (Levels.Gen.g x₀ l))) + ((size (unary (cLam a)) + size (unary (cB a))) +
        ((size (listsOf D (cLam a)).1 + (size (listsOf D (cLam a)).2.1 + size (listsOf D (cLam a)).2.2)) + (1 + (size y + size x)))) + 1) := rfl
  rw [hsz, size_unary', size_unary', size_unary', size_unary', size_unary', size_unary', size_unary']
  omega

/-- **The run for one pattern.** -/
theorem pattern_run (hGW : GroupingWithCall) (hLL : LabelLengthIsL) (hV : ValueIsKept) (hBN : BothNetworks) (hC2 : CaseTwoApplies) (hSub : QueryMachines.StSubstWithin) (c : ℕ) :
    ∃ Cg : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → ∀ y < nPatterns (readyOf D x₀ a.1),
      (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs ≤ 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) ∧
      ∀ tc tq Lam : ℕ, (patternValue c).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) (readyOf D x₀ a.1, y) (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2))
        ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value := by
  obtain ⟨Cg, hCg⟩ := hGW
  refine ⟨Cg, fun ρ x₀ D hS Bound a f l hF hl y hy => ?_⟩
  obtain ⟨hIs, hsi, hL, hL3⟩ := pattern_input hLL hBN hS hF hl hy
  have hK2 := two_le_K (by have := hS.x₀_ge; omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  have habs : (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs ≤ 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) := by
    have h1 := Net.abs_value_le _ hIs
    have e : nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * (Levels.Gen.g x₀ l ^ 3 * cLam a) + nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) = Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) := by rw [nParts_self]
    rw [e, ← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  refine ⟨habs, fun tc tq Lam => ?_⟩
  have hy' := hy
  rw [nPatterns_ready D x₀ a.1 hl] at hy'
  have hcase := hC2 ρ c x₀ D hS l (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hF.1 hy'
  obtain ⟨x, hx, hfind, -, hY, hrun⟩ := hCg 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) _ hK0 (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) (tc + 2) hK2 (by rw [nParts_self]; omega) one_pos Nat.one_le_two_pow hIs (by rw [Nat.cast_one]; exact hcase)
  have e : Levels.Gen.K x₀ l ^ nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) = Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := by rw [nParts_self]
  have e' : nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) = Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) := by rw [nParts_self]
  rw [e] at hx hfind hrun
  rw [e'] at hrun
  have hval : (Value.groupClique asked.under (netInput (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) hK0 x (AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U)).value = (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value :=
    hV NetInput _ (Levels.Gen.K x₀ l) hK0 (asked.close (netOracle (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)))) (netInput (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) 1 _ (asked_isNetworkP (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) hIs) x _ hY
  have hce := child_eq hLL hBN hS hF hl hy x
  have hChild : (spec D c x₀ Bound).Child a f (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) :=
    ⟨by rw [hl]; omega, y, x, hy, by rw [rK_ready D x₀ a.1 hl, rG_ready D x₀ a.1 hl, hsi]; exact hfind, rfl⟩
  have hO : (spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f (Sum.inl (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)))) = some (.inl (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) := by
    have h1 : (spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f (Sum.inl (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)))) =
        some ((spec D c x₀ Bound).val (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) ((spec D c x₀ Bound).tab (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) f)) := by
      unfold Tower.Spec.oracle
      exact if_pos hChild
    rw [h1, child_value D c x₀ Bound _ f (K := Levels.Gen.K x₀ l) (g := Levels.Gen.g x₀ l) (lam := cLam a) (B := cB a) (y := y) (x := x) (tr := direction (readyOf D x₀ a.1, y))
      (L := AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U)
      (by rw [hce]; show Levels.Gen.K x₀ (unary l).length = _; rw [length_unary]) (by rw [hce]; rfl) (by rw [hce]; show (unary _).length = _; rw [length_unary, hL]) hK0, hval]
  have hrun' := patternValue_within hSub (c := c) (w := solPrices c tc tq) (v := (readyOf D x₀ a.1, y)) (x := x) (tc := tc) (Zc := (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value)
    (hG := fun O' hO' => by rw [hsi] at hO' ⊢; exact hrun O' (by rw [hO', hval])) hO rfl
  refine hrun'.mono le_rfl ?_
  have s0 := child_size hLL hBN hS Bound hF hl _ hChild
  have s1 : size (Sum.inl (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value : Ans) ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 3 := by
    have h2 : (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs.size ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 1 := Nat.size_le.2 (habs.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    simp only [size_inl, size_int]
    omega
  have s2 := size_le_of_le hy.le
  have s3 : size (callOf (searchInput c (readyOf D x₀ a.1, y), x)) ≤ size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) + 2 * Levels.Gen.K x₀ l := by
    have h1 : inK (searchInput c (readyOf D x₀ a.1, y)) = Levels.Gen.K x₀ l := by rw [hsi]; exact length_unary _
    have h6 : size (callOf (searchInput c (readyOf D x₀ a.1, y), x)) = size x + (size (unary (inK (searchInput c (readyOf D x₀ a.1, y)))) + (size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.1 + size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.2)) := rfl
    have h7 : size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) = size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.1 + (size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.1 + size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.2) +
        (size (parentAt (readyOf D x₀ a.1, y) x).1 + (size (parentAt (readyOf D x₀ a.1, y) x).2.1 + (size (parentAt (readyOf D x₀ a.1, y) x).2.2.1 + (1 + (size y + size x)))) + 1) := rfl
    rw [h6, h7, h1, size_unary']
    omega
  have t1 : size ((readyOf D x₀ a.1, y) : Ready × ℕ) = size (readyOf D x₀ a.1) + size y := rfl
  have t2 : size (((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)) : (Ready × ℕ) × CliqueCall) = size (readyOf D x₀ a.1) + size y + size (callOf (searchInput c (readyOf D x₀ a.1, y), x)) := rfl
  rw [t1, t2]
  omega

end ExplicitCost
