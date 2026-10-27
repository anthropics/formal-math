/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PatternIs
public import Printed.GroupingProcs
import Mathlib.Tactic

/-! # The numbers in a parent

* `pG_mk`, …: the g, λ, B, lists, direction and pattern number of `mkParent D K g λ B tr y x`;
* `digG_ofLists`, `lenG_ofLists`, `capG_ofLists`: the plain functions of
  proof/rates/ClauseBound/Alg/Data.lean give the same numbers for the lists as for the pieces (from
  the statement `ListsAgree`, a hypothesis here, and the congruence lemmas of GridLemmas.lean);
* `netData_eq`: the input of Definition 2(iii) that the procedure writes from the parent is the
  input that belongs to the network of the pattern. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-! ## The parts -/

/-- The g of the parent for these numbers. -/
theorem pG_mk : pG (mkParent D K g lam B tr y x) = g := List.length_replicate
/-- Its λ. -/
theorem pLam_mk : pLam (mkParent D K g lam B tr y x) = lam := List.length_replicate
/-- Its B. -/
theorem pB_mk : pB (mkParent D K g lam B tr y x) = B := List.length_replicate
/-- Its lists. -/
theorem pLists_mk : pLists (mkParent D K g lam B tr y x) = listsOf D lam := rfl
/-- Its direction. -/
theorem pTr_mk : pTr (mkParent D K g lam B tr y x) = tr := rfl
/-- The number of its pattern. -/
theorem pY_mk : pY (mkParent D K g lam B tr y x) = y := rfl
/-! ## The lists give the numbers of the pieces -/

/-- What the congruence lemmas ask. -/
theorem lists_agree (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    (listsAsPieces (listsOf D lam)).cnt 0 lam = (piecesOf D c).cnt 0 lam ∧ 1 ≤ (listsAsPieces (listsOf D lam)).cnt 0 lam ∧
      ∀ tr, ∀ j < (listsAsPieces (listsOf D lam)).cnt 0 lam, (listsAsPieces (listsOf D lam)).cap tr 0 lam j = (piecesOf D c).cap tr 0 lam j := by
  obtain ⟨h1, h2⟩ := hLA D c lam (hS.short lam)
  refine ⟨h1, ?_, fun tr j hj => h2 tr j ?_⟩
  · rw [h1]
    exact card_I_pos hS.is hlam
  · rw [h1] at hj
    exact hj

/-- ι at a rectangle, from the lists and from the pieces. -/
theorem digG_ofLists (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (d : ℕ) (tr : Bool) (y q κ : ℕ) : digG (listsAsPieces (listsOf D lam)) d tr 0 lam y q κ = digG (piecesOf D c) d tr 0 lam y q κ :=
  digG_congr (lists_agree hLA hS hlam).1 d tr y q κ

/-- The length of the chunk of a rectangle, from the lists and from the pieces. -/
theorem lenG_ofLists (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (d : ℕ) (tr : Bool) (y q κ : ℕ) : lenG (listsAsPieces (listsOf D lam)) d tr 0 lam y q κ = lenG (piecesOf D c) d tr 0 lam y q κ :=
  lenG_congr (lists_agree hLA hS hlam).1 (lists_agree hLA hS hlam).2.1 (lists_agree hLA hS hlam).2.2 d tr y q κ

/-- c_{a,a'}, from the lists and from the pieces. -/
theorem capG_ofLists (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (p d : ℕ) (tr : Bool) (y a b : ℕ) : capG (listsAsPieces (listsOf D lam)) p d tr 0 lam y a b = capG (piecesOf D c) p d tr 0 lam y a b :=
  capG_congr (lists_agree hLA hS hlam).1 (lists_agree hLA hS hlam).2.1 (lists_agree hLA hS hlam).2.2 p d tr y a b

/-! ## The input that the procedure writes -/

/-- **The input that the procedure writes is the input that belongs to the network.** -/
theorem netData_eq (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    netData c (mkParent D K g lam B tr y x) = ((unary K, unary g), netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) := by
  have e : inputOf g (g ^ 3 * lam) (bitsOne c g lam B) (fun _ => nMemb g g tr * (g * g) * lam) (fun a b => capG (listsAsPieces (listsOf D lam)) g g tr 0 lam y a b) =
      inputOf (nParts g g tr) (g ^ 3 * lam) (bitsOne c g lam B) (fun _ => nMemb g g tr * (g * g) * lam) (fun a b => capG (listsAsPieces (listsOf D lam)) g g tr 0 lam y a b) := by
    rw [nParts_self]
  unfold netData netP netB netLen netCap
  simp only [pG_mk, pLam_mk, pB_mk, pLists_mk, pTr_mk, pY_mk]
  refine congrArg (Prod.mk (unary K, unary g)) (e.trans (inputOf_eq (patternNet D c g tr lam y W) _ _ _ _ (fun a => ?_) fun a b hab => ?_))
  · change nMemb g g tr * (g * g) * lam = g ^ 3 * lam
    rw [nMemb_self]
    ring
  · rw [capG_ofLists hLA hS hlam, c_eq hab]

end ExplicitCost
