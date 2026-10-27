/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SquareGrid
import Mathlib.Tactic

/-! # The lists and the pieces

* `digG_congr`, `lenG_congr`, `capG_congr`, `priceG_congr`, `totalG_congr`: the plain functions of
  proof/rates/ClauseBound/Alg/Data.lean that give the numbers of the two networks of a pattern read
  only `cnt` and `cap` of the pieces, and `cap` only at numbers below `cnt`.
* `listsAgree : ListsAgree`: the numbers read from the lists that the solver has after its queries
  are those of the pieces; so the functions above agree on `listsAsPieces (listsOf D λ)` and
  `piecesOf D c`.
* Lemmas on the pieces of Definition 7 in the form `piecesOf D c`: sums over 𝓘 (`sum_indexAt`), the
  functions of the two pairs of strings (`top_piecesOf`, `bot_piecesOf`), and 𝓘 is not empty
  (`card_I_pos`). -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-! ## The functions read only cnt and cap -/

section congr

variable {P P' : PiecesF} {h ℓ : ℕ}

/-- ι at a rectangle reads only the number of pieces. -/
theorem digG_congr (hc : P.cnt h ℓ = P'.cnt h ℓ) (d : ℕ) (tr : Bool) (y q κ : ℕ) : digG P d tr h ℓ y q κ = digG P' d tr h ℓ y q κ := by
  unfold digG
  rw [hc]

/-- The length of the chunk of a rectangle reads only `cnt` and `cap`. -/
theorem lenG_congr (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (d : ℕ) (tr : Bool) (y q κ : ℕ) :
    lenG P d tr h ℓ y q κ = lenG P' d tr h ℓ y q κ := by
  unfold lenG
  rw [← digG_congr hc]
  exact hcap tr _ (digG_lt hpos d tr y q κ)

/-- So does c_{a,a'}. -/
theorem capG_congr (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (p d : ℕ) (tr : Bool) (y a b : ℕ) :
    capG P p d tr h ℓ y a b = capG P' p d tr h ℓ y a b := by
  unfold capG
  exact congrArg _ (Finset.sum_congr rfl fun κ _ => lenG_congr hc hpos hcap d tr y _ κ)

/-- So does what the rectangles cost in a network. -/
theorem priceG_congr (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (p d : ℕ) (tr : Bool) (y : ℕ) :
    priceG P p d tr h ℓ y = priceG P' p d tr h ℓ y := by
  unfold priceG
  refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
  rw [← hc]
  refine hcap tr _ ?_
  have := Prog.digit_le (P.cnt h ℓ - 1) y q
  omega

/-- So does the total U. -/
theorem totalG_congr (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (p d : ℕ) (tr : Bool) (y : ℕ) :
    totalG P p d tr h ℓ y = totalG P' p d tr h ℓ y := by
  unfold totalG
  rw [priceG_congr hc hpos hcap]

end congr

/-! ## The lists -/

/-- The element number j of a list under a map. -/
theorem getD_map_of_lt {α β : Type} (f : α → β) (l : List α) {j : ℕ} (hj : j < l.length) (d : α) (d' : β) : (l.map f).getD j d' = f (l.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map]

/-- The list of 𝓘 has |𝓘| entries. -/
theorem length_sortI (D : PiecesCounted.Data) (lam : ℕ) : ((D.fam lam).I.sort).length = #(D.fam lam).I := Finset.length_sort _

/-- The element number j < |𝓘| of 𝓘 is in 𝓘. -/
theorem indexAt_mem (D : PiecesCounted.Data) (lam : ℕ) {j : ℕ} (hj : j < #(D.fam lam).I) : indexAt D lam j ∈ (D.fam lam).I := by
  have hj' : j < ((D.fam lam).I.sort).length := by rw [length_sortI]; exact hj
  unfold indexAt
  rw [List.getD_eq_getElem _ _ hj']
  exact (Finset.mem_sort _).1 (List.getElem_mem hj')

/-- **The numbers read from the lists are those of the pieces.** -/
theorem listsAgree : ListsAgree := by
  intro D c lam hshort
  refine ⟨length_sortI D lam, fun tr j hj => ?_⟩
  have hj' : j < ((D.fam lam).I.sort).length := by rw [length_sortI]; exact hj
  change min ((if tr = true then (listsOf D lam).2.2 else (listsOf D lam).2.1).getD j 0) (2 * lam) = D.cap lam tr (indexAt D lam j)
  have e : (if tr = true then (listsOf D lam).2.2 else (listsOf D lam).2.1).getD j 0 = D.cap lam tr (indexAt D lam j) := by
    cases tr
    · exact getD_map_of_lt (fun i => D.cap lam false i) _ hj' 0 0
    · exact getD_map_of_lt (fun i => D.cap lam true i) _ hj' 0 0
  rw [e]
  exact min_eq_left (hshort tr _)

/-! ## Lemmas on the pieces in the form `piecesOf D c` -/

/-- A sum over the places of a list. -/
theorem sum_range_getD {α : Type} (f : α → ℤ) (d : α) (l : List α) : ∑ j ∈ range l.length, f (l.getD j d) = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    exact congrArg₂ _ rfl ih

/-- A sum over 𝓘 is the sum over its places. -/
theorem sum_indexAt (D : PiecesCounted.Data) (lam : ℕ) (f : ℤ → ℤ) : ∑ j ∈ range #(D.fam lam).I, f (indexAt D lam j) = ∑ i ∈ (D.fam lam).I, f i := by
  rw [← length_sortI]
  unfold indexAt
  rw [sum_range_getD, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]

/-- A string written as a list and read again. -/
theorem toBits_bitsOf {n : ℕ} (x : Pieces.Bits n) : PiecesCounted.toBits n (ClauseBound.Alg.bitsOf x) = x := by
  funext j
  unfold PiecesCounted.toBits ClauseBound.Alg.bitsOf
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- The functions of a factorization, called with strings written as lists. -/
theorem fn_bitsOf (D : PiecesCounted.Data) {lam : ℕ} (tr side : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (if θ.length = D.cap (ClauseBound.Alg.bitsOf x).length tr (indexAt D (ClauseBound.Alg.bitsOf x).length j) then
      D.fn (ClauseBound.Alg.bitsOf x).length tr side (indexAt D (ClauseBound.Alg.bitsOf x).length j) (PiecesCounted.toBits _ (ClauseBound.Alg.bitsOf x), PiecesCounted.toBits _ (ClauseBound.Alg.bitsOf y)) θ else 0) =
      if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr side (indexAt D lam j) (x, y) θ else 0 := by
  have key : ∀ n, n = lam → (if θ.length = D.cap n tr (indexAt D n j) then D.fn n tr side (indexAt D n j) (PiecesCounted.toBits n (ClauseBound.Alg.bitsOf x), PiecesCounted.toBits n (ClauseBound.Alg.bitsOf y)) θ else 0) =
      if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr side (indexAt D lam j) (x, y) θ else 0 := by
    intro n hn
    subst hn
    rw [toBits_bitsOf, toBits_bitsOf]
  exact key _ (List.length_ofFn)

/-- The function of the first pair of strings, in the form that this development uses. -/
theorem top_piecesOf (D : PiecesCounted.Data) (c : ℕ) {lam : ℕ} (pad : U) (tr : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (piecesOf D c).top ((pad, tr), (0, j), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr false (indexAt D lam j) (x, y) θ else 0 :=
  fn_bitsOf D tr false j x y θ

/-- The function of the second pair of strings, in the form that this development uses. -/
theorem bot_piecesOf (D : PiecesCounted.Data) (c : ℕ) {lam : ℕ} (pad : U) (tr : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (piecesOf D c).bot ((pad, tr), (0, j), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr true (indexAt D lam j) (x, y) θ else 0 :=
  fn_bitsOf D tr true j x y θ

/-- 𝓘 is not empty. -/
theorem card_I_pos {ρ : ℝ} {c : ℕ} {D : PiecesCounted.Data} (h : D.Is ρ c) {lam : ℕ} (hlam : 1 ≤ lam) : 1 ≤ #(D.fam lam).I := by
  by_contra hne
  have h0 : (D.fam lam).I = ∅ := Finset.card_eq_zero.1 (by omega)
  have hs := h.sum lam hlam (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
  have hd := h.d_pos lam hlam
  rw [h0, Finset.sum_empty] at hs
  simp only [Pieces.cross, and_self, if_true, mul_one] at hs
  omega

end ExplicitCost
