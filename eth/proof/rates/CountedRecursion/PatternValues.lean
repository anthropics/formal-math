/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PatternPsi
public import Printed.Coding
import Mathlib.Tactic

/-! # W_a and f_{a,a'} as the procedures compute them

For the network `patternNet D c g tr λ y W` (proof of Proposition 3, «Two networks for each ι», with
the pieces of Definition 7):
* `weight_eq`: «W_a is the product of the g table entries of row a and of the factors of the
  straight edges inside row a», in the form of `rowWeight`: the check `chkG`, then the product of
  the entries at the queries `pointQuery`;
* `factor_eq`: f_{a,a'}(z, θ) is `ClauseBound.Alg.gridFf` for the pieces, the form that `rowFactor`
  follows;
* `pair_eq`: Ψ_{a,a'} for a ≠ a', in either order, in the form of `rowPair` (from the statement
  `PairIsProduct`, a hypothesis here);
* the lengths of the strings that are cut out of a setting. From
  `ClauseBound.Alg.GridPresents.gridN_W`, `gridN_f`. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The network `gridN` of which `patternNet` is made. -/
noncomputable abbrev gridOf (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (W : ℕ → List Bool → ℤ) : Groundwork.Network (Fin (nParts g g tr)) (List Bool) (List Bool) :=
  gridN (piecesOf D c) [()] g g tr 0 lam y fun w θ => W w.val (List.ofFn θ).flatten

variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-- The settings of a row are the strings of g·g²·λ bits. -/
theorem mem_S_iff (a : Fin (nParts g g tr)) (z : List Bool) : z ∈ (patternNet D c g tr lam y W).S a ↔ z.length = nMemb g g tr * (g * g) * lam := mem_words

/-- The query to the tables at the grid point number i of the row a is a legitimate one. -/
theorem pointQuery_ok (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) {i : ℕ} (hi : i < nMemb g g tr) :
    (toTable (pointQuery g tr lam (a.val, z) i)).1 < g * g ∧ (toTable (pointQuery g tr lam (a.val, z) i)).2.length = (g * g - 1) * lam := by
  have hn : nodeG g tr a i < g * g := nodeG_lt tr a.2 hi
  refine ⟨hn, ?_⟩
  change ((List.range (g * g)).map fun u => if u = nodeG g tr a i then [] else heG g g lam z i u).flatten.length = _
  rw [map_range_eq_ofFn]
  refine length_flatten_ofFn ⟨nodeG g tr a i, hn⟩ _ (fun u hu => ?_) (if_pos rfl)
  rw [if_neg fun e => hu (Fin.ext e)]
  exact length_heG hz hi u.2

/-- **W_a**, as `rowWeight` computes it. -/
theorem weight_eq (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) :
    (patternNet D c g tr lam y W).W a z =
      if chkG g g tr lam (a.val, z) = true then ∏ i ∈ range (nMemb g g tr), W (toTable (pointQuery g tr lam (a.val, z) i)).1 (toTable (pointQuery g tr lam (a.val, z) i)).2 else 0 := by
  refine (gridN_W (piecesOf D c) [()] g g tr 0 lam y _ a hz).trans ?_
  by_cases hc : chkG g g tr lam (a.val, z) = true
  · obtain ⟨h1, h2⟩ := (chkG_iff g g tr lam a z).1 hc
    rw [if_pos hc, Finset.prod_eq_one (s := pairs (Fin (nMemb g g tr))) fun q hq => if_pos (h2 q hq), mul_one, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_pos (h1 i)]
    change W ((gridE g g tr).symm (a, i)).val (List.ofFn fun u => if u = (gridE g g tr).symm (a, i) then [] else heG g g lam z i u).flatten =
      W (nodeG g tr a i) ((List.range (g * g)).map fun u => if u = nodeG g tr a i then [] else heG g g lam z i u).flatten
    rw [GridNet.gridE_symm_val, map_range_eq_ofFn]
    congr 3
    funext u
    simp only [Fin.ext_iff, GridNet.gridE_symm_val]
  · rw [if_neg hc]
    rw [chkG_iff, not_and_or] at hc
    rcases hc with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]

/-- c_{a,a'} is the number `capG` computed from the pieces, the grid and the index y. -/
theorem c_eq {a b : Fin (nParts g g tr)} (hab : a ≠ b) : (patternNet D c g tr lam y W).c a b = capG (piecesOf D c) g g tr 0 lam y a b :=
  gridN_c (piecesOf D c) [()] g g tr 0 lam y (fun w θ => W w.val (List.ofFn θ).flatten) hab

/-- **f_{a,a'}(z, θ)** is the function `ClauseBound.Alg.gridFf` for the pieces. -/
theorem factor_eq {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) :
    (patternNet D c g tr lam y W).f a b z θ = gridFf (piecesOf D c) [()] g g tr 0 lam y ((a.val, b.val), (z, θ)) :=
  (gridN_f (piecesOf D c) [()] g g tr 0 lam y _ hab hz hθ).trans (gridFf_eq (piecesOf D c) [()] g g tr 0 lam y a b z θ).symm

/-- **Ψ_{a,a'}(z, z')** for a ≠ a', as `rowPair` computes it: the query is put in order, then the
check and the product. -/
theorem pair_eq (hPP : PairIsProduct) {ρ : ℝ} {x₀ : ℕ} (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hy : y < #(D.fam lam).I ^ nRectG g g) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z ∈ (patternNet D c g tr lam y W).S a) (hz' : z' ∈ (patternNet D c g tr lam y W).S b) :
    (patternNet D c g tr lam y W).Ψ a b z z' = if straightOK g tr lam (ordered ((a.val, b.val), (z, z'))) = true then
      ∏ j ∈ range (g * g), (if j / g < j % g then
        pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri (ordered ((a.val, b.val), (z, z'))).1.1 (ordered ((a.val, b.val), (z, z'))).1.2) (tri (j / g) (j % g))))
          (rectStrings g tr lam (ordered ((a.val, b.val), (z, z'))) (j / g) (j % g)) else 1)
    else 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · have e : ordered ((a.val, b.val), (z, z')) = ((a.val, b.val), (z, z')) := if_pos (Fin.lt_def.1 h)
    rw [e]
    exact hPP ρ c x₀ D hS g lam y tr W hg hlam hy a b h z hz z' hz'
  · have e : ordered ((a.val, b.val), (z, z')) = ((b.val, a.val), (z', z)) := if_neg (not_lt.2 (Fin.lt_def.1 h).le)
    rw [e]
    refine Eq.trans ?_ (hPP ρ c x₀ D hS g lam y tr W hg hlam hy b a h z' hz' z hz)
    exact Network.Ψ_comm (gridOf D c g tr lam y W) a b z z'

end ExplicitCost
