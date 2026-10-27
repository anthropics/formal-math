/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RowWeightRun
import Mathlib.Tactic

/-! # The procedure for Ψ_{a,a'}
`rowPair_within`: on settings z, z' of two rows a ≠ a', the procedure `rowPair` returns Ψ_{a,a'}(z,
z') of the network of the pattern within g²·(2^{cλ} + 3) operations; each A_i is one query to the
pieces, about strings of λ bits only.
«Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows» (proof of
Proposition 3). The bound on the states is explicit. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-- The four strings of a rectangle have λ bits. -/
theorem length_rectStrings {q : PsiQ} (ha : q.1.1 < nParts g g tr) (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hz' : q.2.2.length = nMemb g g tr * (g * g) * lam)
    {i i' : ℕ} (hi : i < nMemb g g tr) (hi' : i' < nMemb g g tr) :
    (rectStrings g tr lam q i i').1.length = lam ∧ (rectStrings g tr lam q i i').2.1.length = lam ∧ (rectStrings g tr lam q i i').2.2.1.length = lam ∧ (rectStrings g tr lam q i i').2.2.2.length = lam := by
  cases tr
  · exact ⟨length_heG hz hi (nodeG_lt false hb hi'), length_heG hz hi' (nodeG_lt false hb hi), length_heG hz' hi (nodeG_lt false ha hi'), length_heG hz' hi' (nodeG_lt false ha hi)⟩
  · exact ⟨length_heG hz hi (nodeG_lt true hb hi'), length_heG hz' hi (nodeG_lt true ha hi'), length_heG hz hi' (nodeG_lt true hb hi), length_heG hz' hi' (nodeG_lt true ha hi)⟩

/-- The pieces answer the question for A_i at four strings of λ bits. -/
theorem pieces_value {i : ℤ} (hi : i ∈ (D.fam lam).I) {s : List Bool × List Bool × List Bool × List Bool} (h1 : s.1.length = lam) (h2 : s.2.1.length = lam) (h3 : s.2.2.1.length = lam) (h4 : s.2.2.2.length = lam)
    (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) {u : List Unit} (hu : u.length = lam) : piecesUpTo D Lam (u, .inr (.inr (.inr (.inl (i, s))))) = some (Sum.inl (pieceValue D lam i s)) := by
  subst hu
  change (if u.length ≤ Lam then (if 1 ≤ u.length then
    (if i ∈ (D.fam u.length).I ∧ s.1.length = u.length ∧ s.2.1.length = u.length ∧ s.2.2.1.length = u.length ∧ s.2.2.2.length = u.length then some (Sum.inl (pieceValue D u.length i s)) else none) else none) else none) = _
  rw [if_pos hLam, if_pos hlam, if_pos ⟨hi, h1, h2, h3, h4⟩]

/-- A query for Ψ put in order has the same size. -/
theorem size_ordered (q : PsiQ) : size (ordered q) = size q := by
  unfold ordered
  split_ifs
  · rfl
  · simp only [size_prod]
    omega

/-- The check and the loop of `rowPair`, after the query has been put in order. -/
def pairLoop : QueryMachine UpQuery Ans (Parent × PsiQ) ℤ :=
  QueryMachine.ite (fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2)
    (QueryMachine.prodRange (fun x : Parent × PsiQ => pG x.1 * pG x.1)
      (QueryMachine.ite (fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × PsiQ) × ℕ => Sum.inr (rectQuestion v)) (QueryMachine.const 1)))
    (QueryMachine.const 0)

/-- `rowPair` puts the query in order and runs the loop. -/
theorem rowPair_eq : rowPair = QueryMachine.mapIn (fun x : Parent × PsiQ => (x.1, ordered x.2)) pairLoop := rfl

/-- The factor number j of the loop. -/
def pairItem (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : PsiQ) (j : ℕ) : ℤ :=
  if j / g < j % g then pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri q.1.1 q.1.2) (tri (j / g) (j % g)))) (rectStrings g tr lam q (j / g) (j % g)) else 1

/-- It is below 2^{(2λ)^c} in absolute value. -/
theorem abs_pairItem_lt (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (q : PsiQ) (j : ℕ) : |pairItem D c g tr lam y q j| < 2 ^ (2 * lam) ^ c := by
  unfold pairItem
  split_ifs
  · exact hS.is.size_A lam hlam _ (dig_mem hS hlam g tr y _ _) _ _ _ _
  · rw [abs_one]
    exact one_lt_pow₀ (by norm_num) (by positivity)

/-- The check and the loop, run. -/
theorem pairLoop_within (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    {q : PsiQ} (ha : q.1.1 < nParts g g tr) (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hz' : q.2.2.length = nMemb g g tr * (g * g) * lam) :
    pairLoop.Within (upOracle D g lam Lam W) (upPrices c tq) (p, q) (g * g * (askCost c lam + 1)) (2 * size (p, q) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9)
      (if straightOK g tr lam q = true then ∏ j ∈ range (g * g), pairItem D c g tr lam y q j else 0) := by
  subst hG hL hT hY
  by_cases hc : straightOK (pG p) (pTr p) (pLam p) q = true
  · rw [if_pos hc]
    have hbody : ∀ j < pG p * pG p, (QueryMachine.ite (fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × PsiQ) × ℕ => (Sum.inr (rectQuestion v) : UpQuery)) (QueryMachine.const 1)).Within
        (upOracle D (pG p) (pLam p) Lam W) (upPrices c tq) ((p, q), j) (askCost c (pLam p)) (size (p, q) + size (pG p * pG p) + (2 * pLam p) ^ c + 4) (pairItem D c (pG p) (pTr p) (pLam p) (pY p) q j) := by
      intro j hj
      have s2 := size_lt_le hj
      have s3 : size ((p, q), j) = size (p, q) + size j := rfl
      have hi : j / pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.div_lt_of_lt_mul hj
      have hi' : j % pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.mod_lt _ hg
      by_cases hlt : j / pG p < j % pG p
      · obtain ⟨l1, l2, l3, l4⟩ := length_rectStrings ha hb hz hz' hi hi'
        have hidx : pieceAt p (tri q.1.1 q.1.2) (tri (j / pG p) (j % pG p)) = indexAt D (pLam p) (digG (piecesOf D c) (pG p) (pTr p) 0 (pLam p) (pY p) (tri q.1.1 q.1.2) (tri (j / pG p) (j % pG p))) := by
          unfold pieceAt
          rw [hLs, digG_ofLists hLA hS hlam]
          rfl
        have hv : upOracle D (pG p) (pLam p) Lam W (Sum.inr (rectQuestion ((p, q), j))) = some (Sum.inl (pairItem D c (pG p) (pTr p) (pLam p) (pY p) q j)) := by
          unfold pairItem
          rw [if_pos hlt]
          change piecesUpTo D Lam (p.2.1.1, .inr (.inr (.inr (.inl (pieceAt p (tri q.1.1 q.1.2) (tri (j / pG p) (j % pG p)), rectStrings (pG p) (pTr p) (pLam p) q (j / pG p) (j % pG p)))))) = _
          rw [hidx]
          exact pieces_value (dig_mem hS hlam _ _ _ _ _) l1 l2 l3 l4 hlam hLam rfl
        have hq := query_within (A := Ans) (h := fun v : (Parent × PsiQ) × ℕ => (Sum.inr (rectQuestion v) : UpQuery)) (w := upPrices c tq) (a := ((p, q), j)) hv
        refine (ite_within_true (p := fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_true hlt) (mapOut_within (g := asInt) hq)).mono le_rfl ?_
        have s1 := size_answer (abs_pairItem_lt (g := pG p) (tr := pTr p) (y := pY p) hS hlam q j)
        omega
      · have e : pairItem D c (pG p) (pTr p) (pLam p) (pY p) q j = 1 := if_neg hlt
        rw [e]
        refine (ite_within_false (p := fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_false hlt) (lift_within (Stepped.const_runs (1 : ℤ) _))).mono ?_ ?_
        · unfold askCost
          omega
        · have : size (1 : ℤ) = 2 := rfl
          omega
    have hprod := prodRange_within (N := fun x : Parent × PsiQ => pG x.1 * pG x.1) (a := (p, q)) (fun _ => askCost c (pLam p)) (pairItem D c (pG p) (pTr p) (pLam p) (pY p) q) (2 ^ (2 * pLam p) ^ c) _ Nat.one_le_two_pow hbody
      fun j _ => Table.natAbs_le (abs_pairItem_lt hS hlam q j).le
    dsimp only at hprod
    refine (ite_within_true (p := fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc hprod).mono (le_of_eq ?_) ?_
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    · have := size_two_pow_pow ((2 * pLam p) ^ c) (pG p * pG p)
      omega
  · rw [if_neg hc]
    rw [Bool.not_eq_true] at hc
    refine (ite_within_false (p := fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc (lift_within (Stepped.const_runs (0 : ℤ) _))).mono ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos hg hg) (Nat.succ_pos _)
    · have : size (0 : ℤ) = 1 := rfl
      omega

/-- **The procedure for Ψ_{a,a'}.** -/
theorem rowPair_within (hPP : PairIsProduct) (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    (hy : y < #(D.fam lam).I ^ nRectG g g) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool} (hz : z ∈ (patternNet D c g tr lam y W).S a) (hz' : z' ∈ (patternNet D c g tr lam y W).S b) :
    rowPair.Within (upOracle D g lam Lam W) (upPrices c tq) (p, ((a.val, b.val), (z, z'))) (g * g * (askCost c lam + 1))
      (2 * size (p, ((a.val, b.val), (z, z'))) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9) ((patternNet D c g tr lam y W).Ψ a b z z') := by
  rw [pair_eq hPP hS hg hlam hy hab hz hz', rowPair_eq]
  have hl := (mem_S_iff a z).1 hz
  have hl' := (mem_S_iff b z').1 hz'
  have hs : size (p, ordered ((a.val, b.val), (z, z'))) = size (p, ((a.val, b.val), (z, z'))) := congrArg (size p + ·) (size_ordered _)
  rw [← hs]
  refine mapIn_within (pairLoop_within hLA hG hL hT hY hLs hS (by omega) hlam hLam ?_ ?_ ?_ ?_)
  all_goals
    unfold ordered
    split_ifs
    all_goals first | exact a.2 | exact b.2 | exact hl | exact hl'

end ExplicitCost
