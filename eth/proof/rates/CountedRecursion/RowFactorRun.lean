/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RowPairRun
import Mathlib.Tactic

/-! # The procedure for f_{a,a'}

`rowFactor_within`: on a setting z of the row a and a string θ of c_{a,a'} bits, the procedure
`rowFactor` returns f_{a,a'}(z, θ) of the network of the pattern within g²·(2^{cλ} + 3) operations:
the first gλ bits of θ are compared with the strings of z on the straight edges, and each rectangle
gives one query to the pieces, for the function of the first pair of strings if a < a' and of the
second if a > a', at the chunk of θ that belongs to the rectangle
(proof of Proposition 3: by the observations after Definition 1 and the first factorization in Lemma
2 (b), Ψ_{a,a'} factors through c_{a,a'} bits). It asks the pieces only about strings of λ bits. The
bound on the states is explicit. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-- The function of the first pair of strings, in the form of `piecesOf`, at strings given as lists. -/
theorem top_lists (D : PiecesCounted.Data) (c : ℕ) (pad : U) (tr : Bool) (h j : ℕ) {s₁ s₂ θ : List Bool} (h1 : s₁.length = lam) :
    (piecesOf D c).top ((pad, tr), (h, j), (s₁, s₂, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr false (indexAt D lam j) (PiecesCounted.toBits lam s₁, PiecesCounted.toBits lam s₂) θ else 0 := by
  subst h1
  rfl

/-- The function of the second pair of strings. -/
theorem bot_lists (D : PiecesCounted.Data) (c : ℕ) (pad : U) (tr : Bool) (h j : ℕ) {s₁ s₂ θ : List Bool} (h1 : s₁.length = lam) :
    (piecesOf D c).bot ((pad, tr), (h, j), (s₁, s₂, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr true (indexAt D lam j) (PiecesCounted.toBits lam s₁, PiecesCounted.toBits lam s₂) θ else 0 := by
  subst h1
  rfl

/-- The pieces answer the question for a function of a factorization. -/
theorem pieces_factor {i : ℤ} (hi : i ∈ (D.fam lam).I) (tr side : Bool) {s₁ s₂ θ : List Bool} (h1 : s₁.length = lam) (h2 : s₂.length = lam) (h3 : θ.length = D.cap lam tr i)
    (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) {u : List Unit} (hu : u.length = lam) :
    piecesUpTo D Lam (u, .inr (.inr (.inr (.inr ((tr, side), i, (s₁, s₂, θ)))))) = some (Sum.inl (D.fn lam tr side i (PiecesCounted.toBits lam s₁, PiecesCounted.toBits lam s₂) θ)) := by
  subst hu
  change (if u.length ≤ Lam then (if 1 ≤ u.length then
    (if i ∈ (D.fam u.length).I ∧ s₁.length = u.length ∧ s₂.length = u.length ∧ θ.length = D.cap u.length tr i then
      some (Sum.inl (D.fn u.length tr side i (PiecesCounted.toBits u.length s₁, PiecesCounted.toBits u.length s₂) θ)) else none) else none) else none) = _
  rw [if_pos hLam, if_pos hlam, if_pos ⟨hi, h1, h2, h3⟩]

/-- The place in 𝓘 of the piece of the rectangle with the columns j / g < j % g. -/
def factorDigit (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : FQ) (j : ℕ) : ℕ := digG (piecesOf D c) g tr 0 lam y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / g) (j % g))

/-- The chunk of θ that belongs to that rectangle. -/
def factorChunk (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : FQ) (j : ℕ) : List Bool :=
  chunkAt (lenG (piecesOf D c) g tr 0 lam y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri (j / g) (j % g)) (q.2.2.drop (g * lam))

/-- The factor number j of the loop. -/
def factorItem (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : FQ) (j : ℕ) : ℤ :=
  if j / g < j % g then D.fn lam tr (!decide (q.1.1 < q.1.2)) (indexAt D lam (factorDigit D c g tr lam y q j))
    (PiecesCounted.toBits lam (heG g g lam q.2.1 (j / g) (nodeG g tr q.1.2 (j % g))), PiecesCounted.toBits lam (heG g g lam q.2.1 (j % g) (nodeG g tr q.1.2 (j / g)))) (factorChunk D c g tr lam y q j)
  else 1

/-- The chunk of a rectangle has as many bits as its piece asks. -/
theorem length_factorChunk {q : FQ} (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) {j : ℕ} (hlt : j / g < j % g) (hg : 0 < g) :
    (factorChunk D c g tr lam y q j).length = D.cap lam tr (indexAt D lam (factorDigit D c g tr lam y q j)) := by
  unfold factorChunk
  refine length_chunkAt _ (r := c2 g) (tri_lt hlt (Nat.mod_lt _ hg)) ?_
  unfold capG at hθ
  rw [nMemb_self] at hθ
  rw [List.length_drop, hθ]
  omega

/-- It is below 2^{(2λ)^c} in absolute value. -/
theorem abs_factorItem_lt (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (hg : 0 < g) {q : FQ} (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) (j : ℕ) : |factorItem D c g tr lam y q j| < 2 ^ (2 * lam) ^ c := by
  unfold factorItem
  split_ifs with hlt
  · exact hS.is.size_f lam hlam _ (dig_mem hS hlam g tr y _ _) _ _ _ _ (mem_words.2 (length_factorChunk hθ hlt hg))
  · rw [abs_one]
    exact one_lt_pow₀ (by norm_num) (by positivity)

/-- `ClauseBound.Alg.gridFf` for the pieces, as the check and the loop of `rowFactor`. -/
theorem gridFf_items (hg : 0 < g) {q : FQ} (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) :
    gridFf (piecesOf D c) [()] g g tr 0 lam y q = if labelOK g tr lam q = true then ∏ j ∈ range (g * g), factorItem D c g tr lam y q j else 0 := by
  unfold gridFf
  change (bif labelOK g tr lam q then _ else 0) = _
  by_cases hc : labelOK g tr lam q = true
  swap
  · rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl
  · rw [hc, cond_true, if_pos rfl, prodL_eq]
    simp only [nMemb_self]
    refine Finset.prod_congr rfl fun j hj => ?_
    unfold factorItem
    by_cases hlt : j / g < j % g
    · rw [if_pos hlt, if_pos hlt]
      have hi : j / g < nMemb g g tr := by rw [nMemb_self]; exact Nat.div_lt_of_lt_mul (Finset.mem_range.1 hj)
      have hi' : j % g < nMemb g g tr := by rw [nMemb_self]; exact Nat.mod_lt _ hg
      have l1 : (heG g g lam q.2.1 (j / g) (nodeG g tr q.1.2 (j % g))).length = lam := length_heG hz hi (nodeG_lt tr hb hi')
      have l3 := length_factorChunk hθ hlt hg
      by_cases hab : q.1.1 < q.1.2
      · rw [if_pos hab, top_lists D c _ tr 0 _ l1]
        exact (if_pos l3).trans (by rw [decide_eq_true hab]; rfl)
      · rw [if_neg hab, bot_lists D c _ tr 0 _ l1]
        exact (if_pos l3).trans (by rw [decide_eq_false hab]; rfl)
    · rw [if_neg hlt, if_neg hlt]

/-- **The procedure for f_{a,a'}.** -/
theorem rowFactor_within (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) :
    rowFactor.Within (upOracle D g lam Lam W) (upPrices c tq) (p, ((a.val, b.val), (z, θ))) (g * g * (askCost c lam + 1))
      (2 * size (p, ((a.val, b.val), (z, θ))) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9) ((patternNet D c g tr lam y W).f a b z θ) := by
  rw [factor_eq hab hz hθ, gridFf_items (q := ((a.val, b.val), (z, θ))) hg b.2 hz hθ]
  subst hG hL hT hY
  obtain ⟨q, hq⟩ : ∃ q : FQ, q = ((a.val, b.val), (z, θ)) := ⟨_, rfl⟩
  have hb : q.1.2 < nParts (pG p) (pG p) (pTr p) := by rw [hq]; exact b.2
  have hz' : q.2.1.length = nMemb (pG p) (pG p) (pTr p) * (pG p * pG p) * pLam p := by rw [hq]; exact hz
  have hθ' : q.2.2.length = capG (piecesOf D c) (pG p) (pG p) (pTr p) 0 (pLam p) (pY p) q.1.1 q.1.2 := by rw [hq]; exact hθ
  rw [← hq]
  by_cases hc : labelOK (pG p) (pTr p) (pLam p) q = true
  · rw [if_pos hc]
    have hbody : ∀ j < pG p * pG p, (QueryMachine.ite (fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × FQ) × ℕ => (Sum.inr (factorQuestion v) : UpQuery)) (QueryMachine.const 1)).Within
        (upOracle D (pG p) (pLam p) Lam W) (upPrices c tq) ((p, q), j) (askCost c (pLam p)) (size (p, q) + size (pG p * pG p) + (2 * pLam p) ^ c + 4) (factorItem D c (pG p) (pTr p) (pLam p) (pY p) q j) := by
      intro j hj
      have s2 := size_lt_le hj
      have s3 : size ((p, q), j) = size (p, q) + size j := rfl
      have hi : j / pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.div_lt_of_lt_mul hj
      have hi' : j % pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.mod_lt _ hg
      by_cases hlt : j / pG p < j % pG p
      · have l1 : (heG (pG p) (pG p) (pLam p) q.2.1 (j / pG p) (nodeG (pG p) (pTr p) q.1.2 (j % pG p))).length = pLam p := length_heG hz' hi (nodeG_lt _ hb hi')
        have l2 : (heG (pG p) (pG p) (pLam p) q.2.1 (j % pG p) (nodeG (pG p) (pTr p) q.1.2 (j / pG p))).length = pLam p := length_heG hz' hi' (nodeG_lt _ hb hi)
        have l3 := length_factorChunk hθ' hlt hg
        have hidx : pieceAt p (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / pG p) (j % pG p)) = indexAt D (pLam p) (factorDigit D c (pG p) (pTr p) (pLam p) (pY p) q j) := by
          unfold pieceAt factorDigit
          rw [hLs, digG_ofLists hLA hS hlam]
          rfl
        have hlen : lenG (listsAsPieces (pLists p)) (pG p) (pTr p) 0 (pLam p) (pY p) (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) = lenG (piecesOf D c) (pG p) (pTr p) 0 (pLam p) (pY p) (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) := by
          funext κ
          rw [hLs, lenG_ofLists hLA hS hlam]
        have hv : upOracle D (pG p) (pLam p) Lam W (Sum.inr (factorQuestion ((p, q), j))) = some (Sum.inl (factorItem D c (pG p) (pTr p) (pLam p) (pY p) q j)) := by
          unfold factorItem
          rw [if_pos hlt]
          change piecesUpTo D Lam (p.2.1.1, .inr (.inr (.inr (.inr ((pTr p, !decide (q.1.1 < q.1.2)), pieceAt p (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / pG p) (j % pG p)),
            (heG (pG p) (pG p) (pLam p) q.2.1 (j / pG p) (nodeG (pG p) (pTr p) q.1.2 (j % pG p)), heG (pG p) (pG p) (pLam p) q.2.1 (j % pG p) (nodeG (pG p) (pTr p) q.1.2 (j / pG p)),
              chunkAt (lenG (listsAsPieces (pLists p)) (pG p) (pTr p) 0 (pLam p) (pY p) (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri (j / pG p) (j % pG p)) (q.2.2.drop (pG p * pLam p)))))))) = _
          rw [hidx, hlen]
          exact pieces_factor (dig_mem hS hlam _ _ _ _ _) _ _ l1 l2 l3 hlam hLam rfl
        have hq' := query_within (A := Ans) (h := fun v : (Parent × FQ) × ℕ => (Sum.inr (factorQuestion v) : UpQuery)) (w := upPrices c tq) (a := ((p, q), j)) hv
        refine (ite_within_true (p := fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_true hlt) (mapOut_within (g := asInt) hq')).mono le_rfl ?_
        have s1 := size_answer (abs_factorItem_lt hS hlam hg hθ' j)
        omega
      · have e : factorItem D c (pG p) (pTr p) (pLam p) (pY p) q j = 1 := if_neg hlt
        rw [e]
        refine (ite_within_false (p := fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_false hlt) (lift_within (Stepped.const_runs (1 : ℤ) _))).mono ?_ ?_
        · unfold askCost
          omega
        · have : size (1 : ℤ) = 2 := rfl
          omega
    have hprod := prodRange_within (N := fun x : Parent × FQ => pG x.1 * pG x.1) (a := (p, q)) (fun _ => askCost c (pLam p)) (factorItem D c (pG p) (pTr p) (pLam p) (pY p) q) (2 ^ (2 * pLam p) ^ c) _ Nat.one_le_two_pow hbody
      fun j _ => Table.natAbs_le (abs_factorItem_lt hS hlam hg hθ' j).le
    dsimp only at hprod
    refine (ite_within_true (p := fun x : Parent × FQ => labelOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc hprod).mono (le_of_eq ?_) ?_
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    · have := size_two_pow_pow ((2 * pLam p) ^ c) (pG p * pG p)
      omega
  · rw [if_neg hc]
    rw [Bool.not_eq_true] at hc
    refine (ite_within_false (p := fun x : Parent × FQ => labelOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc (lift_within (Stepped.const_runs (0 : ℤ) _))).mono ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos hg hg) (Nat.succ_pos _)
    · have : size (0 : ℤ) = 1 := rfl
      omega

end ExplicitCost
