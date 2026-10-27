/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.GridLemmas
public import ClauseBound.Alg.GridPresents
public import StepMachines.Prog.SidePresents
public import Groundwork.Grid.RowNet
import Mathlib.Tactic

/-! # Ψ_{a,a'} is the product that the procedure computes

Proof of Proposition 3, the two networks for each ι: Ψ_{a,a'} is the product of the factors of the g
straight edges between rows a and a' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2
rectangles q with these two rows. The Ψ of `patternNet` is the sum that the factorization defines.
Here:
* `cutsOK_piecesOf`: the pieces, in the form `piecesOf D c`, factor as the grid of this development
  asks (`ClauseBound.Alg.GridNet.CutsOK`), for the functions A_i themselves;
* `pairIsProduct : PairIsProduct`: so, by `Groundwork.Grid.rowNet_Ψ` and
  `Groundwork.Network.Ψ_pull`, Ψ is the product, in the form in which `rowPair` computes it. This is
  the same statement as `Eight.ViaGrouping.psiLt_row` and `psiLt_col`, here for general pieces. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The pieces factor as the grid of this development asks. -/
theorem cutsOK_piecesOf {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) (pad : U) :
    CutsOK (piecesOf D c) pad 0 lam fun j => (D.fam lam).A (indexAt D lam j) where
  cnt_pos := card_I_pos hS.is hlam
  m_pos := le_rfl
  factors := fun tr i hi x y u v => by
    have hm := indexAt_mem D lam hi
    cases tr
    · refine (hS.is.row lam hlam _ hm x y u v).trans (Finset.sum_congr rfl fun θ hθ => ?_)
      have hl : θ.length = D.cap lam false (indexAt D lam i) := mem_words.1 hθ
      change _ = (piecesOf D c).top ((pad, false), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) * (piecesOf D c).bot ((pad, false), (0, i), (ClauseBound.Alg.bitsOf u, ClauseBound.Alg.bitsOf v, θ))
      rw [top_piecesOf, bot_piecesOf, if_pos hl, if_pos hl]
    · refine (hS.is.col lam hlam _ hm x u y v).trans (Finset.sum_congr rfl fun θ hθ => ?_)
      have hl : θ.length = D.cap lam true (indexAt D lam i) := mem_words.1 hθ
      change _ = (piecesOf D c).top ((pad, true), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) * (piecesOf D c).bot ((pad, true), (0, i), (ClauseBound.Alg.bitsOf u, ClauseBound.Alg.bitsOf v, θ))
      rw [top_piecesOf, bot_piecesOf, if_pos hl, if_pos hl]
  cap_le := fun tr i _ => by
    change D.cap lam tr (indexAt D lam i) ≤ 2 * 1 * lam
    have := hS.short lam tr (indexAt D lam i)
    omega
  abs_A := fun i hi x y u v => (hS.is.size_A lam hlam _ (indexAt_mem D lam hi) x y u v).le
  abs_top := fun tr i hi x y θ => by
    change |(piecesOf D c).top ((pad, tr), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ))| ≤ _
    rw [top_piecesOf]
    by_cases hθ : θ.length = D.cap lam tr (indexAt D lam i)
    · rw [if_pos hθ]
      exact (hS.is.size_f lam hlam _ (indexAt_mem D lam hi) tr false (x, y) θ (mem_words.2 hθ)).le
    · rw [if_neg hθ, abs_zero]
      positivity
  abs_bot := fun tr i hi x y θ => by
    change |(piecesOf D c).bot ((pad, tr), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ))| ≤ _
    rw [bot_piecesOf]
    by_cases hθ : θ.length = D.cap lam tr (indexAt D lam i)
    · rw [if_pos hθ]
      exact (hS.is.size_f lam hlam _ (indexAt_mem D lam hi) tr true (x, y) θ (mem_words.2 hθ)).le
    · rw [if_neg hθ, abs_zero]
      positivity

/-- The test and the loop of `rowPair` written as products: over the g straight edges, and over the
pairs i < i'. -/
theorem test_and_loop (g : ℕ) (tr : Bool) (lam : ℕ) (q : PsiQ) (F : ℕ → ℕ → ℤ) :
    (if straightOK g tr lam q = true then ∏ j ∈ range (g * g), (if j / g < j % g then F (j / g) (j % g) else 1) else 0) =
      (∏ i : Fin g, if heG g g lam q.2.1 i (nodeG g tr q.1.2 i) = heG g g lam q.2.2 i (nodeG g tr q.1.1 i) then 1 else 0) * ∏ k : Fin g × Fin g with k.1 < k.2, F k.1 k.2 := by
  have h1 : ∏ i : Fin g, (if heG g g lam q.2.1 i (nodeG g tr q.1.2 i) = heG g g lam q.2.2 i (nodeG g tr q.1.1 i) then (1 : ℤ) else 0) = if straightOK g tr lam q = true then 1 else 0 := by
    unfold straightOK
    rw [← prod_ind_range]
    simp only [beq_iff_eq]
  rw [h1, ← prod_counter_pairs g F]
  by_cases h : straightOK g tr lam q = true
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- Ψ_{a,a'} of the row network, for a < a'. -/
theorem pair_row {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    (gridN (piecesOf D c) [()] g g false 0 lam y Rm).Ψ a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g false b i) = heG g g lam z' i (nodeG g false a i) then 1 else 0) *
        ∏ k : Fin g × Fin g with k.1 < k.2, pieceValue D lam (indexAt D lam (digG (piecesOf D c) g false 0 lam y (tri a.val b.val) (tri k.1 k.2))) (rectStrings g false lam ((a.val, b.val), (z, z')) k.1 k.2) := by
  have hC := cutsOK_piecesOf hS hlam [()]
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g false o i)).length = lam := fun w hw o x i =>
    length_heG (tr := false) hw x.2 (nodeG_lt (p := g) false o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g false lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g false w'.1 w'.2)) :=
    fun w x w' => stC_dec g g false lam w x w'
  refine (Network.Ψ_pull (gridNet (piecesOf D c) [()] g g false 0 lam y (gridR g g false lam Rm)) _ _ _ a b z z').trans ?_
  refine (rowNet_Ψ (fun ω => hC.factors false _ (digG_lt hC.cnt_pos g false y _ _)) _ _ _ hab _ _).trans ?_
  unfold rowΨ
  congr 1
  refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
  exact ⟨fun e => (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).1 ((hd z i (b, i)).symm.trans (e.trans (hd z' i (a, i)))),
    fun e => (hd z i (b, i)).trans (((bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).2 e).trans (hd z' i (a, i)).symm)⟩

/-- Ψ_{j,j'} of the column network, for j < j'. -/
theorem pair_col {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    (gridN (piecesOf D c) [()] g g true 0 lam y Rm).Ψ a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g true b i) = heG g g lam z' i (nodeG g true a i) then 1 else 0) *
        ∏ k : Fin g × Fin g with k.1 < k.2, pieceValue D lam (indexAt D lam (digG (piecesOf D c) g true 0 lam y (tri a.val b.val) (tri k.1 k.2))) (rectStrings g true lam ((a.val, b.val), (z, z')) k.1 k.2) := by
  have hC := cutsOK_piecesOf hS hlam [()]
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g true o i)).length = lam := fun w hw o x i =>
    length_heG (tr := true) hw x.2 (nodeG_lt (p := g) true o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g true lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g true w'.1 w'.2)) :=
    fun w x w' => stC_dec g g true lam w x w'
  refine (Network.Ψ_pull (gridNet (piecesOf D c) [()] g g true 0 lam y (gridR g g true lam Rm)) _ _ _ a b z z').trans ?_
  refine (rowNet_Ψ (fun ω => hC.factors true _ (digG_lt hC.cnt_pos g true y _ _)) _ _ _ hab _ _).trans ?_
  unfold rowΨ
  congr 1
  refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
  exact ⟨fun e => (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).1 ((hd z i (b, i)).symm.trans (e.trans (hd z' i (a, i)))),
    fun e => (hd z i (b, i)).trans (((bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).2 e).trans (hd z' i (a, i)).symm)⟩

/-- **Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows.** -/
theorem pairIsProduct : PairIsProduct := by
  intro ρ c x₀ D hS g lam y tr W _ hlam _ a b hab z hz z' hz'
  rw [test_and_loop g tr lam ((a.val, b.val), (z, z')) fun i i' => pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri a.val b.val) (tri i i'))) (rectStrings g tr lam ((a.val, b.val), (z, z')) i i')]
  cases tr
  · exact pair_row hS hlam y _ hab (mem_words.1 hz) (mem_words.1 hz')
  · exact pair_col hS hlam y _ hab (mem_words.1 hz) (mem_words.1 hz')

end ExplicitCost
