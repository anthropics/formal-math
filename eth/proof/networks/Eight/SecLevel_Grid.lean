/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecLevel_GridDefs
public import Eight.SecCrossing_LemPieces
public import SingleBitPieces.Level.Pieces
import Mathlib.Tactic

/-! # Section 5 «One level of the recursion», the mathematics of one level: the grid, and displays (34) and (36)

The part of the proof of Proposition 3 that is pure mathematics (finite sums and counting, no
algorithm), for the functions A_0, …, A_t, t = ⌈λ/3⌉, of Lemma 2 (`Eight.A`), in the form and with
the constants of the paper. The definitions are in
proof/networks/Eight/SecLevel_GridDefs.lean.

* the functions ι : ℛ → {0, …, t}: `patterns`;
* the expansion (34), with the factor 2^{t|ℛ|}: `Zι`, `eqExpansion`;
* the row network and the column network of a term Z_ι, made with the factorizations `Eight.fTop`,
  `Eight.fBot` of the proof of Lemma 2(b) (`rowCut_factors`, `colCut_factors`): `rowNetwork`,
  `colNetwork`; their edge functions written out: `rowNetwork_Ψ`, `colNetwork_Ψ`;
  their values: `value_rowNetwork`, `value_colNetwork`;
* conditions (i) and (ii) of Definition 2 for both networks, with P = g³λ and all values at most
  2^{gB + g²t} (the paper has below 2^{B₁}, B₁ = gB + g²λ + 1): `rowNetwork_sized_t`,
  `colNetwork_sized_t`;
* the two totals and the smaller total (36): `U_rowNetwork`, `U_colNetwork`, `eqMinTotal_chain`,
  `eqMinTotal`.

The grid, its rectangles and their number (`Paper.rectangles`, `Paper.card_rectangles`,
`Paper.card_rectangles_le`), the four strings of a rectangle and Definition 1
(`Paper.FactorsThrough`) do not depend on the pieces and are taken from
proof/networks/Paper/SecLevel_Grid.lean and proof/networks/Paper/SecNetworks_DefFactor.lean; the sum
over a grid and the network of merged rows, for any functions at the rectangles and any
factorizations of them, are in proof/networks/Groundwork/ (`Groundwork.Grid.ZG`,
`Groundwork.Grid.rowNet`).
λ is written `lam`; a string of λ bits has the type `Bits lam` (= `Fin lam → Bool`); rows and
columns are numbered by `Fin g`. Lemma 2 speaks of λ ≥ 1 and i ≤ t, so the statements that use it
have the hypotheses `1 ≤ lam` and `∀ q, ι q ≤ tOf lam`;
every ι of display (34) satisfies the second one.
The networks that Algorithm 1 runs are these networks with settings and indices written as words:
see proof/networks/Eight/SecLevel_GridWords.lean. -/

public section

namespace Eight

open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)

variable {g lam : ℕ}

/-! ## The expansion (34) -/

/-- **Display (34) of the paper**: 2^{t|ℛ|} · Z = ∑_ι Z_ι, the sum over all ι : ℛ → {0, …, t}.
«Multiply Z by 2^{t|ℛ|}, apply Lemma 2(a) to every rectangle, and expand.»
Here Z = `W.Z d` is the value of the clique with tables W on a node set J with g² elements, with one
string per edge: Z = ∑ over all choices of one string per edge of ∏_w W_w(the strings on the edges
at w).
Different from the paper: the nodes are identified with the grid points by an arbitrary bijection e;
a table W_w is a function of one string for every node w', where the entry at w' = w is a dummy that
is always the fixed string d
(`Grid.onGrid` carries the tables to the grid and makes them 0 unless the dummy entry is d). -/
theorem eqExpansion {J : Type} [Fintype J] [LinearOrder J] (hlam : 1 ≤ lam) (W : Inst J (Bits lam)) (d : Bits lam) (e : J ≃ Fin g × Fin g) :
    2 ^ (tOf lam * #(rectangles g)) * W.Z d = ∑ ι ∈ patterns g lam, Zι (Grid.onGrid W d e) ι := by
  rw [pow_mul]
  exact ClauseBound.Grid.Z_mul_eq_sum W d e (range (tOf lam + 1)) 0 (fun i => A lam i) (2 ^ tOf lam) fun x y u v => by
    rw [lemPieces.a_sum lam hlam, ClauseBound.Alg.GridNet.cross_eq]

/-! ## The two networks of a term Z_ι -/

/-- Lemma 2(b), first factorization. -/
theorem rowCut_factors (hlam : 1 ≤ lam) {i : ℕ} (hi : i ≤ tOf lam) : (rowCut lam i).Factors (A lam i) := fun x y u v =>
  ((stFact lam hlam i hi).1 x y u v).trans
    (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (false, i, List.ofFn x, List.ofFn y, θ) * fBot (false, i, List.ofFn u, List.ofFn v, θ))

/-- Lemma 2(b), second factorization. -/
theorem colCut_factors (hlam : 1 ≤ lam) {i : ℕ} (hi : i ≤ tOf lam) : (colCut lam i).Factors fun x u y v => A lam i x y u v := fun x u y v =>
  ((stFact lam hlam i hi).2.1 x y u v).trans
    (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (true, i, List.ofFn x, List.ofFn u, θ) * fBot (true, i, List.ofFn y, List.ofFn v, θ))

/-- «Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows.» Same as in the
paper. -/
theorem rowNetwork_Ψ (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) {a a' : Fin g} (h : a < a')
    (z z' : RowSetting g lam) :
    (rowNetwork W ι).Ψ a a' z z' = (∏ j, if z j (a', j) = z' j (a, j) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        A lam (ι ((a, a'), k)) (z k.1 (a', k.2)) (z k.2 (a', k.1)) (z' k.1 (a, k.2)) (z' k.2 (a, k.1)) :=
  Grid.rowNet_Ψ (fun q => rowCut_factors hlam (hι q)) W _ lam h z z'

/-- Ψ_{j,j'} in the column network: the product of the factors of the g straight edges between
columns j and j' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the rectangles q with these two columns.
«There x_q, u_q and y_q, v_q are separated.» -/
theorem colNetwork_Ψ (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) {j j' : Fin g} (h : j < j')
    (z z' : RowSetting g lam) :
    (colNetwork W ι).Ψ j j' z z' = (∏ a, if z a (j', a) = z' a (j, a) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        A lam (ι (k, (j, j'))) (z k.1 (j', k.2)) (z' k.1 (j, k.2)) (z k.2 (j', k.1)) (z' k.2 (j, k.1)) :=
  Grid.rowNet_Ψ (G := fun q x u y v => A lam (ι (q.2, q.1)) x y u v) (fun _ => colCut_factors hlam (hι _)) (Grid.trInst W) _ lam h z z'

/-- «Each factor in (34) is used exactly once, so the value is Z_ι»: the row network. Same as in the
paper. -/
theorem value_rowNetwork (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) :
    (rowNetwork W ι).value = Zι W ι :=
  Grid.value_rowNet (fun q => rowCut_factors hlam (hι q)) W _ lam

/-- The column network has the value Z_ι too. Same as in the paper. -/
theorem value_colNetwork (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) :
    (colNetwork W ι).value = Zι W ι :=
  ClauseBound.Grid.value_rowNet_tr (G := fun q => A lam (ι q)) (fun _ => colCut_factors hlam (hι _)) W _ lam

/-! ## Definition 2 for the two networks: P = g³λ, and all values at most 2^{gB + g²t} -/

/-- «Indeed ∑_{a' ≠ a} c_{a,a'} ≤ g³λ, |W_a| < 2^{gB}, and Ψ_{a,a'} and the functions of its
factorization are products of indicators and of g(g−1)/2 numbers of absolute value at most 2^t»: the
row network, with the bound 2^{gB + g²t} for all
values; the paper then uses 2^t ≤ 2^λ. Different from the paper: values «at most 2^{gB + g²t}» where
the paper has «below 2^{B₁}», B₁ = gB + g²λ + 1, and tables with |W_w| ≤ 2^B where the paper has <
2^B. -/
theorem rowNetwork_sized_t {B : ℕ} (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) (hW : ∀ w h, |W w h| ≤ 2 ^ B) {ι : Rectangle g → ℕ}
    (hι : ∀ q, ι q ≤ tOf lam) : (rowNetwork W ι).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by
  have h := Grid.rowNet_sized' (L := lam) (m := 1) (b := tOf lam) le_rfl (Fintype.card_fin g) (Fintype.card_fin g) (by simp) W hW (fun q => rowCut lam (ι q)) []
    (fun q => rowCut_factors hlam (hι q)) (fun _ => (card_words _).le) (fun _ => by rw [Nat.mul_one]; exact min_le_left _ _)
    (fun q x y θ => ((stFact lam hlam _ (hι q)).2.2 false x y θ).1) (fun q u v θ => ((stFact lam hlam _ (hι q)).2.2 false u v θ).2)
    fun q x y u v => lemPieces.a_abs lam _ hlam (hι q) x y u v
  rwa [Nat.one_mul] at h

/-- The same for the column network. -/
theorem colNetwork_sized_t {B : ℕ} (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) (hW : ∀ w h, |W w h| ≤ 2 ^ B) {ι : Rectangle g → ℕ}
    (hι : ∀ q, ι q ≤ tOf lam) : (colNetwork W ι).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by
  have h := Grid.rowNet_sized' (L := lam) (m := 1) (b := tOf lam) le_rfl (Fintype.card_fin g) (Fintype.card_fin g) (by simp) (Grid.trInst W) (fun _ _ => hW _ _)
    (G := fun q x u y v => A lam (ι (q.2, q.1)) x y u v) (fun q => colCut lam (ι (q.2, q.1))) []
    (fun _ => colCut_factors hlam (hι _)) (fun _ => (card_words _).le) (fun _ => by rw [Nat.mul_one]; exact min_le_left _ _)
    (fun _ x u θ => ((stFact lam hlam _ (hι _)).2.2 true x u θ).1) (fun _ y v θ => ((stFact lam hlam _ (hι _)).2.2 true y v θ).2)
    fun _ x u y v => lemPieces.a_abs lam _ hlam (hι _) x y u v
  rwa [Nat.one_mul] at h

/-! ## The smaller total (36) -/

/-- «U_row = g²(g−1)λ + 2 ∑_{q ∈ ℛ} c^row_{ι(q)}», «because U counts ordered pairs». Same as in the
paper. -/
theorem U_rowNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    (rowNetwork W ι).U = g ^ 2 * (g - 1) * lam + 2 * ∑ q ∈ rectangles g, crow lam (ι q) :=
  Grid.U_rowNet (Fintype.card_fin g) (Fintype.card_fin g) W _ _

/-- «U_col = g²(g−1)λ + 2 ∑_{q ∈ ℛ} c^col_{ι(q)}». Same as in the paper. -/
theorem U_colNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    (colNetwork W ι).U = g ^ 2 * (g - 1) * lam + 2 * ∑ q ∈ rectangles g, ccol lam (ι q) := by
  rw [rectangles, ← Grid.sum_Ω_swap fun q => ccol lam (ι q)]
  exact Grid.U_rowNet (Fintype.card_fin g) (Fintype.card_fin g) _ _ _

/-- **Display (36) of the paper**, all three inequalities: min(U_row, U_col) ≤ ½(U_row + U_col) ≤
N/g + |ℛ|(11λ/3 + 8) ≤ N(ρ + 1/g) + 2g⁴, where N = g⁴λ and ρ = 11/12. The second one is Lemma 2(c),
the third one |ℛ| ≤ g⁴/4.
Same as in the paper (N/g is written g³λ, so that g = 0 needs no exception). -/
theorem eqMinTotal_chain (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) :
    ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ (((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U) / 2 ∧
      (((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U) / 2 ≤ (g : ℝ) ^ 3 * lam + #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) ∧
      (g : ℝ) ^ 3 * lam + #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : 2 * min (rowNetwork W ι).U (colNetwork W ι).U ≤ (rowNetwork W ι).U + (colNetwork W ι).U := by omega
    have h' : 2 * ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ ((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U := by exact_mod_cast h
    linarith
  · have h0 : g ^ 2 * (g - 1) * lam ≤ g ^ 3 * lam :=
      Nat.mul_le_mul_right _ (by
        calc g ^ 2 * (g - 1) ≤ g ^ 2 * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = g ^ 3 := by ring)
    have h1 : (rowNetwork W ι).U + (colNetwork W ι).U ≤ 2 * (g ^ 3 * lam) + 2 * ∑ q ∈ rectangles g, (crow lam (ι q) + ccol lam (ι q)) := by
      rw [U_rowNetwork, U_colNetwork, Finset.sum_add_distrib]
      omega
    have h1' : ((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U ≤
        2 * ((g : ℝ) ^ 3 * lam) + 2 * ∑ q ∈ rectangles g, ((crow lam (ι q) + ccol lam (ι q) : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : ∑ q ∈ rectangles g, ((crow lam (ι q) + ccol lam (ι q) : ℕ) : ℝ) ≤ #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) := by
      -- «By Lemma 2(c), c^row_i + c^col_i ≤ 11λ/3 + 8»
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun q _ => (lemPieces.c_sum lam _ hlam (hι q)).trans_eq ?_
      unfold rho
      ring
    linarith
  · have h5 := card_rectangles_le g
    have hpos : (0 : ℝ) ≤ 11 * (lam : ℝ) / 3 + 8 := by positivity
    have h6 := mul_le_mul_of_nonneg_right h5 hpos
    unfold rho
    linarith

/-- **Display (36) of the paper**, its two ends: min(U_row, U_col) ≤ N(ρ + 1/g) + 2g⁴. Same as in
the paper. -/
theorem eqMinTotal (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) :
    ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 :=
  have h := eqMinTotal_chain hlam W hι
  h.1.trans (h.2.1.trans h.2.2)

end Eight
