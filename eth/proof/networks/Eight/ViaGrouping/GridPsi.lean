/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.GridPsiDefs
public import Eight.ViaGrouping.LevelDefs
public import Eight.SecLevel_GridWords
public import Eight.SecCrossing_Cert
public import Eight.Level.Presents
public import Eight.Level.Cert
import Mathlib.Tactic

/-! # Ψ_{a,a'} in the two networks of Proposition 3, as a program: proofs

The program `gridPsi` of proof/networks/Eight/ViaGrouping/GridPsiDefs.lean renders the sentence
«Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows»
(proof of Proposition 3, «Two networks for each ι») on settings written as words. Here:
* `gridPsi_eq`, `stGridPsi`: it computes Ψ of the network that Algorithm 1 runs
  (`Eight.Level.netOfι`). That network is the row network or the column network of the proof with
  settings written as words (`netOfι_row`, `netOfι_col`), whose Ψ, defined as the sum
  ∑_θ f_{a,a'}·f_{a',a}, is the product of the sentence by `Eight.rowNetwork_Ψ` and
  `Eight.colNetwork_Ψ`; the program `aMul` computes A_i (`Eight.stAMul`).
* `gridPsi_polyT`, `stGridPsiPoly`: it is polynomial-time («computable in time poly(λ)», Lemma 2(a),
  for each of the at most g² factors). -/

public section

namespace Eight.ViaGrouping

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level

/-! ## The program as a product -/

/-- The loop and the test of `psiLt` written as products: over the g straight edges, and over the
pairs i < i'. -/
theorem psiLt_eq (g : ℕ) (tr : Bool) (lam y a b : ℕ) (z z' : List Bool) :
    psiLt g tr lam y a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g tr b i) = heG g g lam z' i (nodeG g tr a i) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2, rectPsi g tr lam y a b z z' k.1 k.2 := by
  have h1 : ∏ i : Fin g, (if heG g g lam z i (nodeG g tr b i) = heG g g lam z' i (nodeG g tr a i) then (1 : ℤ) else 0) =
      if ((List.range g).all fun i => heG g g lam z i (nodeG g tr b i) == heG g g lam z' i (nodeG g tr a i)) = true then 1 else 0 := by
    rw [← prod_ind_range]
    simp only [beq_iff_eq]
  rw [h1, ← prod_counter_pairs g fun i i' => rectPsi g tr lam y a b z z' i i']
  unfold psiLt
  simp only [prodL_eq]
  cases (List.range g).all fun i => heG g g lam z i (nodeG g tr b i) == heG g g lam z' i (nodeG g tr a i) with
  | false => simp
  | true => simp

/-- The program of the proof of Lemma 2(a) computes A_i at four words of λ bits. -/
theorem A_bitsOf {lam : ℕ} (i : ℕ) {X Y U V : List Bool} (hX : X.length = lam) (hY : Y.length = lam) (hU : U.length = lam) (hV : V.length = lam) :
    A lam i (Grid.bitsOf lam X) (Grid.bitsOf lam Y) (Grid.bitsOf lam U) (Grid.bitsOf lam V) = aMul (i, X, Y, U, V) := by
  rw [← stAMul]
  change aMul (i, ClauseBound.Alg.bitsOf (Grid.bitsOf lam X), ClauseBound.Alg.bitsOf (Grid.bitsOf lam Y), ClauseBound.Alg.bitsOf (Grid.bitsOf lam U), ClauseBound.Alg.bitsOf (Grid.bitsOf lam V)) = _
  rw [bitsOf_bitsOf hX, bitsOf_bitsOf hY, bitsOf_bitsOf hU, bitsOf_bitsOf hV]

/-! ## Correctness -/

/-- Ψ_{a,a'} of the row network that Algorithm 1 runs, for a < a'. -/
theorem psiLt_row {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    psiLt g false lam y a b z z' = (netOfι g false lam y Rm).Ψ a b z z' := by
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g false o i)).length = lam := fun w hw o x i =>
    length_heG (tr := false) hw x.2 (nodeG_lt (p := g) false o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g false lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g false w'.1 w'.2)) :=
    fun w x w' => stC_dec g g false lam w x w'
  rw [psiLt_eq, netOfι_row]
  refine Eq.trans ?_ (Network.Ψ_pull (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ a b z z').symm
  refine Eq.trans ?_ (rowNetwork_Ψ hlam (gridR0 g g lam Rm) (digOf_le g lam y) hab _ _).symm
  congr 1
  · refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
    rw [hd, hd]
    exact (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).symm
  · refine prod_congr rfl fun k _ => ?_
    rw [hd, hd, hd, hd, A_bitsOf _ (hl z hz b k.1 k.2) (hl z hz b k.2 k.1) (hl z' hz' a k.1 k.2) (hl z' hz' a k.2 k.1)]
    rfl

/-- Ψ_{j,j'} of the column network that Algorithm 1 runs, for j < j'. -/
theorem psiLt_col {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    psiLt g true lam y a b z z' = (netOfι g true lam y Rm).Ψ a b z z' := by
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g true o i)).length = lam := fun w hw o x i =>
    length_heG (tr := true) hw x.2 (nodeG_lt (p := g) true o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g true lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g true w'.1 w'.2)) :=
    fun w x w' => stC_dec g g true lam w x w'
  rw [psiLt_eq, netOfι_col]
  refine Eq.trans ?_ (Network.Ψ_pull (colNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ a b z z').symm
  refine Eq.trans ?_ (colNetwork_Ψ hlam (gridR0 g g lam Rm) (digOf_le g lam y) hab _ _).symm
  congr 1
  · refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
    rw [hd, hd]
    exact (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).symm
  · refine prod_congr rfl fun k _ => ?_
    rw [hd, hd, hd, hd, A_bitsOf _ (hl z hz b k.1 k.2) (hl z' hz' a k.1 k.2) (hl z hz b k.2 k.1) (hl z' hz' a k.2 k.1)]
    rfl

/-- Both directions at once. -/
theorem psiLt_eq_Ψ {g lam : ℕ} (hlam : 1 ≤ lam) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a < b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) :
    psiLt g tr lam y a b z z' = (netOfι g tr lam y Rm).Ψ a b z z' := by
  cases tr
  · exact psiLt_row hlam y Rm hab hz hz'
  · exact psiLt_col hlam y Rm hab hz hz'

/-- **The program computes Ψ_{a,a'}** of the row network and of the column network that Algorithm 1
runs, at all words of g·g²·λ bits. «Ψ_{a,a'} is the product of the factors of the g straight edges
between rows a and a' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the
g(g−1)/2 rectangles q with these two rows.» Same as in the paper; it holds for every number y,
because a digit in base t + 1 is at most t. -/
theorem gridPsi_eq {g lam : ℕ} (hlam : 1 ≤ lam) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) :
    gridPsi g tr lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z' := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact (if_pos (Fin.lt_def.1 h)).trans (psiLt_eq_Ψ hlam tr y Rm h hz hz')
  · rw [Network.Ψ_comm]
    exact (if_neg (not_lt.2 (Fin.lt_def.1 h).le)).trans (psiLt_eq_Ψ hlam tr y Rm h hz' hz)

/-- The same in the form of the interface. -/
theorem stGridPsi : StGridPsi := fun _ tr _ y Rm hlam _ _ hab _ hz _ hz' => gridPsi_eq hlam tr y Rm hab (mem_words.1 hz) (mem_words.1 hz')

/-- The program `gridPsi` computes Ψ: for λ ≥ 1, every ι (a number y < (t + 1)^{|ℛ|}), two different
rows (columns) a, b and settings z, z' of them, gridPsi g tr λ y ((a, b), (z, z')) is Ψ_{a,b}(z, z')
of the network `Eight.Level.netOfι` that Algorithm 1 runs. This is what the
algorithm of one level asks of the function for Ψ (`StPsiOK`). -/
theorem stPsiOK (g : ℕ) (tr : Bool) : StPsiOK g tr (gridPsi g tr) := fun lam y Rm hlam _ a b hab z hz z' hz' => stGridPsi g tr lam y Rm hlam a b hab z hz z' hz'

/-! ## Polynomial time -/

section Poly

variable {α : Type} [Enc α]

/-- The factor of one rectangle is polynomial-time: four strings are cut out of the two settings, a
digit of y is computed, and A_i is «computable in time poly(λ)» (Lemma 2(a)). -/
theorem rectPsi_polyT (g : ℕ) (tr : Bool) {lam y a b i i' : α → ℕ} {z z' : α → List Bool} (hl : PolyT lam) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b)
    (hz : PolyT z) (hz' : PolyT z') (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => rectPsi g tr (lam x) (y x) (a x) (b x) (z x) (z' x) (i x) (i' x) := by
  have hg : PolyT fun _ : α => g := PolyT.const g
  have ht : PolyT fun _ : α => tr := PolyT.const tr
  have hd : PolyT fun x => digit (tOf (lam x)) (y x) (rectIxG g tr (tri (a x) (b x)) (tri (i x) (i' x))) := by
    unfold tOf; fun_prop
  have hX := CertGridG.heG_polyT hg hg hl hz hi (CertGridG.nodeG_polyT hg ht hb hi')
  have hY := CertGridG.heG_polyT hg hg hl hz hi' (CertGridG.nodeG_polyT hg ht hb hi)
  have hU := CertGridG.heG_polyT hg hg hl hz' hi (CertGridG.nodeG_polyT hg ht ha hi')
  have hV := CertGridG.heG_polyT hg hg hl hz' hi' (CertGridG.nodeG_polyT hg ht ha hi)
  cases tr
  · exact SecCrossing_Cert.aMul_polyT.comp (hd.prodMk (hX.prodMk (hY.prodMk (hU.prodMk hV))))
  · exact SecCrossing_Cert.aMul_polyT.comp (hd.prodMk (hX.prodMk (hU.prodMk (hY.prodMk hV))))

/-- Ψ_{a,b} for a < b is polynomial-time: a test on g pairs of strings and a product of g² factors. -/
theorem psiLt_polyT (g : ℕ) (tr : Bool) {lam y a b : α → ℕ} {z z' : α → List Bool} (hl : PolyT lam) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b)
    (hz : PolyT z) (hz' : PolyT z') : PolyT fun x => psiLt g tr (lam x) (y x) (a x) (b x) (z x) (z' x) := by
  have hg : PolyT fun _ : α => g := PolyT.const g
  have ht : PolyT fun _ : α => tr := PolyT.const tr
  have hj : PolyT fun p : α × ℕ => min p.2 (g * g) := by fun_prop
  have hi : PolyT fun p : α × ℕ => min p.2 (g * g) / g := by fun_prop
  have hi' : PolyT fun p : α × ℕ => min p.2 (g * g) % g := by fun_prop
  have hrect : PolyT fun p : α × ℕ => rectPsi g tr (lam p.1) (y p.1) (a p.1) (b p.1) (z p.1) (z' p.1) (min p.2 (g * g) / g) (min p.2 (g * g) % g) :=
    rectPsi_polyT g tr (lam := fun p : α × ℕ => lam p.1) (y := fun p => y p.1) (a := fun p => a p.1) (b := fun p => b p.1) (z := fun p => z p.1) (z' := fun p => z' p.1)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hi hi'
  have hitem : PolyT fun p : α × ℕ => if min p.2 (g * g) / g < min p.2 (g * g) % g then
      rectPsi g tr (lam p.1) (y p.1) (a p.1) (b p.1) (z p.1) (z' p.1) (min p.2 (g * g) / g) (min p.2 (g * g) % g) else 1 :=
    PolyT.ite' (PolyT.decide_lt hi hi') hrect (PolyT.const 1)
  have h1 : PolyT fun x => prodL (g * g) fun j => if j / g < j % g then rectPsi g tr (lam x) (y x) (a x) (b x) (z x) (z' x) (j / g) (j % g) else 1 :=
    CertGridG.prodL_polyT_min (n := fun _ => g * g) (f := fun x j => if j / g < j % g then rectPsi g tr (lam x) (y x) (a x) (b x) (z x) (z' x) (j / g) (j % g) else 1)
      (Unary.const (g * g)) hitem
  have h2 : PolyT fun x => (List.range g).all fun i => heG g g (lam x) (z x) i (nodeG g tr (b x) i) == heG g g (lam x) (z' x) i (nodeG g tr (a x) i) := by fun_prop
  exact PolyT.cond' h2 h1 (PolyT.const 0)

/-- **The program for Ψ is polynomial-time**, as a function of λ, y and the query, for fixed g and a
fixed direction. -/
theorem gridPsi_polyT (g : ℕ) (tr : Bool) {lam y : α → ℕ} {q : α → PsiQ} (hl : PolyT lam) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => gridPsi g tr (lam x) (y x) (q x) :=
  PolyT.ite' (c := fun x => (q x).1.1 < (q x).1.2) (PolyT.decide_lt hq.fst.fst hq.fst.snd) (psiLt_polyT g tr hl hy hq.fst.fst hq.fst.snd hq.snd.fst hq.snd.snd)
    (psiLt_polyT g tr hl hy hq.fst.snd hq.fst.fst hq.snd.snd hq.snd.fst)

end Poly

/-- The same in the form of the interface: λ is a function of the context, given in unary. -/
theorem stGridPsiPoly : StGridPsiPoly := fun g tr _ _ _ hl => gridPsi_polyT g tr (hl.poly.comp PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd

/-- The program `gridPsi` is a polynomial-time function of (context, y, query), for λ given in unary
(`StPsiPoly`). -/
theorem stPsiPoly (g : ℕ) (tr : Bool) : StPsiPoly (gridPsi g tr) := stGridPsiPoly g tr

end Eight.ViaGrouping
