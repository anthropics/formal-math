/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PolyLists
import Mathlib.Tactic

/-! # The plain functions of the procedure

Every plain function of GridProcedures.lean is polynomial-time jointly in all that it reads. K, g,
λ, B are lengths of lists in the context, so they are given in unary; the counter of a loop, the
numbers of the rows, the pattern y and the grouping x are given in binary. -/

public section

namespace ExplicitCost

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

variable {α : Type} [Enc α]

/-! ### The parts of a parent and of a context -/

section Parts

variable {p : α → Parent} (hp : PolyT p)
include hp

/-! K, g, the caller's λ and B are lengths of lists, so they are given in unary (and are
polynomial-time); the lists, the direction, y and x are read off. -/

/-- K is given in unary. -/
@[fun_prop] theorem pK_unary : Unary fun x => pK (p x) := by unfold pK; fun_prop
/-- g is given in unary. -/
@[fun_prop] theorem pG_unary : Unary fun x => pG (p x) := by unfold pG; fun_prop
/-- The caller's λ is given in unary. -/
@[fun_prop] theorem pLam_unary : Unary fun x => pLam (p x) := by unfold pLam; fun_prop
/-- The caller's B is given in unary. -/
@[fun_prop] theorem pB_unary : Unary fun x => pB (p x) := by unfold pB; fun_prop
/-- K is polynomial-time. -/
@[fun_prop] theorem pK_polyT : PolyT fun x => pK (p x) := (pK_unary hp).poly
/-- g is polynomial-time. -/
@[fun_prop] theorem pG_polyT : PolyT fun x => pG (p x) := (pG_unary hp).poly
/-- The caller's λ is polynomial-time. -/
@[fun_prop] theorem pLam_polyT : PolyT fun x => pLam (p x) := (pLam_unary hp).poly
/-- The caller's B is polynomial-time. -/
@[fun_prop] theorem pB_polyT : PolyT fun x => pB (p x) := (pB_unary hp).poly
/-- The lists are read off. -/
@[fun_prop] theorem pLists_polyT : PolyT fun x => pLists (p x) := by unfold pLists; fun_prop
/-- The direction is read off. -/
@[fun_prop] theorem pTr_polyT : PolyT fun x => pTr (p x) := by unfold pTr; fun_prop
/-- The number of the pattern is read off. -/
@[fun_prop] theorem pY_polyT : PolyT fun x => pY (p x) := by unfold pY; fun_prop
/-- The number of the grouping is read off. -/
@[fun_prop] theorem pX_polyT : PolyT fun x => pX (p x) := by unfold pX; fun_prop

end Parts

/-- The parent of a context. -/
@[fun_prop] theorem parentOf_polyT {c : α → Ctx} (hc : PolyT c) : PolyT fun x => parentOf (c x) := by unfold parentOf; fun_prop

/-- The label length of a context is given in unary. -/
@[fun_prop] theorem cLam_unary {c : α → Ctx} (hc : PolyT c) : Unary fun x => cLam (c x) := by unfold cLam hLam; fun_prop

/-! ### The queries -/

/-- The entry of the caller's tables at a grid point. -/
@[fun_prop] theorem pointQuery_polyT {g lam i : α → ℕ} {tr : α → Bool} {q : α → WQ} (hg : Unary g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) (hi : PolyT i) :
    PolyT fun x => pointQuery (g x) (tr x) (lam x) (q x) (i x) := by
  have := hg.poly
  unfold pointQuery; fun_prop

/-- A setting as one string. -/
@[fun_prop] theorem toTable_polyT {q : α → IQ} (hq : PolyT q) : PolyT fun x => toTable (q x) := by unfold toTable; fun_prop

/-- The smaller row first. -/
@[fun_prop] theorem ordered_polyT {q : α → PsiQ} (hq : PolyT q) : PolyT fun x => ordered (q x) := by unfold ordered; fun_prop

/-- The test of the straight edges between two rows. -/
@[fun_prop] theorem straightOK_polyT {g lam : α → ℕ} {tr : α → Bool} {q : α → PsiQ} (hg : Unary g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) :
    PolyT fun x => straightOK (g x) (tr x) (lam x) (q x) := by
  have := hg.poly
  unfold straightOK; fun_prop

/-- The four strings of a rectangle. -/
@[fun_prop] theorem rectStrings_polyT {g lam i i' : α → ℕ} {tr : α → Bool} {q : α → PsiQ} (hg : PolyT g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => rectStrings (g x) (tr x) (lam x) (q x) (i x) (i' x) := by
  unfold rectStrings; fun_prop

/-- ι(q). -/
@[fun_prop] theorem pieceAt_polyT {p : α → Parent} {r κ : α → ℕ} (hp : PolyT p) (hr : PolyT r) (hκ : PolyT κ) : PolyT fun x => pieceAt (p x) (r x) (κ x) := by
  unfold pieceAt; fun_prop

/-- The two columns j / g and j % g of the rectangle number j of a loop. (Written out by hand: on «j
/ g» with g the length of a list, `fun_prop` runs out of time.) -/
theorem colDiv_polyT {β : Type} [Enc β] : PolyT fun v : (Parent × β) × ℕ => v.2 / pG v.1.1 := PolyT.div (by fun_prop) (by fun_prop)
/-- The second column, j % g. -/
theorem colMod_polyT {β : Type} [Enc β] : PolyT fun v : (Parent × β) × ℕ => v.2 % pG v.1.1 := PolyT.mod (by fun_prop) (by fun_prop)

/-- The number j names a rectangle when j / g < j % g. -/
theorem isRect_polyT {β : Type} [Enc β] : PolyT fun v : (Parent × β) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1) := PolyT.decide_lt colDiv_polyT colMod_polyT

/-- The question for a rectangle in Ψ. -/
theorem rectQuestion_polyT : PolyT rectQuestion := by
  have h0 : PolyT fun x : (Parent × PsiQ) × ℕ => x.1.1.2.1.1 := by fun_prop
  have h1 : PolyT fun x : (Parent × PsiQ) × ℕ => pieceAt x.1.1 (tri x.1.2.1.1 x.1.2.1.2) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)) :=
    pieceAt_polyT (by fun_prop) (by fun_prop) (tri_polyT colDiv_polyT colMod_polyT)
  have h2 : PolyT fun x : (Parent × PsiQ) × ℕ => rectStrings (pG x.1.1) (pTr x.1.1) (pLam x.1.1) x.1.2 (x.2 / pG x.1.1) (x.2 % pG x.1.1) :=
    rectStrings_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) colDiv_polyT colMod_polyT
  exact h0.prodMk (PolyT.inr' (PolyT.inr' (PolyT.inr' (PolyT.inl' (h1.prodMk h2)))))

/-- The test of the straight edges against a label. -/
@[fun_prop] theorem labelOK_polyT {g lam : α → ℕ} {tr : α → Bool} {q : α → FQ} (hg : Unary g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) :
    PolyT fun x => labelOK (g x) (tr x) (lam x) (q x) := by
  have := hg.poly
  unfold labelOK; fun_prop

/-- The question for a rectangle in a function of a factorization. -/
theorem factorQuestion_polyT : PolyT factorQuestion := by
  have h0 : PolyT fun x : (Parent × FQ) × ℕ => x.1.1.2.1.1 := by fun_prop
  have h1 : PolyT fun x : (Parent × FQ) × ℕ => (pTr x.1.1, !decide (x.1.2.1.1 < x.1.2.1.2)) := by fun_prop
  have hq : PolyT fun x : (Parent × FQ) × ℕ => tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2) := by fun_prop
  have hk : PolyT fun x : (Parent × FQ) × ℕ => tri (x.2 / pG x.1.1) (x.2 % pG x.1.1) := tri_polyT colDiv_polyT colMod_polyT
  have h2 : PolyT fun x : (Parent × FQ) × ℕ => pieceAt x.1.1 (tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2)) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)) :=
    pieceAt_polyT (by fun_prop) hq hk
  have h3 : PolyT fun x : (Parent × FQ) × ℕ => heG (pG x.1.1) (pG x.1.1) (pLam x.1.1) x.1.2.2.1 (x.2 / pG x.1.1) (nodeG (pG x.1.1) (pTr x.1.1) x.1.2.1.2 (x.2 % pG x.1.1)) :=
    heG_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) colDiv_polyT (nodeG_polyT (by fun_prop) (by fun_prop) (by fun_prop) colMod_polyT)
  have h4 : PolyT fun x : (Parent × FQ) × ℕ => heG (pG x.1.1) (pG x.1.1) (pLam x.1.1) x.1.2.2.1 (x.2 % pG x.1.1) (nodeG (pG x.1.1) (pTr x.1.1) x.1.2.1.2 (x.2 / pG x.1.1)) :=
    heG_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) colMod_polyT (nodeG_polyT (by fun_prop) (by fun_prop) (by fun_prop) colDiv_polyT)
  have h5 : PolyT fun x : (Parent × FQ) × ℕ => chunkAt (lenG (listsAsPieces (pLists x.1.1)) (pG x.1.1) (pTr x.1.1) 0 (pLam x.1.1) (pY x.1.1) (tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2)))
      (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)) (x.1.2.2.2.drop (pG x.1.1 * pLam x.1.1)) :=
    chunkL_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hq hk (by fun_prop)
  exact h0.prodMk (PolyT.inr' (PolyT.inr' (PolyT.inr' (PolyT.inr' (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk h5))))))))

/-! ### The numbers of the network, and what the callee's query becomes -/

section Net

variable {p : α → Parent} (hp : PolyT p)
include hp

/-- P = g³λ is given in unary. -/
@[fun_prop] theorem netP_unary : Unary fun x => netP (p x) := by unfold netP; fun_prop

/-- B₁ is given in unary. -/
@[fun_prop] theorem netB_unary (c : ℕ) : Unary fun x => netB c (p x) := by unfold netB bitsOne; fun_prop

/-- P_a is given in unary. -/
@[fun_prop] theorem netLen_unary {a : α → ℕ} : Unary fun x => netLen (p x) (a x) := by unfold netLen; fun_prop

/-- c_{a,a'} is given in unary. -/
@[fun_prop] theorem netCap_unary {a b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : Unary fun x => netCap (p x) (a x) (b x) := by unfold netCap; fun_prop

end Net

/-- What an algorithm for networks is given (`Printed.inputOf`: P, B and the numbers P_a, c_{a,b},
in unary) is written down in polynomial time from numbers given in unary, the number g of nodes
among them. -/
theorem inputOf_polyT_data {g P B : α → ℕ} {len : α → ℕ → ℕ} {cap : α → ℕ → ℕ → ℕ} (hg : Unary g) (hP : Unary P) (hB : Unary B) (hl : Unary fun p : α × ℕ => len p.1 p.2)
    (hc : Unary fun p : α × ℕ × ℕ => cap p.1 p.2.1 p.2.2) : PolyT fun c => inputOf (g c) (P c) (B c) (len c) (cap c) := by
  have h1 : PolyT fun c => List.replicate (P c) () := hP
  have h2 : PolyT fun c => List.replicate (B c) () := hB
  have h3 : PolyT fun p : α × ℕ => List.replicate (len p.1 p.2) () := hl
  have h4 : PolyT fun p : (α × ℕ) × ℕ => List.replicate (cap p.1.1 p.1.2 p.2) () := PolyT.comp (g := fun p : (α × ℕ) × ℕ => (p.1.1, p.1.2, p.2)) hc (by fun_prop)
  unfold inputOf unary
  fun_prop

/-- K, g and what an algorithm for networks is given, for the network of a parent. -/
@[fun_prop] theorem netData_polyT (c : ℕ) {p : α → Parent} (hp : PolyT p) : PolyT fun x => netData c (p x) :=
  PolyT.prodMk hp.fst (inputOf_polyT_data (pG_unary hp) (netP_unary hp) (netB_unary hp c) (netLen_unary (p := fun q : α × ℕ => p q.1) (by fun_prop))
    (netCap_unary (p := fun q : α × ℕ × ℕ => p q.1) (by fun_prop) (by fun_prop) (by fun_prop)))

/-- Cutting a setting into its K − 1 strings of λ bits, for K given in unary. -/
@[fun_prop] theorem toLists_polyT_data {K lam : α → ℕ} {q : α → TableQuery} (hK : Unary K) (hl : PolyT lam) (hq : PolyT q) : PolyT fun x => toLists (K x) (lam x) (q x) := by
  unfold toLists copyAt place
  fun_prop

/-- From the callee's context and its query to the context of the four procedures and the input of
`entryData`. -/
theorem calleeInput_polyT (c : ℕ) : PolyT (calleeInput c) := by
  have h : PolyT fun y : Ctx × TableQuery => cLam y.1 := (cLam_unary (by fun_prop)).poly
  unfold calleeInput; fun_prop

end ExplicitCost
