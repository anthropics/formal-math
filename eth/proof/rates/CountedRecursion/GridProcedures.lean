/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.AnswersDefs
public import ExplicitCost.EntryDefs

/-! # The contexts, the two networks of a pattern, and the procedure for an entry

Definitions only; nothing is stated or proved here.

**The text** (proof of Theorem A (b)): «Follow the proof of Proposition 3, with this g, with the
A_i, i ∈ 𝓘, in place of A_0, …, A_t and with d in place of 2^t … each Z_ι is the value of the row
network and of the column network.» Proof of Proposition 3, «Two networks for each ι»: «W_a is the
product of the g table entries of row a and of the factors of the
straight edges inside row a. Ψ_{a,a'} is the product of the factors of the g straight edges between
rows a and a' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two
rows.»

**What is here.**
* `Ctx`: the context of an instance: (ℓ, λ, B) in unary, «the (K_ℓ, λ)-clique with |W_w| < 2^B»,
  and, for an instance that was called, its `Parent`: what is needed to compute an entry of ITS
  tables from the caller's.
* `listsAsPieces`: the numbers |𝓘|, c^row_i, c^col_i, read from the lists in the context, in the
  form in which the plain functions of proof/rates/ClauseBound/Alg/Data.lean take them.
* `gridProcsData c`: the row or column network of ι as Definition 2(iii) asks, with g, λ, the
  direction, ι and the lists read from the context. As `Printed.gridProcs` (fixed g, the pieces of
  Lemma 2, computed in a step); here a value of A_i or of a function of a factorization is a query
  to the pieces.
* `procedure c`: an entry of the callee's tables: `entryData` (EntryDefs.lean), each of its queries
  of Definition 2(iii) answered by these procedures (`QueryMachines.QueryMachine.subst`).

The plain functions of the grid (`nodeG`, `heG`, `chkG`, `digG`, `lenG`, `capG`, `rectIxG`) are
those of proof/rates/ClauseBound/Alg/Data.lean, called with p = d = g and h = 0; the layout of the
four strings of a rectangle is that of `Eight.ViaGrouping.rectPsi`, and that of f_{a,a'} is that of
`ClauseBound.Alg.gridFf`. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-! ### Contexts -/

/-- «The set 𝓘 and the numbers … c^row_i, c^col_i»: the list of 𝓘 in increasing order, and the
numbers c^row_i and c^col_i in the same order (in binary). -/
abbrev Lists : Type := List ℤ × List ℕ × List ℕ

/-- What the procedure needs to compute an entry of a callee's tables: (K, g) in unary; the CALLER's
(λ, B) in unary; the lists for the caller's λ; the direction (false: row network), the number y of
the pattern ι, the number x of the grouping. -/
abbrev Parent : Type := (List Unit × List Unit) × (List Unit × List Unit) × Lists × (Bool × ℕ × ℕ)

/-- (ℓ, λ, B) in unary: «the (K_ℓ, λ)-clique with |W_w| < 2^B». This is all that the solver reads of
a context. -/
abbrev Head : Type := List Unit × List Unit × List Unit

/-- The context of an instance: (ℓ, λ, B) in unary; and the parent, if the instance was called. -/
abbrev Ctx : Type := Head × Option Parent

/-- The parts of a parent: K. -/
def pK (p : Parent) : ℕ := p.1.1.length
/-- g. -/
def pG (p : Parent) : ℕ := p.1.2.length
/-- The caller's λ. -/
def pLam (p : Parent) : ℕ := p.2.1.1.length
/-- The caller's B. -/
def pB (p : Parent) : ℕ := p.2.1.2.length
/-- The lists for the caller's λ. -/
def pLists (p : Parent) : Lists := p.2.2.1
/-- The direction: false for the row network, true for the column network. -/
def pTr (p : Parent) : Bool := p.2.2.2.1
/-- The number y of the pattern ι. -/
def pY (p : Parent) : ℕ := p.2.2.2.2.1
/-- The number x of the grouping. -/
def pX (p : Parent) : ℕ := p.2.2.2.2.2

/-- The level, the label length and the bound on the bits of an instance: ℓ. -/
def hLev (h : Head) : ℕ := h.1.length
/-- λ. -/
def hLam (h : Head) : ℕ := h.2.1.length
/-- B. -/
def hB (h : Head) : ℕ := h.2.2.length
/-- The level of an instance. -/
def cLev (c : Ctx) : ℕ := hLev c.1
/-- Its label length. -/
def cLam (c : Ctx) : ℕ := hLam c.1
/-- Its bound on the bits of the tables. -/
def cB (c : Ctx) : ℕ := hB c.1

/-- The parent of an instance. (The procedure is run on instances that were called; for the
outermost instance this is a dummy.) -/
def parentOf (c : Ctx) : Parent := c.2.getD (([], []), ([], []), ([], [], []), (false, 0, 0))

/-- The outermost instance. -/
def top (l lam B : ℕ) : Ctx := ((unary l, unary lam, unary B), none)

/-- The numbers of the pieces, read from the lists. The pieces are numbered by their place in the
list of 𝓘. Only `cnt` and `cap` are read by the functions that are called with it. «We may and do
assume c^row_i, c^col_i ≤ 2λ»: a number in the list is cut at 2λ, so that on EVERY context the
lengths made from it can be written in unary in polynomial time. -/
def listsAsPieces (l : Lists) : PiecesF where
  cnt _ _ := l.1.length
  d _ _ := 0
  cap tr _ lam i := min ((if tr = true then l.2.2 else l.2.1).getD i 0) (2 * lam)
  top _ := 0
  bot _ := 0
  need _ _ := 0
  bits _ _ := 0
  m := 1

/-! ### The numbers of the two networks -/

/-- «B₁ = gB + g²(2λ)^c in the role of B». -/
def bitsOne (c g lam B : ℕ) : ℕ := g * B + g ^ 2 * (2 * lam) ^ c

/-- «P = g³λ». -/
def netP (p : Parent) : ℕ := pG p ^ 3 * pLam p

/-- B₁ for the caller's λ and B. -/
def netB (c : ℕ) (p : Parent) : ℕ := bitsOne c (pG p) (pLam p) (pB p)

/-- P_a: every setting of a row has g·g²·λ bits (this development keeps, for each grid point, a slot
of λ bits for the edge to itself, where the paper encodes a row in g(g² − 1)λ bits). -/
def netLen (p : Parent) (_ : ℕ) : ℕ := nMemb (pG p) (pG p) (pTr p) * (pG p * pG p) * pLam p

/-- c_{a,a'} = gλ + Σ_{q with rows a, a'} c^row_{ι(q)} (or c^col). -/
def netCap (p : Parent) (a b : ℕ) : ℕ := capG (listsAsPieces (pLists p)) (pG p) (pG p) (pTr p) 0 (pLam p) (pY p) a b

/-- The input of Definition 2(iii) for the network, with K and g beside it. -/
def netData (c : ℕ) (p : Parent) : DataInput := (p.1, inputOf (pG p) (netP p) (netB c p) (netLen p) (netCap p))

/-! ### The queries -/

/-- The queries of the procedure: to the caller's tables, or to the pieces. -/
abbrev UpQuery : Type := TableQuery ⊕ PieceQuery

/-- The entry of the caller's tables at the grid point number i of the row a = q.1, at the strings
that the setting z = q.2 of the row has for it. As in `ClauseBound.Alg.gridW`. -/
def pointQuery (g : ℕ) (tr : Bool) (lam : ℕ) (q : WQ) (i : ℕ) : IQ :=
  (nodeG g tr q.1 i, (List.range (g * g)).map fun u => if u = nodeG g tr q.1 i then [] else heG g g lam q.2 i u)

/-- A query for Ψ with the smaller row first: Ψ_{a,a'}(z, z') = Ψ_{a',a}(z', z). -/
def ordered (q : PsiQ) : PsiQ := if q.1.1 < q.1.2 then q else ((q.1.2, q.1.1), (q.2.2, q.2.1))

/-- «the factors of the g straight edges between rows a and a'»: the two copies agree on each of
them. As in `Eight.ViaGrouping.psiLt`. -/
def straightOK (g : ℕ) (tr : Bool) (lam : ℕ) (q : PsiQ) : Bool :=
  (List.range g).all fun i => heG g g lam q.2.1 i (nodeG g tr q.1.2 i) == heG g g lam q.2.2 i (nodeG g tr q.1.1 i)

/-- The four strings (x_q, y_q, u_q, v_q) of the rectangle on the rows a < b and the columns i < i'
(tr = true: on the columns a < b and the rows i < i'). As in `Eight.ViaGrouping.rectPsi`. -/
def rectStrings (g : ℕ) (tr : Bool) (lam : ℕ) (q : PsiQ) (i i' : ℕ) : List Bool × List Bool × List Bool × List Bool :=
  bif tr then (heG g g lam q.2.1 i (nodeG g tr q.1.2 i'), heG g g lam q.2.2 i (nodeG g tr q.1.1 i'), heG g g lam q.2.1 i' (nodeG g tr q.1.2 i), heG g g lam q.2.2 i' (nodeG g tr q.1.1 i))
  else (heG g g lam q.2.1 i (nodeG g tr q.1.2 i'), heG g g lam q.2.1 i' (nodeG g tr q.1.2 i), heG g g lam q.2.2 i (nodeG g tr q.1.1 i'), heG g g lam q.2.2 i' (nodeG g tr q.1.1 i))

/-- ι(q) ∈ 𝓘 for the rectangle number κ of the pair of rows number r: the digit of y in base |𝓘|
gives its place in the list. -/
def pieceAt (p : Parent) (r κ : ℕ) : ℤ := (pLists p).1.getD (digG (listsAsPieces (pLists p)) (pG p) (pTr p) 0 (pLam p) (pY p) r κ) 0

/-- The question «A_{ι(q)}(x_q, y_q, u_q, v_q)?» for the rectangle with the columns j / g < j % g. -/
def rectQuestion (x : (Parent × PsiQ) × ℕ) : PieceQuery :=
  (x.1.1.2.1.1, .inr (.inr (.inr (.inl (pieceAt x.1.1 (tri x.1.2.1.1 x.1.2.1.2) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)),
    rectStrings (pG x.1.1) (pTr x.1.1) (pLam x.1.1) x.1.2 (x.2 / pG x.1.1) (x.2 % pG x.1.1))))))

/-- In f_{a,b}(z, θ): the first gλ bits of θ are the strings of z on the g straight edges to b. As
in `ClauseBound.Alg.gridFf`. -/
def labelOK (g : ℕ) (tr : Bool) (lam : ℕ) (q : FQ) : Bool :=
  (List.range (nMemb g g tr)).all fun i => heG g g lam q.2.1 i (nodeG g tr q.1.2 i) == block lam i q.2.2

/-- The question for the factor of the rectangle with the columns j / g < j % g in f_{a,b}(z, θ):
the function of the first pair of strings if a < b, of the second if a > b, at the two strings of z
and the chunk of θ that belongs to the rectangle. As in `ClauseBound.Alg.gridFf`. -/
def factorQuestion (x : (Parent × FQ) × ℕ) : PieceQuery :=
  (x.1.1.2.1.1, .inr (.inr (.inr (.inr ((pTr x.1.1, !decide (x.1.2.1.1 < x.1.2.1.2)),
    pieceAt x.1.1 (tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2)) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)),
    (heG (pG x.1.1) (pG x.1.1) (pLam x.1.1) x.1.2.2.1 (x.2 / pG x.1.1) (nodeG (pG x.1.1) (pTr x.1.1) x.1.2.1.2 (x.2 % pG x.1.1)),
     heG (pG x.1.1) (pG x.1.1) (pLam x.1.1) x.1.2.2.1 (x.2 % pG x.1.1) (nodeG (pG x.1.1) (pTr x.1.1) x.1.2.1.2 (x.2 / pG x.1.1)),
     chunkAt (lenG (listsAsPieces (pLists x.1.1)) (pG x.1.1) (pTr x.1.1) 0 (pLam x.1.1) (pY x.1.1) (tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2))) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1))
       (x.1.2.2.2.drop (pG x.1.1 * pLam x.1.1))))))))

/-! ### The four procedures -/

/-- «W_a is the product of the g table entries of row a and of the factors of the straight edges
inside row a»: the check, then g queries to the caller's tables. -/
def rowWeight : QueryMachine UpQuery Ans (Parent × WQ) ℤ :=
  QueryMachine.ite (fun x : Parent × WQ => chkG (pG x.1) (pG x.1) (pTr x.1) (pLam x.1) x.2)
    (QueryMachine.prodRange (fun x : Parent × WQ => pG x.1) (askInt fun v : (Parent × WQ) × ℕ => Sum.inl (toTable (pointQuery (pG v.1.1) (pTr v.1.1) (pLam v.1.1) v.1.2 v.2))))
    (QueryMachine.const 0)

/-- «Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows»: the check, then
one query to the pieces for each rectangle. The loop runs over all j = i·g + i' < g², with the
factor 1 unless i < i'. -/
def rowPair : QueryMachine UpQuery Ans (Parent × PsiQ) ℤ :=
  QueryMachine.mapIn (fun x : Parent × PsiQ => (x.1, ordered x.2))
    (QueryMachine.ite (fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2)
      (QueryMachine.prodRange (fun x : Parent × PsiQ => pG x.1 * pG x.1)
        (QueryMachine.ite (fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × PsiQ) × ℕ => Sum.inr (rectQuestion v)) (QueryMachine.const 1)))
      (QueryMachine.const 0))

/-- f_{a,a'}(z, θ): the check of the straight edges against θ, then one query to the pieces for each
rectangle. -/
def rowFactor : QueryMachine UpQuery Ans (Parent × FQ) ℤ :=
  QueryMachine.ite (fun x : Parent × FQ => labelOK (pG x.1) (pTr x.1) (pLam x.1) x.2)
    (QueryMachine.prodRange (fun x : Parent × FQ => pG x.1 * pG x.1)
      (QueryMachine.ite (fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × FQ) × ℕ => Sum.inr (factorQuestion v)) (QueryMachine.const 1)))
    (QueryMachine.const 0)

/-- **«Two networks for each ι»**: the row network (direction false) or the column network
(direction true) of ι, as Definition 2(iii) asks; everything is read from the context. Every string
of g³λ bits is a setting; W_a is 0 unless the slots for the edges from a grid point to itself are 0
and the straight edges inside the row agree. -/
def gridProcsData (c : ℕ) : ProcsQ UpQuery Ans Parent where
  P := netP
  B := netB c
  len := netLen
  cap := netCap
  mem := QueryMachine.lift (Stepped.mapIn (fun _ => ()) (Stepped.const true))
  W := rowWeight
  Ψ := rowPair
  f := rowFactor

/-! ### The procedure -/

/-- From the callee's context and its query (γ, Θ): the context of the four procedures, and the
input of `entryData`: K, g, the input of Definition 2(iii), the grouping number x, and Θ cut into
its K − 1 strings of L bits; L is the callee's label length. -/
def calleeInput (c : ℕ) (y : Ctx × TableQuery) : Parent × X0 DataInput :=
  (parentOf y.1, ((netData c (parentOf y.1), pX (parentOf y.1)), toLists (pK (parentOf y.1)) (cLam y.1) y.2))

/-- **«answer each query by computing the entry»**: the entry (γ, Θ) of the tables W̃ of the callee,
computed with queries to the caller's tables and to the pieces. -/
def procedure (c : ℕ) : QueryMachine UpQuery Ans (Ctx × TableQuery) Ans :=
  QueryMachine.mapOut (QueryMachine.mapIn (calleeInput c) (entryData.subst (gridProcsData c).answer)) Sum.inl

end ExplicitCost
