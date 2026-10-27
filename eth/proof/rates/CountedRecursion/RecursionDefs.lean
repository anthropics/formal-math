/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverDefs
public import CliqueLevelsStatement

/-! # Theorem A (b) on counted operations: the statements

Definitions and statements only; nothing is proved here.

**The text.** «One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w|
< 2^B, outputs the value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}(K_ℓ(λ+B))^{C₀K_ℓ²} operations.»
The machine is `recursion c x₀` (SolverDefs.lean).

**The forms.** `RecursionCountedUpTo`: the pieces are an oracle, and a query about strings of λ'
bits costs 2^{cλ'} + 2 operations (`PiecesCounted.price`: the cost that Definition 7 (c) prints, and
two for handing over the question and taking the answer); then ALL states have size at most
(K_ℓ(λ+B))^{C₀K_ℓ}, which is within the factor (K_ℓ(λ+B))^{C₀K_ℓ²} that the printed bound has
anyway; states within that factor are what it takes for the exponent e_ℓK_ℓ²λ to carry over to a
Turing machine with that oracle without a constant factor (`CliqueLevels.SolvesInFactor`).
`RecursionPlugged`: the pieces are computed by their algorithm; the machine has query access to the
tables alone, and its states are larger by the room of that algorithm, about 2^{cΛ} for the largest
label length Λ of the recursion; so there the exponent carries over to a Turing machine only up to a
constant factor.
`RecursionSolves`: the sentence of the theorem as `CliqueLevels.Solves` has it, the ONE definition
that is also the hypothesis of Theorem D (a).

**Lemma 8** is used in its form up to the call (`GroupingWithCall`, with `EntryCostExplicit` for the
entries), not as `GroupingExplicit`: the call is a call of the tower, not a substitution.

**The order of this file.**
1. The pieces in the form in which the plain functions and the theorems of this development take
   them (`piecesOf`, `listsOf`), and the networks of a pattern (`patternNet`).
2. What the recursion is to compute (`spec`, of type `QueryMachines.Tower.Spec`), and the bounds
   that λ and B obey along the recursion from one outermost instance (`boundsDown`). These are
   devices of the statements, not parts of the machine; they may and do use ρ.
3. The steps of the printed proof, in its order.
4. The costs of the solver and of the procedure as functions of the depth (`solverCost`,
   `entryCost`), that the machines meet the specification with them (`RecursionMeets`), and the
   count (`TotalCount`).
5. The theorem, in its two forms, and how the steps give it.

**Where this differs from the printed algorithm.** (1) An operation is a step of a machine with
query access; every statement carries a bound on the sizes of the states. (2) ℓ, λ, B are given in
unary; K and g are written in unary by a loop of ℓ rounds at the start of every activation of the
solver. (3) 𝓘 is handled as the list of its elements in increasing order, and a pattern ι as a
number y < |𝓘|^{|ℛ|}, whose digit in base |𝓘| at the number of a
rectangle is the place of ι(q) in that list. (4) A number c^row_i or c^col_i that the pieces return
is cut at 2λ when it is used («We may and do assume c^row_i, c^col_i ≤ 2λ»). (5) A setting of a row
has g³λ bits, not g(g² − 1)λ (a slot of λ bits for the edge from a grid point to itself, which must
be 0). (6) Every string of g³λ bits is a setting, so the test for membership says yes without a
query.
(7) If the totals are equal the row network is taken. (8) A call and each level that a query runs up
    cost 2 operations more (the tower's own steps). (9) The numbers c_{a,a'} are not stored with the
    callee: the procedure writes the input of Definition 2(iii) anew, from the lists in the context,
    when it is handed a query (this is not counted as an operation; it is polynomial-time in the
    context). (10) In the same way «finding the numbers c_{a,a'} and the totals of both networks for
    one ι» is the plain function by which the solver hands the network over to the procedure of
    Lemma 8; it is polynomial-time in what the solver holds, and is not counted.
(11) c^row_i, c^col_i ≤ 2λ is a hypothesis of the statements here (`Setting.short`). The paper says
     after Definition 7: «We may and do assume c^row_i, c^col_i ≤ 2λ … (and c by c + 2 …)»; we read
     this so: from there on the pieces ARE short, and the c of Theorem A is the c after the
     replacement. The statements here are for short pieces only. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-! ## 1. The pieces and the networks of a pattern -/

/-- The hypotheses of the theorem: pieces with parameters (ρ, c) (clauses (a), (b) and the sizes of (c)
of Definition 7, without its algorithm), with c^row_i, c^col_i ≤ 2λ; «x₀ ≥ 18 an integer with 2^{x₀}
≥ c + 5». -/
structure Setting (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data) : Prop where
  is : D.Is ρ c
  short : ∀ lam tr i, D.cap lam tr i ≤ 2 * lam
  x₀_ge : 18 ≤ x₀
  x₀_c : c + 5 ≤ 2 ^ x₀

/-- The element number j of 𝓘, in increasing order. -/
def indexAt (D : PiecesCounted.Data) (lam j : ℕ) : ℤ := ((D.fam lam).I.sort).getD j 0

/-- The pieces in the form of proof/rates/ClauseBound/Alg/Data.lean: numbered by their place in 𝓘;
the pad is not read, and neither is the parameter h. The functions of a factorization are taken as 0
at a string θ that has not c^row_i (or c^col_i) bits, where Definition 7 says nothing of them. -/
def piecesOf (D : PiecesCounted.Data) (c : ℕ) : PiecesF where
  cnt _ lam := #(D.fam lam).I
  d _ lam := (D.fam lam).d.toNat
  cap tr _ lam j := D.cap lam tr (indexAt D lam j)
  top q := if q.2.2.2.2.length = D.cap q.2.2.1.length q.1.2 (indexAt D q.2.2.1.length q.2.1.2) then
    D.fn q.2.2.1.length q.1.2 false (indexAt D q.2.2.1.length q.2.1.2) (PiecesCounted.toBits _ q.2.2.1, PiecesCounted.toBits _ q.2.2.2.1) q.2.2.2.2 else 0
  bot q := if q.2.2.2.2.length = D.cap q.2.2.1.length q.1.2 (indexAt D q.2.2.1.length q.2.1.2) then
    D.fn q.2.2.1.length q.1.2 true (indexAt D q.2.2.1.length q.2.1.2) (PiecesCounted.toBits _ q.2.2.1, PiecesCounted.toBits _ q.2.2.2.1) q.2.2.2.2 else 0
  need _ _ := 0
  bits _ lam := (2 * lam) ^ c
  m := 1

/-- The lists that the solver has after its queries to the pieces. -/
def listsOf (D : PiecesCounted.Data) (lam : ℕ) : Lists :=
  ((D.fam lam).I.sort, ((D.fam lam).I.sort).map fun i => D.cap lam false i, ((D.fam lam).I.sort).map fun i => D.cap lam true i)

/-- **The row network (tr = false) or the column network (tr = true) of the pattern number y**, for
the (g², λ)-clique with the tables W, as the data of Definition 2. As `Eight.ViaGrouping.levelNetP`,
for these pieces: the network `ClauseBound.Alg.GridNet.gridN` on words, with Ψ_{a,a'} the sum that
its factorization defines and P_a = g³λ. It has g nodes (`nParts g g tr` is g). -/
noncomputable def patternNet (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (W : ℕ → List Bool → ℤ) : Net (nParts g g tr) :=
  ofNetwork (gridN (piecesOf D c) [()] g g tr 0 lam y fun w θ => W w.val (List.ofFn θ).flatten) fun _ => g ^ 3 * lam

/-- The parent for these numbers. -/
def mkParent (D : PiecesCounted.Data) (K g lam B : ℕ) (tr : Bool) (y x : ℕ) : Parent := ((unary K, unary g), (unary lam, unary B), listsOf D lam, (tr, y, x))

/-- Ξ = g²(λ + B). -/
def Xi (g lam B : ℕ) : ℕ := g ^ 2 * (lam + B)

/-! ## 2. What the recursion is to compute -/

/-- Tables as an oracle of the tower: the entry v is the answer `Sum.inl v`. -/
def answersOf (K lam : ℕ) (W : ℕ → List Bool → ℤ) : TableQuery → Option Ans := fun q => (tables K lam W q).map Sum.inl

/-- Back: the tables that an oracle gives (0 where it gives nothing). -/
def readTables (f : TableQuery → Option Ans) : ℕ → List Bool → ℤ := fun w z => asInt ((f (w, z)).getD (.inl 0))

/-- The instance (a, f) is «the (K_ℓ, λ)-clique with |W_w| < 2^B», λ, B ≥ 1. -/
def Fits (x₀ : ℕ) (a : Ctx) (f : TableQuery → Option Ans) : Prop :=
  1 ≤ cLam a ∧ 1 ≤ cB a ∧ ∃ W : ℕ → List Bool → ℤ, (∀ w < Levels.Gen.K x₀ (cLev a), ∀ z ∈ words ((Levels.Gen.K x₀ (cLev a) - 1) * cLam a), |W w z| < 2 ^ cB a) ∧ f = answersOf (Levels.Gen.K x₀ (cLev a)) (cLam a) W

/-- What the solver has computed when the loop over the patterns begins. -/
def readyOf (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) : Ready :=
  (((((h, (unary (2 ^ (3 * (hLev h - 1) + x₀)), unary (Levels.Gen.K x₀ (hLev h - 1)))), (listsOf D (hLam h)).1), (D.fam (hLam h)).d), (listsOf D (hLam h)).2.1), (listsOf D (hLam h)).2.2)

/-- The tables W̃ of the (K, L)-clique of the groups, for the network of the parent p and the
caller's tables W. -/
noncomputable def groupTables (D : PiecesCounted.Data) (c : ℕ) (p : Parent) (L : ℕ) (W : ℕ → List Bool → ℤ) : ℕ → List Bool → ℤ := fun γ Θ =>
  if h : γ < pK p then
    (Value.groupClique asked.under (netInput (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) (netP p) (netB c p)) (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) (Nat.zero_lt_of_lt h) (pX p) L).W ⟨γ, h⟩ Θ
  else 0

/-- **What the recursion is to compute.** The depth of an instance is ℓ; its value is the value of
the clique; the solver may call, for each pattern y, the context that it makes from y and the first
grouping x that the test accepts («find the first such grouping among all K^g»); the tables of a
callee are the tables W̃ of the clique of the groups. `Bound` holds λ and B within bounds (see
`InBounds`). -/
noncomputable def spec (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) : Tower.Spec Ctx TableQuery Ans where
  lev := cLev
  Good a f := Bound a ∧ Fits x₀ a f
  val a f := .inl (clique (Levels.Gen.K x₀ (cLev a)) (cLam a) fun w => readTables f w.val).value
  Child a _ a' := 1 ≤ cLev a ∧ ∃ y x : ℕ, y < nPatterns (readyOf D x₀ a.1) ∧
    (List.range (rK (readyOf D x₀ a.1) ^ rG (readyOf D x₀ a.1))).find? (fun x' => goodData (searchInput c (readyOf D x₀ a.1, y), x')) = some x ∧ a' = child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))
  tab a' f := answersOf (pK (parentOf a')) (cLam a') (groupTables D c (parentOf a') (cLam a') (readTables f))

/-- Bounds for (λ, B) after k levels down from the outermost instance (ℓ, λ, B). With K, g, ζ of the
level j = ℓ − (k + 1) and (Λ, 𝔅) the bounds one level up: «K²L ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K²», N =
g⁴Λ; and B' = ⌈2gP/K⌉ + g²B₁ for P = g³Λ, B₁ = g𝔅 + g²(2Λ)^c. -/
noncomputable def boundsDown (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (lam, B)
  | k + 1 =>
    (⌊((ρ + 3 * Levels.Gen.zeta (l - (k + 1))) * ((Levels.Gen.g x₀ (l - (k + 1)) : ℝ) ^ 4 * (boundsDown ρ c x₀ l lam B k).1) +
        (c : ℝ) / 4 * (Levels.Gen.g x₀ (l - (k + 1)) : ℝ) ^ 4 * Real.logb 2 (2 * (boundsDown ρ c x₀ l lam B k).1) + (Levels.Gen.K x₀ (l - (k + 1)) : ℝ) ^ 2) / (Levels.Gen.K x₀ (l - (k + 1)) : ℝ) ^ 2⌋₊,
     bitsOut (Levels.Gen.K x₀ (l - (k + 1))) (Levels.Gen.g x₀ (l - (k + 1))) (Levels.Gen.g x₀ (l - (k + 1)) ^ 3 * (boundsDown ρ c x₀ l lam B k).1)
       (bitsOne c (Levels.Gen.g x₀ (l - (k + 1))) (boundsDown ρ c x₀ l lam B k).1 (boundsDown ρ c x₀ l lam B k).2))

/-- The bound for λ at the depth j ≤ ℓ. -/
noncomputable def lamAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := (boundsDown ρ c x₀ l lam B (l - j)).1
/-- The bound for B at the depth j ≤ ℓ. -/
noncomputable def bitsAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := (boundsDown ρ c x₀ l lam B (l - j)).2

/-- The context lies within the bounds that hold along the recursion from the outermost instance (ℓ,
λ, B). -/
def InBounds (ρ : ℝ) (c x₀ l lam B : ℕ) (a : Ctx) : Prop := cLev a ≤ l ∧ cLam a ≤ lamAt ρ c x₀ l lam B (cLev a) ∧ cB a ≤ bitsAt ρ c x₀ l lam B (cLev a)

/-- The largest label length of the recursion from (ℓ, λ, B). -/
noncomputable def lamMax (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ := (range (l + 1)).sup fun j => lamAt ρ c x₀ l lam B j

/-- The pieces as an oracle that answers only questions about strings of at most Λ bits. A run
against it is a run in which no other question is asked. (This is the function that is written out
in `PiecesCounted.OracleFromAlgorithm`.) -/
def piecesUpTo (D : PiecesCounted.Data) (Lam : ℕ) : PieceQuery → Option Ans := fun g => if g.1.length ≤ Lam then D.oracle g else none

/-- What a query to the pieces about strings of λ bits costs: 2^{cλ} + 2 operations. -/
def askCost (c lam : ℕ) : ℕ := PiecesCounted.steps c lam + 2

/-- The prices: a call tc, a query to the tables tq, a query to the pieces about strings of λ' bits
2^{cλ'} + 2. -/
def solPrices (c tc tq : ℕ) : SolQuery → ℕ := Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) (PiecesCounted.price c))
/-- The same without calls: the prices of the queries of the procedure and of the one machine. -/
def upPrices (c tq : ℕ) : UpQuery → ℕ := Sum.elim (fun _ => tq) (PiecesCounted.price c)

/-! ## 3. The steps of the printed proof -/

/-- The numbers read from the lists are those of the pieces. -/
def ListsAgree : Prop := ∀ (D : PiecesCounted.Data) (c lam : ℕ), (∀ tr i, D.cap lam tr i ≤ 2 * lam) →
  (listsAsPieces (listsOf D lam)).cnt 0 lam = (piecesOf D c).cnt 0 lam ∧ ∀ tr, ∀ j < #(D.fam lam).I, (listsAsPieces (listsOf D lam)).cap tr 0 lam j = (piecesOf D c).cap tr 0 lam j

/-- «For ℓ = 0, brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms, each at a cost of at most
(K₀(λ+B))^{C₅}.» With explicit numbers: a term costs K₀ queries and K₀ + 1 steps. One constant for
all x₀. -/
def SolverBase : Prop := ∃ C₅ : ℕ, ∀ (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) (gl : PieceQuery → Option Ans) (a : Ctx) (f : TableQuery → Option Ans), Fits x₀ a f → cLev a = 0 → ∀ tc tq : ℕ,
  (solver c x₀).Within ((spec D c x₀ Bound).oracle gl a f) (solPrices c tc tq) a (2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * cLam a) * (2 ^ x₀ * (tq + 1) + 1)) ((2 ^ x₀ * (cLam a + cB a)) ^ C₅) ((spec D c x₀ Bound).val a f)

/-- «Thus d^{|ℛ|}Z = Σ_ι Z_ι over the |𝓘|^{|ℛ|} … functions ι : ℛ → 𝓘, and each Z_ι is the value of
the row network and of the column network»: whichever of the two is taken for each ι. «this part of
that proof works for every g ≥ 2». -/
def Expansion : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (g lam : ℕ) (W : ℕ → List Bool → ℤ) (tr : ℕ → Bool), 2 ≤ g → 1 ≤ lam →
  (D.fam lam).d ^ nRectG g g * (clique (g * g) lam fun w => W w.val).value = ∑ y ∈ range (#(D.fam lam).I ^ nRectG g g), (patternNet D c g (tr y) lam y W).value

/-- «|𝓘|^{|ℛ|} ≤ Ξ^{cg⁴/4}». -/
def PatternsFew : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ g lam B : ℕ, 2 ≤ g → 1 ≤ lam → 1 ≤ B → 4 * nRectG g g ≤ g ^ 4 ∧ (#(D.fam lam).I ^ nRectG g g) ^ 4 ≤ Xi g lam B ^ (c * g ^ 4)

/-- «so again P = g³λ, gP = N, and moreover c_{a,a'} ≤ g²λ = P/g. By Definition 7 (c), Definition 2
holds with B₁ = gB + g²(2λ)^c in the role of B and with τ = 2^{cλ}Ξ^{C₂}.» For the procedures
`gridProcsData c`: the network is a network with these parameters; the input that the procedure
writes is the input that belongs to it; and every query of Definition 2(iii) is answered within
(2^{cλ} + 2 + tq)·Ξ^{C₂} operations, if a query to the tables of the clique costs tq and a query to
the pieces 2^{cλ} + 2, on states of size at most Ξ^{C₂}. Only questions about strings of λ bits are
asked. C₂ depends on c only. -/
def BothNetworks : Prop := ∀ c : ℕ, ∃ C₂ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (K g lam B y x tq Lam : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 2 ≤ g → K ≤ g → 1 ≤ lam → lam ≤ Lam → 1 ≤ B →
  (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < #(D.fam lam).I ^ nRectG g g → x < K ^ g →
    (patternNet D c g tr lam y W).Is (g ^ 3 * lam) (bitsOne c g lam B) ∧
    (∀ a b, a ≠ b → (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam) ∧
    netData c (mkParent D K g lam B tr y x) = ((unary K, unary g), netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) ∧
    ∀ (q : NetQuery) (v : ℤ), netOracle (patternNet D c g tr lam y W) q = some v →
      (gridProcsData c).answer.Within (Sum.elim (answersOf (g * g) lam W) (piecesUpTo D Lam)) (upPrices c tq) (mkParent D K g lam B tr y x, q) ((askCost c lam + tq) * Xi g lam B ^ C₂) (Xi g lam B ^ C₂) v

/-- A_i at four strings given as lists. -/
def pieceValue (D : PiecesCounted.Data) (lam : ℕ) (i : ℤ) (s : List Bool × List Bool × List Bool × List Bool) : ℤ :=
  (D.fam lam).A i (PiecesCounted.toBits lam s.1) (PiecesCounted.toBits lam s.2.1) (PiecesCounted.toBits lam s.2.2.1) (PiecesCounted.toBits lam s.2.2.2)

/-- «Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows»: on settings, the Ψ
of `patternNet`, which is the sum that the factorization defines, is this product, in the form in
which `rowPair` computes it. -/
def PairIsProduct : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (g lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 2 ≤ g → 1 ≤ lam → y < #(D.fam lam).I ^ nRectG g g →
  ∀ a b : Fin (nParts g g tr), a < b → ∀ z ∈ (patternNet D c g tr lam y W).S a, ∀ z' ∈ (patternNet D c g tr lam y W).S b,
    (patternNet D c g tr lam y W).Ψ a b z z' = if straightOK g tr lam ((a.val, b.val), (z, z')) = true then
      ∏ j ∈ range (g * g), (if j / g < j % g then pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri a.val b.val) (tri (j / g) (j % g)))) (rectStrings g tr lam ((a.val, b.val), (z, z')) (j / g) (j % g)) else 1)
    else 0

/-- The totals that the solver compares are the totals U of the two networks. -/
def TotalsAre : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (g lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 2 ≤ g → 1 ≤ lam →
  (patternNet D c g tr lam y W).U = totalG (listsAsPieces (listsOf D lam)) g g tr 0 lam y

/-- «U = min(U^row, U^col) ≤ N/g + |ℛ|(4ρλ + c·log(2λ)) ≤ N(ρ + 1/g) + (c/4)g⁴log(2λ).» -/
def SmallerTotal : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ g lam y : ℕ, 2 ≤ g → 1 ≤ lam → y < #(D.fam lam).I ^ nRectG g g →
  ((min (totalG (listsAsPieces (listsOf D lam)) g g false 0 lam y) (totalG (listsAsPieces (listsOf D lam)) g g true 0 lam y) : ℕ) : ℝ) ≤ (g : ℝ) ^ 4 * lam * (ρ + 1 / g) + (c : ℝ) / 4 * (g : ℝ) ^ 4 * Real.logb 2 (2 * lam)

/-- «Case (ii) of Lemma 8 applies to the network with the smaller total (with B₁ in the role of B)»:
for K = K_ℓ, g = g_ℓ, ζ = ζ_ℓ, and either network. -/
def CaseTwoApplies : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (l lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 1 ≤ lam → y < #(D.fam lam).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) →
  AppRunningTime.Cases (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) tr) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).c

/-- «So the lemma's L satisfies K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K².» -/
def LabelBound : Prop := ∀ (ρ : ℝ) (c x₀ l lam U : ℕ), 1 / 2 ≤ ρ → 18 ≤ x₀ → 1 ≤ lam → (U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / Levels.Gen.g x₀ l) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) →
  (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
    (ρ + 3 * Levels.Gen.zeta l) * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) + (Levels.Gen.K x₀ l : ℝ) ^ 2

/-- «Crude bounds give L ≤ N + 1», for the lemma's L and either network of a pattern. -/
def LabelCrude : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (l lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 1 ≤ lam →
  AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1

/-- «Crude bounds give L ≤ N + 1 [`LabelCrude` for the L of a call, a clause of `ChainLabel` for the
bounds; here a hypothesis], B' ≤ N + g²B₁, g(P + B₁) ≤ Ξ^{c+4} and K(L + B') ≤ Ξ^{c+5}.» -/
def CrudeBounds : Prop := ∀ c x₀ l lam B L : ℕ, 18 ≤ x₀ → 1 ≤ lam → 1 ≤ B → L ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 →
  bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * lam) (bitsOne c (Levels.Gen.g x₀ l) lam B) ≤ Levels.Gen.g x₀ l ^ 4 * lam + Levels.Gen.g x₀ l ^ 2 * bitsOne c (Levels.Gen.g x₀ l) lam B ∧
  Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * lam + bitsOne c (Levels.Gen.g x₀ l) lam B) ≤ Xi (Levels.Gen.g x₀ l) lam B ^ (c + 4) ∧
  Levels.Gen.K x₀ l * (L + bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * lam) (bitsOne c (Levels.Gen.g x₀ l) lam B)) ≤ Xi (Levels.Gen.g x₀ l) lam B ^ (c + 5)

/-- A call goes to the (K_ℓ, L)-clique of the groups of the network with the smaller total of some
pattern: one level down, well formed (λ = L ≥ 1, B = B' ≥ 1, |W̃_γ| < 2^{B'}), with the value Z_ι
for the pattern ι whose number stands in the child's parent, with L as bounded in `LabelBound` and
B' as printed. -/
def ChildIsGood : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a a' : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → (spec D c x₀ Bound).Child a f a' →
  cLev a' = l ∧ Fits x₀ a' ((spec D c x₀ Bound).tab a' f) ∧
  pY (parentOf a') < nPatterns (readyOf D x₀ a.1) ∧
  (spec D c x₀ Bound).val a' ((spec D c x₀ Bound).tab a' f) = .inl (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, pY (parentOf a'))) (cLam a) (pY (parentOf a')) (readTables f)).value ∧
  (Levels.Gen.K x₀ l : ℝ) ^ 2 * cLam a' ≤ (ρ + 3 * Levels.Gen.zeta l) * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * cLam a) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) + (Levels.Gen.K x₀ l : ℝ) ^ 2 ∧
  cB a' = bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))

/-- **One entry of the callee's tables**: «an entry is a sum of at most 2^{2gP/K} terms …»
(`EntryCostExplicit`), each query of Definition 2(iii) answered by the procedures of the network
(`BothNetworks`): within 2^{P⌊2g/K⌋}·(2^{cλ} + 2 + tq)·Ξ^{C} operations, on states of size at most
Ξ^{C}; P = g³λ; λ, B are the caller's. C depends on c only. -/
def ProcedureCost : Prop := ∀ c : ℕ, ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a a' : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → (spec D c x₀ Bound).Child a f a' →
  ∀ (q : TableQuery) (v : Ans), (spec D c x₀ Bound).tab a' f q = some v → ∀ tq Lam : ℕ, cLam a ≤ Lam →
    (procedure c).Within (Sum.elim f (piecesUpTo D Lam)) (upPrices c tq) (a', q)
      (2 ^ (Levels.Gen.g x₀ l ^ 3 * cLam a * (2 * Levels.Gen.g x₀ l / Levels.Gen.K x₀ l)) * ((askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C)) (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C) v

/-- **The solver at a level ℓ + 1**, with its calls answered by the values Z_ι at the price tc: «The
set 𝓘 and the numbers d, c^row_i, c^col_i are computed once. … each of the following takes at most
Ξ^{C₃} operations: finding the numbers c_{a,a'} and the totals of both networks for one ι; adding
one Z_ι; computing d^{|ℛ|} and dividing by it.» It returns Z within
|𝓘|^{|ℛ|}·(Ξ^{C₃}·K^g + tc) + (2|𝓘| + 2)·(2^{cλ} + 2) + Ξ^{C₃} operations, on states of size at most
Ξ^{C₃}, and the contexts of its calls have size at most Ξ^{C₃}. C₃ depends on c only. -/
def SolverStep : Prop := ∀ c : ℕ, ∃ C₃ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 →
  (∀ a', (spec D c x₀ Bound).Child a f a' → size a' ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃) ∧
  ∀ tc tq Lam : ℕ, cLam a ≤ Lam → (solver c x₀).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) a
    (#(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) * (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃ * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + tc) + (2 * #(D.fam (cLam a)).I + 2) * askCost c (cLam a) + Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃)
    (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃) ((spec D c x₀ Bound).val a f)

/-! ### How the steps rest on each other -/

/-- The two networks, from: Ψ is the product that `rowPair` computes; the numbers read from the
lists are those of the pieces. -/
def BothNetworksFrom : Prop := PairIsProduct → ListsAgree → BothNetworks

/-- A call is good, from Lemma 8 up to the call, its L, the bound on the entries, «whose value is
that of the network», and the printed steps on the network with the smaller total. -/
def ChildIsGoodFrom : Prop := GroupingWithCall → LabelLengthIsL → EntryCostExplicit → ValueIsKept → BothNetworks → TotalsAre → SmallerTotal → CaseTwoApplies → LabelBound → ChildIsGood

/-- An entry of the callee's tables, from Lemma 8 up to the call, its L and case (ii) (the grouping
in the callee's context is the first that the test accepts, so it has the two properties), the cost
of an entry with one constant (which asks L ≤ 2gP, and this follows from «Crude bounds give L ≤ N +
1» for the L of the call), the procedures of the network, «g(P + B₁) ≤ Ξ^{c+4}», and «answer each
query by computing …», the rule of substitution. -/
def ProcedureCostFrom : Prop := GroupingWithCall → LabelLengthIsL → CaseTwoApplies → EntryCostExplicit → BothNetworks → LabelCrude → CrudeBounds → QueryMachines.StSubstWithin → ProcedureCost

/-- The solver at a level ℓ + 1, from the numbers of the level, the expansion, Lemma 8 up to the
call on the network with the smaller total, and the rule of substitution by which the call is passed
on. -/
def SolverStepFrom : Prop := NumbersRun → Expansion → PatternsFew → GroupingWithCall → LabelLengthIsL → ValueIsKept → BothNetworks → CaseTwoApplies → CrudeBounds → QueryMachines.StSubstWithin → SolverStep

/-! ## 4. The costs as functions of the depth, and the count -/

/-- Ξ for the callers of the depth j + 1, at the bounds for λ and B: g_j²(Λ_{j+1} + 𝔅_{j+1}). -/
noncomputable def xiAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := Xi (Levels.Gen.g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1))

/-- The bound ((2Λ)^c)^{|ℛ|} for the number of patterns at the depth j + 1. -/
noncomputable def patternsAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := ((2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c) ^ nRectG (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j)

/-- The cost of the solver at a depth, for all instances within the bounds, but for its calls and
its queries to its tables: `SolverBase` and `SolverStep` at the bounds for λ and B, with |𝓘| ≤
(2λ)^c. -/
noncomputable def solverOwn (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * (2 ^ x₀ + 1)
  | j + 1 => patternsAt ρ c x₀ l lam B j * (xiAt ρ c x₀ l lam B j ^ C * Levels.Gen.K x₀ j ^ Levels.Gen.g x₀ j) + (2 * (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c + 2) * askCost c (lamAt ρ c x₀ l lam B (j + 1)) + xiAt ρ c x₀ l lam B j ^ C

/-- The number of its calls. -/
noncomputable def solverCalls (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => patternsAt ρ c x₀ l lam B j

/-- The number of its queries to its tables. -/
noncomputable def solverAsks (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * 2 ^ x₀
  | _ + 1 => 0

/-- The cost of the solver at the depth j if a call costs tc and a query to its tables tq: own +
calls·tc + queries·tq. -/
noncomputable def solverCost (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ → ℕ → ℕ := Tower.shapeS (solverOwn C ρ c x₀ l lam B) (solverCalls ρ c x₀ l lam B) (solverAsks ρ c x₀ l lam B)

/-- The number of queries to the caller's tables in the procedure for a callee of the depth j, as
bounded by `ProcedureCost` at the bounds for the caller's λ and B: 2^{P⌊2g/K⌋}·Ξ^C. -/
noncomputable def entryAsks (C : ℕ) (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ :=
  2 ^ (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1) * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) * xiAt ρ c x₀ l lam B j ^ C

/-- The rest of its cost: 2^{P⌊2g/K⌋}·Ξ^C·(2^{cΛ} + 2). -/
noncomputable def entryOwn (C : ℕ) (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := entryAsks C ρ c x₀ l lam B j * askCost c (lamAt ρ c x₀ l lam B (j + 1))

/-- The cost of the procedure for a callee of the depth j if a query to the caller's tables costs
tq: own' + queries'·tq. -/
noncomputable def entryCost (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ → ℕ := Tower.shapeI (entryOwn C ρ c x₀ l lam B) (entryAsks C ρ c x₀ l lam B)

/-- One bound for the sizes of the states of the solver and of the procedure and of the contexts, at
all depths: the sum over j ≤ ℓ of (K_j(Λ_j + 𝔅_j))^C. -/
noncomputable def roomAll (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ := ∑ j ∈ range (l + 1), (Levels.Gen.K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C

/-- **The solver and the procedure meet the specification**, for every outermost instance (ℓ, λ, B),
with these costs and sizes, and with the pieces asked only about strings of at most Λ bits, Λ the
largest label length of the recursion. C depends on c only. -/
def RecursionMeets : Prop := ∀ c : ℕ, ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
  (spec D c x₀ (InBounds ρ c x₀ l lam B)).Meets (piecesUpTo D (lamMax ρ c x₀ l lam B)) (PiecesCounted.price c) (solver c x₀) (procedure c) (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B)

/-- How the steps give it. -/
def RecursionMeetsFrom : Prop := SolverBase → SolverStep → ProcedureCost → ChildIsGood → RecursionMeets

/-- The bound on the sizes of the states when the pieces are an oracle: (K_ℓ(λ+B))^{C₀K_ℓ}. The
exponent is C₀K_ℓ, sharper than the C₀K_ℓ² of the printed factor; it is what the tower achieves
(`TotalRoom`). The statements here ask only that the states stay within the printed factor
(`CliqueLevels.SolvesInFactor`), which already keeps the exponent e_ℓK_ℓ²λ; with the sharper bound,
besides, all K·2^{(K−1)λ} entries of the
tables fit into a state only where λ is at most about 2C₀·log(K(λ+B)), and there brute force is
within the printed polynomial factor anyway. -/
noncomputable def sizeBound (x₀ C₀ l lam B : ℕ) : ℝ := ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * Levels.Gen.K x₀ l)

/-- The bound of the theorem: 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²}. (It is
`CliqueLevels.bound (e_ℓ) (K_ℓ) C₀ λ B`.) -/
noncomputable def timeBound (ρ : ℝ) (x₀ C₀ l lam B : ℕ) : ℝ := (2 : ℝ) ^ (Levels.Gen.e ρ x₀ l * (Levels.Gen.K x₀ l : ℝ) ^ 2 * lam) * ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * Levels.Gen.K x₀ l ^ 2)

/-! ### The chain: from one depth to the next, at the bounds for λ and B -/

/-- X_j = K_j(Λ_j + 𝔅_j): the base of the polynomial factor at the depth j. (X_{j+1} is `xiAt … j`.) -/
noncomputable def baseAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := Levels.Gen.K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)

/-- The hypotheses on the numbers, for the arithmetic. -/
structure Numbers (ρ : ℝ) (c x₀ lam B : ℕ) : Prop where
  rho_ge : 1 / 2 ≤ ρ
  rho_lt : ρ < 1
  c_pos : 1 ≤ c
  x₀_ge : 18 ≤ x₀
  x₀_c : c + 5 ≤ 2 ^ x₀
  lam_pos : 1 ≤ lam
  B_pos : 1 ≤ B

/-- «K²L ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K²» and «L ≤ N + 1», for the bounds: 1 ≤ Λ_j ≤ g_j⁴Λ_{j+1} +
1 and K_j²Λ_j ≤ (ρ + 3ζ_j)g_j⁴Λ_{j+1} + (c/4)g_j⁴log(2Λ_{j+1}) + K_j²; also 1 ≤ 𝔅_j. -/
def ChainLabel : Prop := ∀ (ρ : ℝ) (c x₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l →
  1 ≤ lamAt ρ c x₀ l lam B j ∧ 1 ≤ bitsAt ρ c x₀ l lam B j ∧ lamAt ρ c x₀ l lam B j ≤ Levels.Gen.g x₀ j ^ 4 * lamAt ρ c x₀ l lam B (j + 1) + 1 ∧
  (Levels.Gen.K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) +
    (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (Levels.Gen.K x₀ j : ℝ) ^ 2

/-- «K(L + B') ≤ Ξ^{c+5}», for the bounds: X_j ≤ X_{j+1}^{c+5}. -/
def ChainBase : Prop := ∀ (ρ : ℝ) (c x₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l → baseAt ρ c x₀ l lam B j ≤ baseAt ρ c x₀ l lam B (j + 1) ^ (c + 5)

/-- «(c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2», k times: 2^k(c + 5)^kK_{ℓ−k}² ≤ K_ℓ²; and (c + 5)^ℓ ≤ K_ℓ. -/
def ChainLevels : Prop := ∀ c x₀ l k : ℕ, 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → k ≤ l → 2 ^ k * (c + 5) ^ k * Levels.Gen.K x₀ (l - k) ^ 2 ≤ Levels.Gen.K x₀ l ^ 2 ∧ (c + 5) ^ l ≤ Levels.Gen.K x₀ l

/-- The exponents of 2: e_jK_j²Λ_j ≤ e_{j+1}K_{j+1}²Λ_{j+1} − 3K_{j+1}²Λ_{j+1}/K_j +
(c/4)K_{j+1}²log(2Λ_{j+1}) + K_j² (by e_{j+1} = (ρ + 3ζ_j)e_j + 3/K_j and e_j ≤ 1). -/
def ChainExponent : Prop := ∀ (ρ : ℝ) (c x₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l →
  Levels.Gen.e ρ x₀ j * (Levels.Gen.K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j + 3 * ((Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / Levels.Gen.K x₀ j ≤
    Levels.Gen.e ρ x₀ (j + 1) * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) + (c : ℝ) / 4 * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (Levels.Gen.K x₀ j : ℝ) ^ 2

/-- The bound for X_j, from the bounds for Λ_j and the crude bounds. -/
def ChainBaseFrom : Prop := ChainLabel → CrudeBounds → ChainBase
/-- The inequality between the exponents of 2, from the bounds for Λ_j and part (a) of the theorem. -/
def ChainExponentFrom : Prop := ChainLabel → Levels.Gen.PartA → ChainExponent

/-! ### The count -/

/-- The bound of the theorem for the depth j, at the bounds for λ and B. -/
noncomputable def levelBound (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ) : ℝ := timeBound ρ x₀ C₀ j (lamAt ρ c x₀ l lam B j) (bitsAt ρ c x₀ l lam B j)

/-- **«By the induction hypothesis and e ≤ 1, the lemma's 𝒯 may be taken as 𝒯 = 2^{eK²L}(K(L +
B'))^{C₀K²} ≤ 2^{e(ρ+3ζ)N}·Ξ^{cg⁴/4+K²+(c+5)C₀K²}.»** For the bounds: the bound of the theorem for
the depth j, at (Λ_j, 𝔅_j), against the numbers of the depth j + 1, for every C₀. The exponent of 2
is written e_{j+1}N − 3N/K_j, which is e_j(ρ + 3ζ_j)N by e_{j+1} = (ρ + 3ζ_j)e_j + 3/K_j; N =
K_{j+1}²Λ_{j+1} = g_j⁴Λ_{j+1}; cg⁴/4 is the natural number c·(g⁴/4), and 4 divides g⁴. -/
def BoundBelow : Prop := ∀ (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l →
  levelBound ρ c x₀ C₀ l lam B j ≤
    (2 : ℝ) ^ (Levels.Gen.e ρ x₀ (j + 1) * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) - 3 * ((Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / Levels.Gen.K x₀ j) *
      (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * (Levels.Gen.g x₀ j ^ 4 / 4) + Levels.Gen.K x₀ j ^ 2 + (c + 5) * C₀ * Levels.Gen.K x₀ j ^ 2)

/-- How: from the chain. -/
def BoundBelowFrom : Prop := ChainLabel → ChainBase → ChainExponent → BoundBelow

/-- «For ℓ = 0, brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms, each at a cost of at most
(K₀(λ+B))^{C₅}»: the cost of the solver at the depth 0, if a query to its tables costs t ≥ 1, is at
most t times the bound, for every C₀ ≥ 1. -/
def CountBase : Prop := ∀ (C : ℕ) (ρ : ℝ) (c x₀ C₀ l lam B t : ℕ), Numbers ρ c x₀ lam B → 1 ≤ C₀ → 1 ≤ t →
  (solverCost C ρ c x₀ l lam B 0 0 t : ℝ) ≤ t * levelBound ρ c x₀ C₀ l lam B 0

/-- **«So the total number of operations is at most |𝓘|^{|ℛ|}((K^g + 𝒯·2^{2N/K}τ)Ξ^{(c+4)C₁} +
2Ξ^{C₃}) + (2|𝓘| + 2)2^{cλ} + Ξ^{C₃} ≤ Ξ^{cg⁴/4+g+C₄}·𝒯·2^{2N/K+cλ} ≤
2^{e_{ℓ+1}N}·Ξ^{cg⁴/2+g+K²+C₄+(c+5)C₀K²}.»** For the costs of this file: with 𝒯 the bound of the
depth j, a call costs (cost of an entry + 2)·𝒯 + 2 operations if a query to the tables of the
depth j + 1 costs t ≥ 1. C₄ depends on c and C only, not on C₀. -/
def CountStep : Prop := ∀ c C : ℕ, ∃ C₄ : ℕ, ∀ (ρ : ℝ) (x₀ C₀ l lam B j t : ℕ), Numbers ρ c x₀ lam B → j < l → 1 ≤ t →
  (solverOwn C ρ c x₀ l lam B (j + 1) : ℝ) + solverCalls ρ c x₀ l lam B (j + 1) * (((entryCost C ρ c x₀ l lam B j t : ℕ) + 2) * levelBound ρ c x₀ C₀ l lam B j + 2) ≤
    t * ((2 : ℝ) ^ (Levels.Gen.e ρ x₀ (j + 1) * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) *
      (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * Levels.Gen.g x₀ j ^ 4 / 2 + Levels.Gen.g x₀ j + Levels.Gen.K x₀ j ^ 2 + C₄ + (c + 5) * C₀ * Levels.Gen.K x₀ j ^ 2))

/-- **«Since (c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2, the exponent of Ξ is at most (c + C₄ + 1)g⁴ + ½C₀g⁴ ≤ C₀g⁴ =
C₀K_{ℓ+1}² by the choice of C₀.»** -/
def ExponentFits : Prop := ∀ c C₄ C₀ x₀ j : ℕ, 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 2 * (c + C₄ + 1) ≤ C₀ →
  c * Levels.Gen.g x₀ j ^ 4 / 2 + Levels.Gen.g x₀ j + Levels.Gen.K x₀ j ^ 2 + C₄ + (c + 5) * C₀ * Levels.Gen.K x₀ j ^ 2 ≤ C₀ * Levels.Gen.K x₀ (j + 1) ^ 2

/-- The base, from the bounds for Λ_j. -/
def CountBaseFrom : Prop := ChainLabel → CountBase
/-- The step, from the bounds for Λ_j, the bound for 𝒯, and part (a) of the theorem (for e_j ≥ 0). -/
def CountStepFrom : Prop := ChainLabel → BoundBelow → Levels.Gen.PartA → CountStep

/-- **The count**, for the recursion `QueryMachines.Tower.cost` of these costs: for every c and C
there is a C₀ such that the cost of the tower, at one operation for a query to the tables of the
outermost instance, is at most the bound of the theorem. -/
def TotalCount : Prop := ∀ c C : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ l lam B : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 1 ≤ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 1 ≤ lam → 1 ≤ B →
  (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) l 1 : ℝ) ≤ timeBound ρ x₀ C₀ l lam B

/-- By induction on the depth: the cost of the tower at the depth j, if a query costs t ≥ 1, is at
most t times the bound of the depth j. -/
def TotalCountFrom : Prop := CountBase → CountStep → ExponentFits → Tower.CostShape → TotalCount

/-- The sizes of the states of the tower are at most (K_ℓ(λ+B))^{C₀K_ℓ}. (The paper bounds no
memory. The reason: K_j(Λ_j + 𝔅_j) ≤ (K_{j+1}(Λ_{j+1} + 𝔅_{j+1}))^{c+5} by the crude bounds, and (c + 5)^ℓ
≤ K_ℓ.) -/
def TotalRoom : Prop := ∀ c C : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ l lam B : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 1 ≤ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 1 ≤ lam → 1 ≤ B →
  (Tower.towerSize l (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) : ℝ) ≤ sizeBound x₀ C₀ l lam B

/-- How. -/
def TotalRoomFrom : Prop := ChainBase → ChainLevels → TotalRoom

/-- The room of the algorithm of the pieces, at the largest label length of the recursion, is within
the bound of the theorem. (The reason: c ≤ K_j ≤ e_jK_j², so 2^{cΛ_j} ≤ 2^{e_jK_j²Λ_j}, and the
bound of the level j at (Λ_j, 𝔅_j) is at most that of the level j + 1 at (Λ_{j+1}, 𝔅_{j+1}), as in
the printed display for 𝒯; the other factors of the room are polynomial in Λ_j.) -/
def RoomIsWithinTheBound : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ l lam B : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 1 ≤ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 1 ≤ lam → 1 ≤ B →
  (PiecesCounted.room c (lamMax ρ c x₀ l lam B) : ℝ) ≤ timeBound ρ x₀ C₀ l lam B

/-- From the bounds for Λ_j, the bound for 𝒯 with the sentence on the exponent of Ξ (so the bound of
a depth is at most that of the next), the inequalities between the K_j, and part (a) of the theorem
(for c ≤ e_jK_j²). -/
def RoomIsWithinTheBoundFrom : Prop := ChainLabel → BoundBelow → ChainLevels → ExponentFits → Levels.Gen.PartA → RoomIsWithinTheBound

/-! ## 5. The theorem -/

/-- The solver and the procedure have polynomial-time steps: one certificate each, for all levels. -/
def RecursionPoly : Prop := ∀ c x₀ : ℕ, (solver c x₀).PolyTimeSteps ∧ (procedure c).PolyTimeSteps

/-- So the one machine has. -/
def RecursionPolyFrom : Prop := Tower.TowerPoly → RecursionPoly → ∀ c x₀ : ℕ, (recursion c x₀).PolyTimeSteps

/-- **Theorem A (b), with the pieces as an oracle at 2^{cλ'} + 2 operations a query**: the pieces
are asked only about strings of at most Λ bits, Λ the largest label length of the recursion. -/
def RecursionCountedUpTo : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B →
  (∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, (recursion c x₀).Within (Sum.elim (answersOf (Levels.Gen.K x₀ l) lam W) (piecesUpTo D (lamMax ρ c x₀ l lam B))) (upPrices c 1) (top l lam B) T S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) ∧
      (T : ℝ) ≤ timeBound ρ x₀ C₀ l lam B ∧ (S : ℝ) ≤ sizeBound x₀ C₀ l lam B

/-- How the steps give the theorem. -/
def RecursionCountedUpToFrom : Prop := RecursionMeets → TotalCount → TotalRoom → Tower.TowerRuns → RecursionCountedUpTo
/-- **Theorem A (b), with the pieces computed by their algorithm.** For pieces WITH their algorithm
(all of Definition 7): the machine `recursionWith c x₀ Alg` has query access to the tables alone, at
one operation for a query. It outputs the value within three times the bound (a query that is passed
on costs 2 operations more); its states are larger by the room of Alg at Λ, the largest label length
of the recursion. That room is about 2^{cΛ}: so a Turing machine that carries this machine out has
the exponent of the bound only up to a constant factor, where `RecursionCountedUpTo` keeps it
exactly, relative to the oracle. -/
def RecursionPlugged : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped PieceQuery Ans), PiecesCounted.IsPieces ρ c D Alg → Setting ρ c x₀ D → ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B →
  (∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, (recursionWith c x₀ Alg).Within (answersOf (Levels.Gen.K x₀ l) lam W) (fun _ => 1) (top l lam B) T S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) ∧
      (T : ℝ) ≤ 3 * timeBound ρ x₀ C₀ l lam B ∧ (S : ℝ) ≤ 2 * sizeBound x₀ C₀ l lam B + PiecesCounted.room c (lamMax ρ c x₀ l lam B)

/-- How: the price of a query to the tables is raised from 1 to 3 (`PricesScale`), and then the
queries to the pieces are answered by the algorithm (`PiecesCounted.OracleFromAlgorithm`). -/
def RecursionPluggedFrom : Prop := RecursionCountedUpTo → PricesScale → PiecesCounted.OracleFromAlgorithm → RecursionPlugged

/-- Given an algorithm for the pieces with polynomial-time steps, the machine with that algorithm
built in, and the algorithm of the theorem (`cliqueMachine`), have polynomial-time steps. -/
def RecursionWithPoly : Prop := ∀ (c x₀ : ℕ) (Alg : Stepped PieceQuery Ans), Nonempty (IsPolyT Alg) → (recursionWith c x₀ Alg).PolyTimeSteps ∧ (cliqueMachine c x₀ Alg).PolyTimeSteps

/-- How: from the certificate of the one machine for all levels. -/
def RecursionWithPolyFrom : Prop := (∀ c x₀ : ℕ, (recursion c x₀).PolyTimeSteps) → RecursionWithPoly

/-- **Theorem A (b)**, in the ONE form that is also the hypothesis of Theorem D (a)
(`CliqueLevels.Solves`): «One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to
tables with |W_w| < 2^B, outputs the value of the (K_ℓ, λ)-clique within
2^{e_ℓK_ℓ²λ}(K_ℓ(λ+B))^{C₀K_ℓ²} operations», on states of at most that size. C₀ depends on c only.
(The states hold the room of the algorithm of the pieces; see `RecursionPlugged`.) -/
def RecursionSolves : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped PieceQuery Ans), PiecesCounted.IsPieces ρ c D Alg → Setting ρ c x₀ D →
  (cliqueMachine c x₀ Alg).PolyTimeSteps ∧ CliqueLevels.Solves (cliqueMachine c x₀ Alg) (Levels.Gen.K x₀) (Levels.Gen.e ρ x₀) C₀

/-- How. -/
def RecursionSolvesFrom : Prop := RecursionPlugged → RoomIsWithinTheBound → ReadAsRuns → RecursionWithPoly → RecursionSolves

end ExplicitCost
