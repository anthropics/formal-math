/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.Kernel
public import QueryMachines.CombDefs
public import QueryMachines.CombRunsStatement
public import QueryMachines.Comb
public import PiecesFromEightSquaresStatement

/-! # Pieces with parameters (ρ, c), with «one algorithm … within 2^{cλ} operations»

Definitions and statements only (no theorem, no proof). What an operation is:
proof/machines/QueryMachines/Kernel.lean. Imports proof/machines/QueryMachines/Comb.lean (theorems
on the constructions of proof/machines/QueryMachines/; it holds no definition) and
`PiecesFromEightSquaresStatement.lean` (and through it `AppRunningTimeStatement.lean`,
`AppHalfPiecesStatement.lean`, `PiecesStatement.lean`).

## The sentences of the paper that are stated here

* Definition 7: «Pieces with parameters (ρ, c) consist, for every λ ≥ 1, of an integer d ≥ 1, a
  finite set 𝓘 of integers and functions A_i : ({0,1}^λ)⁴ → ℤ, i ∈ 𝓘, such that: (a) … (b) … (c) |𝓘|
  ≤ (2λ)^c; the number d, the elements of 𝓘 and all values of the A_i and of the functions of these
  factorizations are below
  2^{(2λ)^c} in absolute value; and one algorithm computes each of them, and 𝓘, c^row_i, c^col_i,
  from λ, i and the arguments within 2^{cλ} operations.» This is `IsPieces`, `Exist`.
* After Definition 7: «By Lemma 2, the functions A_0, …, A_t of Definition 5 are pieces with
  parameters (11/12, c) … for every integer c ≥ 8 such that 2^{cλ} exceeds the polynomial running
  times in Lemma 2 for all λ ≥ 1» (`EightSquarePieces`); «We may and do assume c^row_i, c^col_i ≤ 2λ
  … (and c by c + 2 …)» (`MayAssume`).
* Theorem B: «There are pieces with parameters (1/√2, c), for an absolute constant c»
  (`HalfPieces`).

## How to read it

* `Data`: for every λ the integer d, the finite set 𝓘 of integers, the functions A_i and the numbers
  c^row_i, c^col_i (`Pieces.Family λ` of `PiecesStatement.lean`), and the four functions of the two
  factorizations of each A_i. `Data.Is ρ c`: clauses (a), (b) and the sizes of (c).
* `Question`, `Answer`, `Data.answer`: what the one algorithm is asked and what it has to return: d;
  the list of 𝓘, in increasing order; c^row_i or c^col_i; A_i(x, y, u, v); a value of one of the
  four functions. A question about an i outside 𝓘, or with strings of the wrong length, has no
  answer, and nothing is asked of the algorithm there.
* «One algorithm»: ONE step machine `Alg` (`Groundwork.Stepped`) with polynomial-time steps, whose
  input is λ in unary and the question. «Within 2^{cλ} operations»: it halts with the answer within
  2^{cλ} steps.
* An operation is a step of a machine whose steps are polynomial-time in the size of the state, so a
  number of operations means something only with a bound on the sizes of the states (head of
  proof/machines/QueryMachines/Kernel.lean). Here the bound is `room c λ` = (2^{cλ} + (2λ)^c + 8)·((2λ)^c + 8):
  room for as many numbers as there are
  operations or elements of 𝓘, each of the size that (c) allows, with a little to spare for the
  question. This is the case «S is exponential in a parameter» of that head. The number of steps
  alone bounds little: a state can grow to this size in few steps, and one step can then do work
  polynomial in it. So the clause amounts
  to: a Turing machine answers within 2^{O(λ)} steps, where the O depends on c and on the degree of
  the certificate of Alg. This costs nothing where c is only said to exist (Theorem B, Lemma 2's
  pieces) and nothing where the pieces are an oracle; but «the same c» as for operations on words is
  not what it says.
* `Data.oracle`, `price`: the pieces as an oracle whose query (λ, question) costs 2^{cλ} + 2
  operations: those of the algorithm, and two for handing over the question and taking the answer,
  which is what the cost model of proof/machines/QueryMachines/Kernel.lean charges when a query is
  answered by running a machine. This is the form in which
  the proof of Theorem A (b) uses the pieces: its networks, to which Lemma 8 is applied, ask them.
  `OracleFromAlgorithm` is the step from the oracle to the algorithm.

## Where these statements differ from the printed sentences

* Steps of a step machine, with the bound on the sizes of its states, in place of operations of a
  word RAM; λ in unary; strings as lists of bits.
* `AppRunningTime.IsPieces` (`AppRunningTimeStatement.lean`) renders the last clause of (c) by a
  padding string, has six programs in place of one algorithm, and numbers 𝓘 from 0. `FromPadded` is
  the step from there to here; it changes c. Its algorithm writes the padding string, one unit in
  each step, and then does the work in a single
  step: the extreme case (3) of the head of proof/machines/QueryMachines/Kernel.lean. It is honest
  only because `room` is in the statement. So Theorem B in this form says of the running time what
  `AppRunningTime.ThmHalfPieces` says, in other words; the procedures of «Sizes and operations» are
  not run step by step. -/

@[expose] public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog

/-! ### The data, and clauses (a), (b) and the sizes of (c) -/

/-- For every λ: d, 𝓘, the A_i, c^row_i, c^col_i (`fam λ`), and the functions of the factorizations:
`fn λ tr side i z θ`, where tr = false is the factorization as a function of (x, y) and (u, v) and
tr = true that as a function of (x, u) and (y, v); side = false is the function of the first pair
and side = true that
of the second; z is the pair of strings and θ the string of shared bits. -/
structure Data where
  fam : (lam : ℕ) → Pieces.Family lam
  fn : (lam : ℕ) → Bool → Bool → ℤ → Pieces.Bits lam × Pieces.Bits lam → List Bool → ℤ

/-- c^row_i (tr = false) or c^col_i (tr = true). -/
def Data.cap (D : Data) (lam : ℕ) (tr : Bool) (i : ℤ) : ℕ := if tr then (D.fam lam).ccol i else (D.fam lam).crow i

/-- Definition 7 without its last clause. -/
structure Data.Is (D : Data) (ρ : ℝ) (c : ℕ) : Prop where
  /-- ½ ≤ ρ < 1 real, c ≥ 1 an integer, d ≥ 1 -/
  rho_ge : 1 / 2 ≤ ρ
  rho_lt : ρ < 1
  c_pos : 1 ≤ c
  d_pos : ∀ lam, 1 ≤ lam → 1 ≤ (D.fam lam).d
  /-- (a) Σ_{i ∈ 𝓘} A_i = d·[x = v][y = u] -/
  sum : ∀ lam, 1 ≤ lam → ∀ x y u v, ∑ i ∈ (D.fam lam).I, (D.fam lam).A i x y u v = (D.fam lam).d * Pieces.cross x y u v
  /-- (b) A_i factors through c^row_i bits as a function of (x, y) and (u, v) -/
  row : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ x y u v, (D.fam lam).A i x y u v = ∑ θ ∈ words (D.cap lam false i), D.fn lam false false i (x, y) θ * D.fn lam false true i (u, v) θ
  /-- (b) and through c^col_i bits as a function of (x, u) and (y, v) -/
  col : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ x y u v, (D.fam lam).A i x y u v = ∑ θ ∈ words (D.cap lam true i), D.fn lam true false i (x, u) θ * D.fn lam true true i (y, v) θ
  /-- (b) where c^row_i + c^col_i ≤ 4ρλ + c·log(2λ) -/
  caps : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ((D.cap lam false i + D.cap lam true i : ℕ) : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  /-- (c) |𝓘| ≤ (2λ)^c -/
  card : ∀ lam, 1 ≤ lam → #(D.fam lam).I ≤ (2 * lam) ^ c
  /-- (c) d, the elements of 𝓘 and all values of the A_i and of the functions of these
      factorizations are below 2^{(2λ)^c} in absolute value -/
  size_d : ∀ lam, 1 ≤ lam → (D.fam lam).d < 2 ^ (2 * lam) ^ c
  size_I : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, |i| < 2 ^ (2 * lam) ^ c
  size_A : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ x y u v, |(D.fam lam).A i x y u v| < 2 ^ (2 * lam) ^ c
  size_f : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ tr side z, ∀ θ ∈ words (D.cap lam tr i), |D.fn lam tr side i z θ| < 2 ^ (2 * lam) ^ c

/-! ### The last clause of (c): one algorithm -/

/-- What the algorithm is asked, beside λ: d; 𝓘; (tr, i): c^row_i or c^col_i; (i, (x, y, u, v)):
A_i(x, y, u, v); ((tr, side), i, (z₁, z₂, θ)): a value of one of the four functions. -/
abbrev Question : Type := Unit ⊕ (Unit ⊕ ((Bool × ℤ) ⊕ ((ℤ × (List Bool × List Bool × List Bool × List Bool)) ⊕ ((Bool × Bool) × ℤ × (List Bool × List Bool × List Bool)))))

/-- An answer: an integer, or (for 𝓘) a list of integers. -/
abbrev Answer : Type := ℤ ⊕ List ℤ

/-- A list of bits as a string of n bits. -/
def toBits (n : ℕ) (l : List Bool) : Pieces.Bits n := fun j => l.getD j.val false

/-- The right answer for the strings of λ bits. A question about an i outside 𝓘, or with strings of
the wrong length, has none. -/
def Data.answer (D : Data) (lam : ℕ) : Question → Option Answer
  | .inl _ => some (.inl (D.fam lam).d)
  | .inr (.inl _) => some (.inr (D.fam lam).I.sort)
  | .inr (.inr (.inl q)) => if q.2 ∈ (D.fam lam).I then some (.inl (D.cap lam q.1 q.2)) else none
  | .inr (.inr (.inr (.inl q))) =>
    if q.1 ∈ (D.fam lam).I ∧ q.2.1.length = lam ∧ q.2.2.1.length = lam ∧ q.2.2.2.1.length = lam ∧ q.2.2.2.2.length = lam then
      some (.inl ((D.fam lam).A q.1 (toBits lam q.2.1) (toBits lam q.2.2.1) (toBits lam q.2.2.2.1) (toBits lam q.2.2.2.2))) else none
  | .inr (.inr (.inr (.inr q))) =>
    if q.2.1 ∈ (D.fam lam).I ∧ q.2.2.1.length = lam ∧ q.2.2.2.1.length = lam ∧ q.2.2.2.2.length = D.cap lam q.1.1 q.2.1 then
      some (.inl (D.fn lam q.1.1 q.1.2 q.2.1 (toBits lam q.2.2.1, toBits lam q.2.2.2.1) q.2.2.2.2)) else none

/-- The pieces as an oracle: the query is (λ in unary, question), λ ≥ 1. -/
def Data.oracle (D : Data) (g : List Unit × Question) : Option Answer := if 1 ≤ g.1.length then D.answer g.1.length g.2 else none

/-- The number of operations that (c) allows for strings of λ bits: 2^{cλ}. -/
def steps (c lam : ℕ) : ℕ := 2 ^ (c * lam)

/-- The price of a query to the pieces as an oracle: 2^{cλ} operations, and two for handing over the
question and taking the answer. -/
def price (c : ℕ) (g : List Unit × Question) : ℕ := steps c g.1.length + 2

/-- The bound on the sizes of the states of the algorithm: (2^{cλ} + (2λ)^c + 8)·((2λ)^c + 8). -/
def room (c lam : ℕ) : ℕ := (2 ^ (c * lam) + (2 * lam) ^ c + 8) * ((2 * lam) ^ c + 8)

/-- «One algorithm computes each of them, and 𝓘, c^row_i, c^col_i, from λ, i and the arguments
within 2^{cλ} operations.» -/
def Computes (Alg : Stepped (List Unit × Question) Answer) (D : Data) (c : ℕ) : Prop :=
  ∀ (g : List Unit × Question) (a : Answer), D.oracle g = some a → Alg.Runs g (steps c g.1.length) (room c g.1.length) a

/-- **Definition 7.** D, with the algorithm Alg, are pieces with parameters (ρ, c). -/
structure IsPieces (ρ : ℝ) (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer) : Prop where
  is : D.Is ρ c
  polyTimeSteps : Nonempty (IsPolyT Alg)
  computes : Computes Alg D c

/-- «There are pieces with parameters (ρ, c).» -/
def Exist (ρ : ℝ) (c : ℕ) : Prop := ∃ D Alg, IsPieces ρ c D Alg

/-- Clauses (a), (b) and the sizes of (c) as pure mathematics (`Pieces.Family.Is`) follow. -/
def ToPure : Prop := ∀ (D : Data) (ρ : ℝ) (c : ℕ), D.Is ρ c → ∀ lam, 1 ≤ lam → (D.fam lam).Is ρ c

/-- The bound of (b) only weakens when ρ or c grows, and so do the sizes and the number of
operations: pieces with parameters (ρ, c) are pieces with parameters (ρ', c') for ρ ≤ ρ' < 1 and c ≤
c'. -/
def GrowWithTheParameters : Prop := ∀ (ρ ρ' : ℝ) (c c' : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), ρ ≤ ρ' → ρ' < 1 → c ≤ c' → IsPieces ρ c D Alg → IsPieces ρ' c' D Alg

/-! ### From the oracle to the algorithm -/

/-- The machine that answers a query of either kind: a query of the first kind is asked again and
its answer handed back; a query to the pieces is answered by running Alg. -/
def passOrRun {Q : Type} [HasSize Q] (Alg : Stepped (List Unit × Question) Answer) : QueryMachines.QueryMachine Q Answer (Unit × (Q ⊕ (List Unit × Question))) Answer :=
  QueryMachines.QueryMachine.branch (fun p : Unit × (Q ⊕ (List Unit × Question)) => p.2) (QueryMachines.QueryMachine.query id) (QueryMachines.QueryMachine.lift Alg)

/-- M with the queries to the pieces answered by running Alg. -/
def withAlgorithm {Q α β : Type} [HasSize Q] (M : QueryMachines.QueryMachine (Q ⊕ (List Unit × Question)) Answer α β) (Alg : Stepped (List Unit × Question) Answer) : QueryMachines.QueryMachine Q Answer α β :=
  QueryMachines.QueryMachine.mapIn (fun a : α => ((), a)) (M.subst (passOrRun Alg))

/-- From the oracle to the algorithm. Let M be any machine with two kinds of queries, of which the
second are queries to the pieces, and let it ask the pieces only for strings of at most Λ bits. If M
returns b within T operations when the pieces are an oracle at the prices `price c` and a query x of
the first kind
costs w x + 2, then `withAlgorithm M Alg` returns b within T operations when x costs w x. Its states
are larger by the room of the algorithm at Λ and by the size S_Q of a query of the first kind with
its answer. -/
def OracleFromAlgorithm : Prop := ∀ (Q α β : Type) [HasSize Q] (M : QueryMachines.QueryMachine (Q ⊕ (List Unit × Question)) Answer α β) (Alg : Stepped (List Unit × Question) Answer) (D : Data) (c : ℕ),
  Computes Alg D c → ∀ (O : Q → Option Answer) (w : Q → ℕ) (a : α) (T S Λ SQ : ℕ) (b : β), (∀ x v, O x = some v → size x + size v ≤ SQ) →
    M.Within (Sum.elim O fun g => if g.1.length ≤ Λ then D.oracle g else none) (Sum.elim (fun x => w x + 2) (price c)) a T S b →
      (withAlgorithm M Alg).Within O w a T (S + room c Λ + SQ + 4) b

/-! ### From the padding string -/

/-- The data that belong to pieces in the sense of `AppRunningTime.IsPieces`, for a padding string
of 2^{cλ} units: 𝓘 = {0, …, cnt − 1} shifted by `shift λ`. -/
def ofPadded (P : ClauseBound.Alg.PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (c : ℕ) (shift : ℕ → ℤ) : Data where
  fam lam :=
    { d := P.d 0 lam
      I := (range (P.cnt 0 lam)).image fun i : ℕ => (i : ℤ) + shift lam
      A := fun i => A lam (i - shift lam).toNat
      crow := fun i => P.cap false 0 lam (i - shift lam).toNat
      ccol := fun i => P.cap true 0 lam (i - shift lam).toNat }
  fn lam tr side i z θ :=
    if side then P.bot ((List.replicate (2 ^ (c * lam)) (), tr), (0, (i - shift lam).toNat), (ClauseBound.Alg.bitsOf z.1, ClauseBound.Alg.bitsOf z.2, θ))
    else P.top ((List.replicate (2 ^ (c * lam)) (), tr), (0, (i - shift lam).toNat), (ClauseBound.Alg.bitsOf z.1, ClauseBound.Alg.bitsOf z.2, θ))

/-- From the padding string to counted operations. Pieces with parameters (ρ, c) in the sense of
`AppRunningTime.IsPieces` are, with a larger constant c', pieces in the sense of this file, for
every shift of the index set that is computed in polynomial time from λ in unary and is below
2^{(2λ)^c} − (2λ)^c in absolute value. The
algorithm writes the padding string, one unit in each step, and then runs the program that is asked
for in one step. -/
def FromPadded : Prop := ∀ (ρ : ℝ) (c : ℕ) (P : ClauseBound.Alg.PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ) (shift : ℕ → ℤ), AppRunningTime.IsPieces ρ c P A val →
  PolyT (fun u : List Unit => shift u.length) → (∀ lam, 1 ≤ lam → |shift lam| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c) →
    ∃ (c' : ℕ) (Alg : Stepped (List Unit × Question) Answer), c ≤ c' ∧ IsPieces ρ c' (ofPadded P A c shift) Alg

/-! ### The sentences after Definition 7 -/

/-- «We may and do assume c^row_i, c^col_i ≤ 2λ: … a longer factorization is replaced by this one
(and c by c + 2, which pays for computing c^row_i or c^col_i first).» Pieces with parameters (ρ, c)
give pieces with parameters (ρ, c + 2) with the same d, 𝓘 and A_i and with all numbers of bits at
most 2λ. -/
def MayAssume : Prop := ∀ (ρ : ℝ) (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), IsPieces ρ c D Alg →
  ∃ (D' : Data) (Alg' : Stepped (List Unit × Question) Answer), IsPieces ρ (c + 2) D' Alg' ∧
    ∀ lam, (D'.fam lam).d = (D.fam lam).d ∧ (D'.fam lam).I = (D.fam lam).I ∧ (D'.fam lam).A = (D.fam lam).A ∧ ∀ tr i, D'.cap lam tr i ≤ 2 * lam

/-- «By Lemma 2, the functions A_0, …, A_t of Definition 5 are pieces with parameters (11/12, c),
with 𝓘 = {0, …, t}, d = 2^t and the numbers c^row_i, c^col_i defined there … This holds for every
integer c ≥ 8 such that 2^{cλ} exceeds the polynomial running times in Lemma 2 for all λ ≥ 1.» There
is ONE algorithm, and a
number c₀ ≥ 8, such that for every c ≥ c₀ the data made from Lemma 2's functions, with this
algorithm, are pieces with parameters (11/12, c); and these data are as the sentence says. (The
programs of Lemma 2's functions do not read the padding string, so `ofPadded` is taken with c = 0
there, a padding string of one unit. They are
polynomial-time, so the algorithm need not count operations: it writes that one unit and answers in
the next step, two steps in all, and c₀ comes from the sizes alone.) -/
def EightSquarePieces : Prop := (∃ (c₀ : ℕ) (Alg : Stepped (List Unit × Question) Answer), 8 ≤ c₀ ∧ ∀ c : ℕ, c₀ ≤ c → IsPieces (11 / 12) c (ofPadded Eight.eightF Eight.A 0 fun _ => 0) Alg) ∧
  ∀ lam, 1 ≤ lam → ((ofPadded Eight.eightF Eight.A 0 fun _ => 0).fam lam).I = Finset.Icc 0 (Eight.tOf lam : ℤ) ∧ ((ofPadded Eight.eightF Eight.A 0 fun _ => 0).fam lam).d = 2 ^ Eight.tOf lam ∧
    ∀ i : ℕ, i ≤ Eight.tOf lam → ((ofPadded Eight.eightF Eight.A 0 fun _ => 0).fam lam).A i = Eight.A lam i ∧
      (ofPadded Eight.eightF Eight.A 0 fun _ => 0).cap lam false i = Eight.crow lam i ∧ (ofPadded Eight.eightF Eight.A 0 fun _ => 0).cap lam true i = Eight.ccol lam i ∧
      ((Eight.crow lam i + Eight.ccol lam i : ℕ) : ℝ) ≤ 11 * lam / 3 + 8

/-! ### Theorem B -/

/-- **Theorem B**, for the functions of its proof: there are pieces with parameters (1/√2, c), for
an absolute constant c, namely, with h = `AppHalfPieces.hOf λ` and μ(x) the partition of h with
number x in the lexicographic list: 𝓘 = {−2h, …, 2h}, d = h!, A_s = `AppHalfPieces.piece`, c^row_s =
⌈log R^row_s⌉ and c^col_s = ⌈log R^col_s⌉. -/
def HalfPieces : Prop := ∃ (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), IsPieces (1 / Real.sqrt 2) c D Alg ∧
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    (D.fam lam).I = Finset.Icc (-(2 * (AppHalfPieces.hOf lam : ℤ))) (2 * (AppHalfPieces.hOf lam : ℤ)) ∧ (D.fam lam).d = (AppHalfPieces.hOf lam).factorial ∧
    ∀ s ∈ (D.fam lam).I, (∀ x y u v, ((D.fam lam).A s x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu s x y u v) ∧
      D.cap lam false s = Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) s) ∧ D.cap lam true s = Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) s)

/-- Theorem B in the paper's words. -/
def HalfPiecesExist : Prop := ∃ c : ℕ, Exist (1 / Real.sqrt 2) c

/-- The step: Theorem B in this form, from Theorem B with the padding string
(`AppRunningTime.ThmHalfPieces`) and `FromPadded`, with the index set shifted by −2h. -/
def HalfPiecesFrom : Prop := AppRunningTime.ThmHalfPieces → FromPadded → HalfPieces

end PiecesCounted
