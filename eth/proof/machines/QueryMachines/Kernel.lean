/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.PolyT

/-! # Machines with query access: own steps and queries are counted (definitions and statements only)

Section 3 of the paper counts time in «operations: operations on words … and table queries», and
Definition 3 says of the tables of a clique: «an algorithm queries them by naming w and z_w ∈ S_w,
and receives W_w(z_w) at the cost of one operation».
The step machines of this development (`Groundwork.Stepped`,
proof/statements/StepMachineStatements.lean) have no way to ask: without this file the number of
queries is not a notion.
This file adds the notion. A `QueryMachine` is a step machine with two more fields: `ask` (in this
state the machine waits for the answer to this query) and `resume` (the state after the answer has
come).
* `Reaches`, `Runs`: the run against an oracle, with the number of own steps and THE LIST OF THE
  QUERIES ASKED, in order.
* `Within`: the cost of a run when the query x costs w x operations. With w = 1 this is the unit of
  cost of Definitions 3 and 4; with w = τ it is Definition 2(iii).
* `close`: the oracle built in, one step per query: a step machine of this development. `plug`: each
  query answered by running a step machine. `subst`: each query answered by running a machine that
  has query access of its own («Answer each of its … queries by computing the entry», proof of Lemma 1).
* `IsPolyQ`: all five functions of the machine are computed in polynomial time.
The statements `St…` at the end are what proof/machines/QueryMachines/ proves about these notions;
all bounds in them are explicit (no unnamed constant).

**What an operation is here, and what a number of operations can hide.** One operation is one
application of `step`, or one query. `step` may be any function that a Turing machine computes in
time polynomial in the length of the word of the state (`IsPolyQ`). The encoding of the states is
chosen with the proof of `IsPolyQ` and need not determine the state. This hides nothing: the machine
is deterministic, so the word of the next state, of a query and of the result depend only on the
word of the state; the words of queries and results determine them (true of the encodings of
proof/machines/ToTuring/Enc.lean for every type used here), so whatever a state holds beyond its
word cannot affect the queries or the result, and `Carried` makes the word at most 7 times the size.
`init`, `out`, `ask` and `resume` are not counted as operations; each is computed in polynomial time
in the length of its argument (`IsPolyQ`), and `exists_tmW` counts `init` and `out`. So one
operation may read and rewrite the whole state, where an operation
of the paper's word RAM touches a bounded number of words. For this reason a number T of operations
means something only together with the bound S on the sizes of all states, and every statement
carries S. What the pair (T, S) can hide is bounded, for step machines on bit strings with a bit
string as result, by a theorem of this development (`CountKSat.exists_tmW`,
proof/consequences/CountKSat/Host.lean):
if the machine has polynomial-time steps and halts within T steps on states of size at most S, ONE
Turing machine of Mathlib does the same within q·(T + 1)·(|x| + S + 1)^q steps, where q depends on
the machine and not on the input: linear in T. It applies to a machine of this file once its queries
are answered by polynomial-time computation (`StPolyClose`, `StPolyPlug`)
and its input and result are written as bit strings. It does not apply to a machine whose oracle is
an arbitrary table (Definitions 3 and 4, Lemma 1); for these the same bound, for a Turing machine
with an oracle, is an argument outside Lean. In the other direction: T operations of a word RAM on a
memory of S bits are T operations here on states of size O(S) (an argument outside Lean).
So an algorithm whose memory is polynomial loses nothing; for one with more memory, this translation
gives no polynomial S. Three cases follow.
(1) S is polynomial in the quantity whose powers the printed bound leaves unnamed: B + λ in
    Definition 4, P + B in Lemma 1. The paper prints no bound on memory there; a bound S = C·(B +
    λ)^C, or S = C₁·(P + B)^{C₁}, on the sizes of the states is a condition that the paper does not
    state. With it the hidden factor is of the kind that the printed bound contains already, and the
    Lean statement gives the printed sentence with a larger unnamed constant.
(2) S is exponential in a parameter. Then T operations may stand for T·2^{O(parameter)} operations
    on words, and a printed bound 2^{c·parameter} follows only with a larger c. No statement of
    proof/machines/QueryMachines/ is of this kind; a statement of Definition 7 (c) in this model
    would be, and would have to say so.
(3) The extreme: a machine may write T units in T operations and then do work polynomial in T in a
    single operation. Nothing in the model forbids this; what shows that a given statement does not
    do it is its S.
A function with a certificate of polynomial time that is to be charged with more than one operation
can be treated as a query priced by `w` and built in at the end (`plug`, `close`).
This file has no proofs. -/

@[expose] public section

namespace QueryMachines

open Groundwork

variable {Q A Q' A' C α β : Type}

/-! ## The machine -/

/-- A step machine with query access. Q is the type of queries, A the type of answers. A state s is
read in this order: if `out s = some b` the machine has halted with the result b; else, if
`ask s = some x`, it asks the query x, and goes on in the state `resume s v`
once it has received the answer v; else it makes the step of its own `step s`. The fields σ, init,
step, out and the measure of size are those of `Groundwork.Stepped`. -/
structure QueryMachine (Q A α β : Type) : Type 1 extends Stepped α β where
  ask : σ → Option Q
  resume : σ → A → σ

namespace QueryMachine

/-! ## Runs against an oracle -/

/-- From the state s, with the oracle O: the machine halts with the result b after at most `own`
steps of its own; L is the list of the queries that it asks, in order; all states have size at most
S.
`O x = none` says that x is not a query that the oracle answers: a machine that asks such an x has
no run. So a run also says that every query asked was a legitimate one. -/
inductive Reaches (M : QueryMachine Q A α β) (O : Q → Option A) (S : ℕ) (b : β) : M.σ → ℕ → List Q → Prop
  | halt {s : M.σ} {own : ℕ} : M.out s = some b → size s ≤ S → Reaches M O S b s own []
  | step {s : M.σ} {own : ℕ} {L : List Q} : M.out s = none → M.ask s = none → size s ≤ S → Reaches M O S b (M.step s) own L →
      Reaches M O S b s (own + 1) L
  | query {s : M.σ} {own : ℕ} {L : List Q} {x : Q} {v : A} : M.out s = none → M.ask s = some x → O x = some v → size s ≤ S →
      Reaches M O S b (M.resume s v) own L → Reaches M O S b s own (x :: L)

/-- On the input a, with the oracle O: the result is b, after at most `own` own steps and exactly
the queries L, on states of size at most S. -/
def Runs (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (own : ℕ) (L : List Q) (S : ℕ) (b : β) : Prop := M.Reaches O S b (M.init a) own L

/-- On the input a, with the oracle O, **if the query x costs w x operations**: the result is b
within T operations (own steps plus the costs of the queries asked), on states of size at most S. -/
def Within (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (a : α) (T S : ℕ) (b : β) : Prop :=
  ∃ (own : ℕ) (L : List Q), M.Runs O a own L S b ∧ own + (L.map w).sum ≤ T

/-- The same from a state s. -/
def WithinFrom (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (s : M.σ) (T S : ℕ) (b : β) : Prop :=
  ∃ (own : ℕ) (L : List Q), M.Reaches O S b s own L ∧ own + (L.map w).sum ≤ T

/-- «At the cost of one operation» (Definition 3). -/
def unitCost : Q → ℕ := fun _ => 1

/-! ## Three ways to answer the queries -/

/-- The oracle built in: a step machine of this development in which a query is answered in one
step. (At a query that the oracle does not answer the machine stays where it is, and so never
halts.) -/
def close (M : QueryMachine Q A α β) (O : Q → Option A) : Stepped α β where
  σ := M.σ
  sz := M.sz
  init := M.init
  step s := match M.ask s with
    | some x => (match O x with | some v => M.resume s v | none => s)
    | none => M.step s
  out := M.out

/-- Each query x is answered by running the step machine R on (c, x); c is a context, handed over
with the input and kept to the end: it stands for whatever the caller holds in memory. A query costs
the steps of R and two more (to start R, to take its result). -/
def plug [HasSize C] (M : QueryMachine Q A α β) (R : Stepped (C × Q) A) : Stepped (C × α) β where
  σ := C × (M.σ ⊕ (M.σ × R.σ))
  init x := (x.1, .inl (M.init x.2))
  step s := match s.2 with
    | .inl m => (match M.ask m with
      | some x => (s.1, .inr (m, R.init (s.1, x)))
      | none => (s.1, .inl (M.step m)))
    | .inr p => (match R.out p.2 with
      | some v => (s.1, .inl (M.resume p.1 v))
      | none => (s.1, .inr (p.1, R.step p.2)))
  out s := match s.2 with | .inl m => M.out m | .inr _ => none

/-- «Answer each of its … queries by computing the entry» (proof of Lemma 1): each query x of M is
answered by running N on (c, x), where N has query access of its own, to another oracle. The step
machine underneath is `plug M N.toStepped`; the queries of the new machine are those that N asks. -/
def subst [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) : QueryMachine Q' A' (C × α) β where
  toStepped := M.plug N.toStepped
  ask := fun (s : C × (M.σ ⊕ (M.σ × N.σ))) => match s.2 with
    | .inl _ => none
    | .inr p => (match N.out p.2 with | some _ => none | none => N.ask p.2)
  resume := fun (s : C × (M.σ ⊕ (M.σ × N.σ))) v => match s.2 with
    | .inl _ => s
    | .inr p => (s.1, .inr (p.1, N.resume p.2 v))

/-! ## Polynomial-time steps -/

/-- Every part of the machine is computed in polynomial time (`Groundwork.PolyT`: on Mathlib's
multi-stack Turing machines), and the words of its states are at most linear in their size:
`Groundwork.IsPolyT` with the two new fields. The class holds data (the encoding of the states), so
statements say `PolyTimeSteps`. -/
class IsPolyQ [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) where
  [enc : Enc M.σ]
  [carried : Carried M.σ]
  init : PolyT M.init
  step : PolyT M.step
  out : PolyT M.out
  ask : PolyT M.ask
  resume : PolyT fun p : M.σ × A => M.resume p.1 p.2

/-- The machine has polynomial-time steps. Without this a number of steps says nothing, since a step
is an arbitrary function. -/
def PolyTimeSteps [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) : Prop := Nonempty (IsPolyQ M)

end QueryMachine

/-! ## What proof/machines/QueryMachines/ proves about these notions -/

/-- Bounds may be raised. -/
def StMono : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (s : M.σ) (own own' S S' : ℕ) (L : List Q) (b : β),
  M.Reaches O S b s own L → own ≤ own' → S ≤ S' → M.Reaches O S' b s own' L

/-- The cost from a state, rule by rule: a halted state costs nothing; an own step costs 1; the
query x costs w x. -/
def StWithinRules : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (s : M.σ) (T S : ℕ) (b : β),
  (M.out s = some b → size s ≤ S → M.WithinFrom O w s T S b) ∧
  (M.out s = none → M.ask s = none → size s ≤ S → M.WithinFrom O w (M.step s) T S b → M.WithinFrom O w s (T + 1) S b) ∧
  (∀ (x : Q) (v : A), M.out s = none → M.ask s = some x → O x = some v → size s ≤ S → M.WithinFrom O w (M.resume s v) T S b → M.WithinFrom O w s (T + w x) S b)

/-- The result and the list of the queries are determined by the input and the oracle. -/
def StUnique : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (own own' S S' : ℕ) (L L' : List Q) (b b' : β),
  M.Runs O a own L S b → M.Runs O a own' L' S' b' → b = b' ∧ L = L'

/-- Cost at one operation per query is the number of steps of the step machine with the oracle built
in. (This is what carries the counts proved for the step machines of this development over to
machines with query access.) -/
def StClose : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (T S : ℕ) (b : β),
  (M.close O).Runs a T S b ↔ M.Within O QueryMachine.unitCost a T S b

/-- An algorithm that takes at most T operations makes at most T queries. -/
def StQueriesLe : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (T S : ℕ) (b : β),
  M.Within O QueryMachine.unitCost a T S b → ∃ (own : ℕ) (L : List Q), M.Runs O a own L S b ∧ own + L.length ≤ T

/-- So if a query costs t ≥ 1 operations in place of one, T operations become at most T·t. -/
def StSlowDown : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (T S t : ℕ) (b : β), 1 ≤ t →
  M.Within O QueryMachine.unitCost a T S b → M.Within O (fun _ => t) a (T * t) S b

/-- Queries answered by a step machine: if R answers the query x within t x steps on states of size
at most S', the whole takes own + Σ_{x asked} (t x + 2) steps. R need answer only the queries that
are asked. -/
def StPlug : Prop := ∀ (Q A C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (R : Stepped (C × Q) A) (O : Q → Option A) (c : C) (a : α) (own S S' : ℕ) (L : List Q) (b : β) (t : Q → ℕ),
  M.Runs O a own L S b → (∀ x ∈ L, ∀ v, O x = some v → R.Runs (c, x) (t x) S' v) →
    (M.plug R).Runs (c, a) (own + (L.map fun x => t x + 2).sum) (size c + S + S' + 1) b

/-- Queries answered by a machine with query access of its own: own steps add up as in `StPlug`, and
the queries asked are those of the answering runs, in order. -/
def StSubst : Prop := ∀ (Q A Q' A' C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O : Q → Option A) (O' : Q' → Option A') (c : C) (a : α) (own S S' : ℕ)
    (L : List Q) (b : β) (t : Q → ℕ) (L' : Q → List Q'),
  M.Runs O a own L S b → (∀ x ∈ L, ∀ v, O x = some v → N.Runs O' (c, x) (t x) (L' x) S' v) →
    (M.subst N).Runs O' (c, a) (own + (L.map fun x => t x + 2).sum) (L.flatMap L') (size c + S + S' + 1) b

/-- The same in costs: if the query x of M is priced at w x, and N answers it within w x − 2
operations at the prices w', then the whole stays within the cost of M. -/
def StSubstWithin : Prop := ∀ (Q A Q' A' C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O : Q → Option A) (O' : Q' → Option A') (w : Q → ℕ) (w' : Q' → ℕ) (c : C)
    (a : α) (T S S' : ℕ) (b : β) (t : Q → ℕ),
  M.Within O w a T S b → (∀ x v, O x = some v → N.Within O' w' (c, x) (t x) S' v) → (∀ x, t x + 2 ≤ w x) →
    (M.subst N).Within O' w' (c, a) T (size c + S + S' + 1) b

/-- Building the outer oracle into a substitution is plugging in the answering machine with that
oracle built in. -/
def StCloseSubst : Prop := ∀ (Q A Q' A' C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O' : Q' → Option A'),
  (M.subst N).close O' = M.plug (N.close O')

/-- Polynomial-time steps are kept by `plug` (for `subst` and `close` see `StPolySubst` and
`StPolyClose`). (For tables that are part of the input: `plug` with C the tables and R a machine
that looks an entry up.) -/
def StPolyPlug : Prop := ∀ (Q A C α β : Type) [Enc Q] [Enc A] [Enc α] [Enc β] [HasSize C] [Enc C] [Carried C] (M : QueryMachine Q A α β) (R : Stepped (C × Q) A),
  M.PolyTimeSteps → Nonempty (IsPolyT R) → Nonempty (IsPolyT (M.plug R))

/-- Polynomial-time steps are kept by `subst`. -/
def StPolySubst : Prop := ∀ (Q A Q' A' C α β : Type) [Enc Q] [Enc A] [Enc Q'] [Enc A'] [Enc α] [Enc β] [HasSize C] [Enc C] [Carried C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A),
  M.PolyTimeSteps → N.PolyTimeSteps → (M.subst N).PolyTimeSteps

/-- Polynomial-time steps are kept by `close`, for an oracle computed in polynomial time from the
query alone. -/
def StPolyClose : Prop := ∀ (Q A α β : Type) [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) (O : Q → Option A),
  M.PolyTimeSteps → PolyT O → Nonempty (IsPolyT (M.close O))

end QueryMachines
