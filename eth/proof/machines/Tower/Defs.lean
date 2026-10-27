/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.Kernel
public import QueryMachines.CombDefs
public import QueryMachines.CombRunsStatement

/-! # A tower: one machine for a recursion whose depth is data

Definitions and statements only; nothing is proved here. The machines are
`QueryMachines.QueryMachine` (a step machine with a pending query; `Within O w a T S b`: with the
oracle O, if the query x costs w x operations, the
result on a is b within T operations on states of size at most S; `PolyTimeSteps`).

**Why.** Theorem A (b) says: «One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to
tables with |W_w| < 2^B, outputs the value of the (K_ℓ, λ)-clique within … operations.» Its proof is
a recursion on ℓ: the
algorithm for K_{ℓ+1} nodes goes through the functions ι : 𝓡 → 𝓘, and for each of them calls the
algorithm for K_ℓ nodes on a clique whose tables, in the words of Definition 3, «are not written
out»: every query of the callee is answered by computing the entry, which
in turn queries the tables of the caller. So at depth ℓ a query of the innermost call runs up
through ℓ procedures. For a fixed depth one could build, by recursion in Lean, one machine and one
type of
states for each ℓ; here ℓ is part of the input, so there must be ONE machine, with one type of
states and one certificate that a step takes polynomial time.

**What is here.**
* `selfCall M`: M may, besides its queries, CALL ITSELF on another input (query `Sum.inr a'`, answer
  `Sum.inr b`). `selfCall M` is ONE machine that runs M with all its calls; its state is the list of
  the activations of M, the running one first.
  `SelfCallPoly`: it has polynomial-time steps if M has. `SelfCallRuns`: if M, with every call of a'
  answered by `val a'` at the price `T a' + 2`, returns `val a` at the cost `T a`, and calls go down
  in a measure `dep`, then `selfCall M` returns `val a` at the cost `T a`.
* `nest Sol Inn`, `tower Sol Inn`: the shape of the appendix's recursion. A solver `Sol` (input: a
  context c; it may call the solver on another context c', query `Sum.inl c'`, and may query its own
  tables, `Sum.inr (Sum.inl q)`) and a procedure `Inn`
  (input: the context c' of a callee and a query q of that callee to its tables; it may query the
  tables of the caller, `Sum.inl q'`). The tables of a callee are a function of the caller's tables,
  so the recursion is of higher order as printed. It
  becomes a machine that calls itself when every activation carries the list `env` of the contexts
  through which its table queries have to run up: a query with `env = []` goes to the tables of the
  outermost instance, and a query
  with `env = c :: env'` is a call of the procedure on c, whose own queries run up through `env'`.
* A second kind of query, of type G, is the same at every depth and is passed on unchanged
  (`Sum.inr g`): for what every level may ask, such as the algorithm of the pieces, or a certified
  function used as one instruction at a price. Take G empty if there is none.
* `TowerPoly`: the tower has polynomial-time steps if `Sol` and `Inn` have.
* `TowerRuns`: the tower returns the value, within the cost given by the recursion `cost`: T(ℓ+1, t) =
  T_Sol(ℓ+1; a call costs T(ℓ, T_Inn(ℓ, t) + 2) + 2, a query costs t). With T_Sol = own +
  calls·(cost of a call) and T_Inn = own' + q'·t
  (`CostShape`, `CostSlowDown`) this is the recursion behind the display «So the total number of
  operations is at most …» in the proof of Theorem A (b).

**What these statements do not show.** That the solver and the procedure of Theorem A (b) exist with
these properties. That a number of operations is a number of steps of a Turing machine: that is
`StPolyPlug` or `StPolyClose` with
`CountKSat.exists_tmW`, and it costs a factor polynomial in the sizes of the states. These sizes are
part of every claim; those of the tower are quadratic in the depth, because every activation carries
its own list env. -/

@[expose] public section

namespace QueryMachines.Tower

open Groundwork

/-! ### A machine that calls itself -/

section selfCall

variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)

/-- One step of the stack of activations, the running one first. If the running activation has
halted, its result goes to the one below it; a call starts a new activation on top; else the running
activation makes a step. Where the
whole has halted or the running activation asks a query that is not a call, the step does nothing. -/
def rstep : List M.σ → List M.σ
  | [] => []
  | s :: rest =>
    match M.out s with
    | some b =>
      match rest with
      | [] => [s]
      | s' :: rest' => M.resume s' (Sum.inr b) :: rest'
    | none =>
      match M.ask s with
      | some (Sum.inr a') => M.init a' :: s :: rest
      | some (Sum.inl _) => s :: rest
      | none => M.step s :: rest

/-- The query of the whole: a query of the running activation that is not a call. -/
def rask : List M.σ → Option Q
  | [] => none
  | s :: _ =>
    match M.out s, M.ask s with
    | none, some (Sum.inl x) => some x
    | _, _ => none

/-- The answer goes to the running activation. -/
def rresume : List M.σ → A → List M.σ
  | [], _ => []
  | s :: rest, a => M.resume s (Sum.inl a) :: rest

/-- The whole has halted when the only activation has. -/
def rout : List M.σ → Option β
  | [s] => M.out s
  | _ => none

/-- M with all its calls of itself, as one machine. -/
def selfCall : QueryMachine Q A α β where
  σ := List M.σ
  init a := [M.init a]
  step := rstep M
  out := rout M
  ask := rask M
  resume := rresume M

end selfCall

open Classical in
/-- How the queries of M on the input a are to be answered: a query that is not a call by O; a call
of a', if a' is a good input of smaller depth than a, by `val a'`. Any other call has no answer. -/
noncomputable def callOracle {Q A α β : Type} (O : Q → Option A) (Good : α → Prop) (val : α → β) (dep : α → ℕ) (a : α) : Q ⊕ α → Option (A ⊕ β)
  | Sum.inl x => (O x).map Sum.inl
  | Sum.inr a' => if Good a' ∧ dep a' < dep a then some (Sum.inr (val a')) else none

/-- `selfCall M` has polynomial-time steps, once and for all depths of the recursion, if M has. -/
def SelfCallPoly : Prop := ∀ (Q A α β : Type) [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β), M.PolyTimeSteps → (selfCall M).PolyTimeSteps

/-- Let M, on every good input a, return `val a` within `T a` operations on states of size at most
S, when its queries are answered by O at the prices w and every call of a good input a' of smaller
depth is answered by `val a'` at the price
`T a' + 2`. Then `selfCall M`, on every good input a, returns `val a` within `T a` operations, with
queries answered by O at the prices w, and its states have size at most (dep a + 1)·(S + 1) + 1. -/
def SelfCallRuns : Prop := ∀ (Q A α β : Type) (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β) (O : Q → Option A) (w : Q → ℕ) (Good : α → Prop) (val : α → β) (dep T : α → ℕ) (S : ℕ),
  (∀ a, Good a → M.Within (callOracle O Good val dep a) (Sum.elim w fun a' => T a' + 2) a (T a) S (val a)) →
  ∀ a, Good a → (selfCall M).Within O w a (T a) ((dep a + 1) * (S + 1) + 1) (val a)

/-! ### The tower: tables of the callee computed from the tables of the caller -/

section tower

variable {Ctx Q G A : Type} [HasSize Ctx]

/-- The inputs of the machine that calls itself. `Sum.inl (env, c)`: solve the instance with the
context c, whose table queries run up through env. `Sum.inr (c, env, q)`: the entry q of the tables
of the callee with the context c, where the
queries to the caller's tables run up through env. -/
abbrev NIn (Ctx Q : Type) : Type := (List Ctx × Ctx) ⊕ (Ctx × List Ctx × Q)

/-- Where a query goes. A query q to tables that run up through env: to the tables of the outermost
instance, or to the procedure on the first context of env. A query g of the second kind: out of the
tower, unchanged. -/
def upQuery (env : List Ctx) : Q ⊕ G → (Q ⊕ G) ⊕ NIn Ctx Q
  | Sum.inl q =>
    match env with
    | [] => Sum.inl (Sum.inl q)
    | c :: env' => Sum.inr (Sum.inr (c, env', q))
  | Sum.inr g => Sum.inl (Sum.inr g)

variable (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A)

/-- The solver and the procedure as one machine that calls itself; every activation carries its list
env. -/
def nest : QueryMachine ((Q ⊕ G) ⊕ NIn Ctx Q) (A ⊕ A) (NIn Ctx Q) A where
  σ := (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)
  init x :=
    match x with
    | Sum.inl (env, c) => Sum.inl (env, Sol.init c)
    | Sum.inr (c, env, q) => Sum.inr (env, Inn.init (c, q))
  step s :=
    match s with
    | Sum.inl (env, s) => Sum.inl (env, Sol.step s)
    | Sum.inr (env, i) => Sum.inr (env, Inn.step i)
  out s :=
    match s with
    | Sum.inl (_, s) => Sol.out s
    | Sum.inr (_, i) => Inn.out i
  ask s :=
    match s with
    | Sum.inl (env, s) =>
      match Sol.ask s with
      | some (Sum.inl c') => some (Sum.inr (Sum.inl (c' :: env, c')))
      | some (Sum.inr x) => some (upQuery env x)
      | none => none
    | Sum.inr (env, i) => (Inn.ask i).map (upQuery env)
  resume s r :=
    match s with
    | Sum.inl (env, s) => Sum.inl (env, Sol.resume s (r.elim id id))
    | Sum.inr (env, i) => Sum.inr (env, Inn.resume i (r.elim id id))

/-- The tower: `selfCall (nest Sol Inn)`, started on the outermost instance with the context c,
whose table queries are queries of the tower. -/
def tower : QueryMachine (Q ⊕ G) A Ctx A where
  σ := List (nest Sol Inn).σ
  init c := [(nest Sol Inn).init (Sum.inl ([], c))]
  step := rstep (nest Sol Inn)
  out := rout (nest Sol Inn)
  ask := rask (nest Sol Inn)
  resume := rresume (nest Sol Inn)

end tower

/-! ### What the tower computes, and at what cost -/

/-- What a recursion is to compute. An instance is a context c with tables f (a function from
queries to answers that need not answer every query). `lev c` is its depth, `Good c f` says that it
is well formed, `val c f` is its value, `Child c f c'` says that the solver may call
c' when it works on (c, f), and `tab c' f` are the tables of the callee c' when f are the tables of
the caller. This is a device of the statement, not a part of the machine. It may be chosen anew for
every outermost instance, and so may the
costs and sizes in `Meets`: so `Good` may hold the parameters (in the appendix: λ and B) within the
bounds that they have along the recursion from that instance, and the costs, which are indexed by
the depth alone, may depend on that instance. -/
structure Spec (Ctx Q A : Type) where
  lev : Ctx → ℕ
  Good : Ctx → (Q → Option A) → Prop
  val : Ctx → (Q → Option A) → A
  Child : Ctx → (Q → Option A) → Ctx → Prop
  tab : Ctx → (Q → Option A) → Q → Option A

open Classical in
/-- How the queries of the solver on (c, f) are to be answered: a call of a permitted c' by the
value of c' with its tables; a query to the tables by f; a query of the second kind by gl. A call
that is not permitted has no answer. -/
noncomputable def Spec.oracle {Ctx Q G A : Type} (P : Spec Ctx Q A) (gl : G → Option A) (c : Ctx) (f : Q → Option A) : Ctx ⊕ (Q ⊕ G) → Option A
  | Sum.inl c' => if P.Child c f c' then some (P.val c' (P.tab c' f)) else none
  | Sum.inr (Sum.inl q) => f q
  | Sum.inr (Sum.inr g) => gl g

/-- The solver and the procedure meet the specification, with these costs and sizes; gl answers the
queries of the second kind, at the prices wg. `TS l tc tq`: cost of the solver at depth l if a call
costs tc and a query to its tables tq; it must hold
for all instances of depth l that `Good` admits (in Appendix A the number L of a callee depends on
ι; the bound is one for all ι). `TI l tq`: cost of the procedure for a callee of depth l if a query
to the caller's tables
costs tq. SS, SI, SC: sizes of the states of the solver, of the procedure, and of the contexts of
calls. -/
structure Spec.Meets {Ctx Q G A : Type} [HasSize Ctx] (P : Spec Ctx Q A) (gl : G → Option A) (wg : G → ℕ) (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A)
    (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (SS SI SC : ℕ) : Prop where
  /-- a call goes one level down -/
  child_lev : ∀ c f c', P.Good c f → P.Child c f c' → P.lev c' + 1 = P.lev c
  /-- to a well-formed instance -/
  child_good : ∀ c f c', P.Good c f → P.Child c f c' → P.Good c' (P.tab c' f)
  /-- with a small context -/
  child_size : ∀ c f c', P.Good c f → P.Child c f c' → size c' ≤ SC
  /-- the solver, with its calls and queries answered as specified, returns the value -/
  sol : ∀ c f, P.Good c f → ∀ tc tq : ℕ, Sol.Within (P.oracle gl c f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) wg)) c (TS (P.lev c) tc tq) SS (P.val c f)
  /-- the procedure, with the caller's tables, returns the entries of the callee's tables -/
  inn : ∀ c f c', P.Good c f → P.Child c f c' → ∀ q a, P.tab c' f q = some a → ∀ tq : ℕ, Inn.Within (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) (c', q) (TI (P.lev c') tq) SI a

/-- The cost of the tower at depth l if a query to the tables of the instance costs t. -/
def cost (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, t => TS 0 0 t
  | l + 1, t => TS (l + 1) (cost TS TI l (TI l t + 2) + 2) t

/-- The bound on the sizes of the states of the tower at depth l: at most 2l + 2 activations, each
with a list of at most l contexts. -/
def towerSize (l SS SI SC : ℕ) : ℕ := (2 * l + 2) * (l * (SC + 1) + SS + SI + 3) + 1

/-- The tower has polynomial-time steps, once and for all depths, if the solver and the procedure
have. -/
def TowerPoly : Prop := ∀ (Ctx Q G A : Type) [HasSize Ctx] [Enc Ctx] [Carried Ctx] [Enc Q] [Enc G] [Enc A] (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A),
  Sol.PolyTimeSteps → Inn.PolyTimeSteps → (tower Sol Inn).PolyTimeSteps

/-- The tower returns the value of every well-formed instance, at the cost of the recursion, for
every cost tq of a query to the tables of that instance. -/
def TowerRuns : Prop := ∀ (Ctx Q G A : Type) [HasSize Ctx] (P : Spec Ctx Q A) (gl : G → Option A) (wg : G → ℕ) (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A)
  (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (SS SI SC : ℕ), P.Meets gl wg Sol Inn TS TI SS SI SC →
  ∀ c f, P.Good c f → ∀ tq : ℕ, (tower Sol Inn).Within (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) c (cost TS TI (P.lev c) tq) (towerSize (P.lev c) SS SI SC) (P.val c f)

/-- The costs of the shape own + calls·tc + queries·tq and own' + q'·t, as in the appendix. -/
def shapeS (own calls qs : ℕ → ℕ) (l tc tq : ℕ) : ℕ := own l + calls l * tc + qs l * tq

/-- See `shapeS`. -/
def shapeI (own' q' : ℕ → ℕ) (l tq : ℕ) : ℕ := own' l + q' l * tq

/-- The recursion written out for these shapes: T(l+1, t) = own + calls·(T(l, own' + q'·t + 2) + 2) +
queries·t. -/
def CostShape : Prop := ∀ (own calls qs own' q' : ℕ → ℕ) (l t : ℕ),
  cost (shapeS own calls qs) (shapeI own' q') (l + 1) t =
    own (l + 1) + calls (l + 1) * (cost (shapeS own calls qs) (shapeI own' q') l (own' l + q' l * t + 2) + 2) + qs (l + 1) * t

/-- For these shapes, queries that cost x times as much make the whole cost at most x times as much.
This is what turns T(l, cost of an entry) into the product 𝒯·(cost of an entry) of the appendix. -/
def CostSlowDown : Prop := ∀ (own calls qs own' q' : ℕ → ℕ) (l x y : ℕ), 1 ≤ x →
  cost (shapeS own calls qs) (shapeI own' q') l (x * y) ≤ x * cost (shapeS own calls qs) (shapeI own' q') l y

end QueryMachines.Tower
