/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Defs

/-! # The tower as a machine that calls itself: what its activations compute

Fix an outermost instance (c0, f0) and the cost tq of a query to its tables. An activation carries
the list env of the contexts through which its table queries run up. `tabs env` are the tables that
these queries see, `parent env` is the
context of the instance that owns them, `Chain env` says that every context of env is a permitted
call of the one below it, `price env` is what a query to `tabs env` costs. With these, `nGood`,
`nval`, `ndep`, `nT` are the good
inputs, the values, the depths and the costs for `SelfCallRuns`. -/

@[expose] public section

namespace QueryMachines.Tower

open Groundwork

variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)

/-- The tables seen by queries that run up through env. -/
def tabs : List Ctx → Q → Option A
  | [] => f0
  | c :: env => P.tab c (tabs env)

/-- The context of the instance that owns these tables. -/
def parent : List Ctx → Ctx
  | [] => c0
  | c :: _ => c

/-- Every context of env is a permitted call of the instance below it. -/
def Chain : List Ctx → Prop
  | [] => True
  | c :: env => Chain env ∧ P.Child (parent c0 env) (tabs P f0 env) c

/-- The cost of a query to `tabs env`. -/
def price : List Ctx → ℕ
  | [] => tq
  | c :: env => TI (P.lev c) (price env) + 2

/-- The price of a call made at depth l, if a query to the tables of the caller costs t. -/
def callCost : ℕ → ℕ → ℕ
  | 0, _ => 0
  | l + 1, t => cost TS TI l (TI l t + 2) + 2

/-- The cost of the tower at depth l is the cost of the solver with the price of a call made at
depth l. -/
theorem cost_eq (l t : ℕ) : cost TS TI l t = TS l (callCost TS TI l t) t := by cases l <;> rfl

/-- The good inputs. -/
def nGood : NIn Ctx Q → Prop
  | Sum.inl (env, c) => Chain P c0 f0 env ∧ c = parent c0 env
  | Sum.inr (c, env, q) => Chain P c0 f0 (c :: env) ∧ (P.tab c (tabs P f0 env) q).isSome

/-- The values. (Where an entry is missing: some element of A.) -/
def nval : NIn Ctx Q → A
  | Sum.inl (env, c) => P.val c (tabs P f0 env)
  | Sum.inr (c, env, q) => (P.tab c (tabs P f0 env) q).getD (P.val c0 f0)

/-- The depths. -/
def ndep : NIn Ctx Q → ℕ
  | Sum.inl (env, c) => 2 * P.lev c + env.length + 1
  | Sum.inr (_, env, _) => env.length

/-- The costs. -/
def nT : NIn Ctx Q → ℕ
  | Sum.inl (env, c) => cost TS TI (P.lev c) (price P TI tq env)
  | Sum.inr (c, env, _) => TI (P.lev c) (price P TI tq env)

/-- A call of a good input of smaller depth is answered by its value. -/
theorem callOracle_call {Q A α β : Type} (O : Q → Option A) {Good : α → Prop} (val : α → β) {dep : α → ℕ} {a a' : α} (h : Good a' ∧ dep a' < dep a) :
    callOracle O Good val dep a (Sum.inr a') = some (Sum.inr (val a')) := if_pos h

variable {P TS TI c0 f0} [HasSize Ctx] {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A} {SS SI SC : ℕ}

/-- Along a chain: the instance is well formed, the depths add up, the list is small. -/
theorem chain_facts (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) : ∀ env : List Ctx, Chain P c0 f0 env →
    P.Good (parent c0 env) (tabs P f0 env) ∧ P.lev (parent c0 env) + env.length = P.lev c0 ∧ size env ≤ env.length * (SC + 1) + 1
  | [], _ => ⟨hG, rfl, by simp [size_list]⟩
  | c :: env, h => by
    obtain ⟨h1, h2, h3⟩ := chain_facts hM hG env h.1
    refine ⟨hM.child_good _ _ _ h1 h.2, ?_, ?_⟩
    · have := hM.child_lev _ _ _ h1 h.2
      simp only [parent, List.length_cons] at *
      omega
    · have := hM.child_size _ _ _ h1 h.2
      rw [size_list] at h3
      simp only [size_list, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

omit [HasSize Ctx] in
/-- A query y that runs up through env, asked by the activation x: it has the answer that `tabs env`
or gl gives, at the price `price env` or wg. -/
theorem up_ok (gl : G → Option A) (wg : G → ℕ) (TS : ℕ → ℕ → ℕ → ℕ) (env : List Ctx) (hC : Chain P c0 f0 env) (y : Q ⊕ G) (v : A) (hy : Sum.elim (tabs P f0 env) gl y = some v) (x : NIn Ctx Q)
    (hx : env.length ≤ ndep P x) :
    ∃ r : A ⊕ A, callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x (upQuery env y) = some r ∧ r.elim id id = v ∧
      (Sum.elim (Sum.elim (fun _ => tq) wg) fun a' => nT P TS TI tq a' + 2) (upQuery env y) = Sum.elim (fun _ => price P TI tq env) wg y := by
  rcases y with q | g
  · rcases env with _ | ⟨c1, env'⟩
    · refine ⟨Sum.inl v, ?_, rfl, rfl⟩
      show Option.map Sum.inl (f0 q) = some (Sum.inl v)
      rw [show f0 q = some v from hy]; rfl
    · have hy' : P.tab c1 (tabs P f0 env') q = some v := hy
      refine ⟨Sum.inr v, ?_, rfl, rfl⟩
      show callOracle _ _ _ _ x (Sum.inr (Sum.inr (c1, env', q))) = _
      rw [callOracle_call _ _ ⟨⟨hC, by rw [hy']; rfl⟩, Nat.lt_of_succ_le hx⟩]
      show some (Sum.inr ((P.tab c1 (tabs P f0 env') q).getD _)) = _
      rw [hy']; rfl
  · refine ⟨Sum.inl v, ?_, rfl, rfl⟩
    show Option.map Sum.inl (gl g) = some (Sum.inl v)
    rw [show gl g = some v from hy]; rfl

end QueryMachines.Tower
