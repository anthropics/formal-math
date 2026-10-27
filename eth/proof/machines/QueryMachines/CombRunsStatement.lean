/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.CombDefs

/-! # How the constructions run (statements only)

For ten constructions of proof/machines/QueryMachines/CombDefs.lean (lift, query, mapAsk, mapIn,
mapOut, bind, both, branch, foldWhile, foldRange): the run of the whole from the runs of the parts.
ite, const, optBind, sumRange, prodRange and gated are made from these.
For mapIn, mapOut, bind, both, branch, foldWhile and foldRange, own steps and sizes are those of the
lemma of the same name for step machines (proof/machines/StepMachines/Prog/Stepped.lean,
proof/machines/StepMachines/Prog/Comb.lean, proof/machines/StepMachines/Prog/Range.lean). lift keeps
the run of the step machine. query has the size bound of `ofFun_runs` and no own step. mapAsk keeps
the run with each query rewritten. The lists of queries are joined in the order of the runs. All
bounds are explicit.
The main text does not need these (it goes through `close`); they serve programs whose queries must
be told apart, as in Appendices A, B and D. This file has no proofs. -/

@[expose] public section

namespace QueryMachines

open Groundwork Finset

/-- A step machine asks nothing. -/
def StLiftRuns : Prop := ∀ (Q A α β : Type) (R : Stepped α β) (O : Q → Option A) (a : α) (t S : ℕ) (b : β),
  R.Runs a t S b → (QueryMachine.lift R : QueryMachine Q A α β).Runs O a t [] S b

/-- One query, no own step. -/
def StQueryRuns : Prop := ∀ (Q A α : Type) [HasSize α] [HasSize A] (h : α → Q) (O : Q → Option A) (a : α) (v : A),
  O (h a) = some v → (QueryMachine.query h : QueryMachine Q A α A).Runs O a 0 [h a] (max (size a) (size v) + 1) v

/-- Queries rewritten by h: the list of queries is mapped by h. -/
def StMapAskRuns : Prop := ∀ (Q Q' A α β : Type) (h : Q → Q') (M : QueryMachine Q A α β) (O : Q' → Option A) (a : α) (own S : ℕ) (L : List Q) (b : β),
  M.Runs (fun x => O (h x)) a own L S b → (QueryMachine.mapAsk h M).Runs O a own (L.map h) S b

/-- A function applied to the input: the run is that of M. -/
def StMapInRuns : Prop := ∀ (Q A α β γ : Type) (g : α → β) (M : QueryMachine Q A β γ) (O : Q → Option A) (a : α) (own S : ℕ) (L : List Q) (c : γ),
  M.Runs O (g a) own L S c → (QueryMachine.mapIn g M).Runs O a own L S c

/-- A function applied to the result: the run is that of M. -/
def StMapOutRuns : Prop := ∀ (Q A α β γ : Type) (M : QueryMachine Q A α β) (g : β → γ) (O : Q → Option A) (a : α) (own S : ℕ) (L : List Q) (b : β),
  M.Runs O a own L S b → (QueryMachine.mapOut M g).Runs O a own L S (g b)

/-- M, then N: own steps add up, with one more for the hand-over; first the queries of M, then those
of N. -/
def StBindRuns : Prop := ∀ (Q A α β γ : Type) [HasSize α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) (O : Q → Option A) (a : α) (t t' S S' : ℕ) (L L' : List Q) (b : β) (c : γ),
  M.Runs O a t L S b → N.Runs O (a, b) t' L' S' c → (QueryMachine.bind M N).Runs O a (t + 1 + t') (L ++ L') (max (size a + S) S' + 1) c

/-- M, then N, on one input: as for `bind`. -/
def StBothRuns : Prop := ∀ (Q A α β γ : Type) [HasSize α] [HasSize β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) (O : Q → Option A) (a : α) (t t' S S' : ℕ) (L L' : List Q) (b : β) (c : γ),
  M.Runs O a t L S b → N.Runs O a t' L' S' c → (QueryMachine.both M N).Runs O a (t + 1 + t') (L ++ L') (max (size a + S) (size b + S') + 1) (b, c)

/-- A choice: the run is that of the machine chosen; the size bound is one larger. -/
def StBranchRuns : Prop := ∀ (Q A α α₁ α₂ β : Type) (sel : α → α₁ ⊕ α₂) (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) (O : Q → Option A) (a : α) (t S : ℕ) (L : List Q) (b : β),
  (∀ x, sel a = .inl x → M₁.Runs O x t L S b → (QueryMachine.branch sel M₁ M₂).Runs O a t L (S + 1) b) ∧
  (∀ y, sel a = .inr y → M₂.Runs O y t L S b → (QueryMachine.branch sel M₁ M₂).Runs O a t L (S + 1) b)

/-- The loop: own steps Σ over the orbit of (own steps of the body + 1); the queries of the rounds
one after the other; the result is the fold over the orbit. -/
def StFoldWhileRuns : Prop := ∀ (Q A α β γ τ : Type) [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : QueryMachine Q A τ β) (g : γ → τ → β → γ) (c₀ : α → γ) (O : Q → Option A)
    (a : α) (xs : List τ), Stepped.Orbit nxt (start a) xs → ∀ (t : τ → ℕ) (Lq : τ → List Q) (v : τ → β) (Sx Sc Sm : ℕ),
  (∀ x ∈ xs, M.Runs O x (t x) (Lq x) Sm (v x)) → (∀ x ∈ xs, size x ≤ Sx) → (∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) →
  (QueryMachine.foldWhile start nxt M g c₀).Runs O a (xs.map fun x => t x + 1).sum (xs.flatMap Lq) (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) (c₀ a))

/-- The loop over y < N a; the range is a function of the input. -/
def StFoldRangeRuns : Prop := ∀ (Q A α β γ : Type) [HasSize α] [HasSize γ] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) β) (g : γ → ℕ → β → γ) (c₀ : α → γ) (O : Q → Option A) (a : α)
    (t : ℕ → ℕ) (Lq : ℕ → List Q) (v : ℕ → β) (Sc Sm : ℕ),
  (∀ y < N a, M.Runs O (a, y) (t y) (Lq y) Sm (v y)) → (∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) →
  (QueryMachine.foldRange N M g c₀).Runs O a (∑ y ∈ range (N a), (t y + 1)) ((List.range (N a)).flatMap Lq) (size a + size (N a) + (Sc + Sm) + 1) ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a))

end QueryMachines
