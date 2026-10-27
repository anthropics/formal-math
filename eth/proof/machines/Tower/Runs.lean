/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Defs
import Tower.Kernel

/-! # Runs of `selfCall M`

The lemma `selfCall_from` is about a run of M from any state s on the input a, with any stack K of
waiting activations below it and any continuation: if the whole reaches b within tk operations once
the running activation has halted
with `val a`, then it reaches b from `s :: K` within the cost of M's run plus tk. Strong induction
on the depth outside (a call is a run of M on an input of smaller depth, on the stack `s :: K`),
induction on the run inside. The bound on
the sizes is a hypothesis of the lemma: the stack below, and room for `dep a + 1` activations more. -/

public section

namespace QueryMachines.Tower

open Groundwork

variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)

/-! ### One step of the stack, case by case -/

/-- While the running activation has not halted, the whole has not. -/
theorem rout_none {s : M.σ} (K : List M.σ) (h : M.out s = none) : rout M (s :: K) = none := by
  cases K
  · exact h
  · rfl

/-- A halted activation asks nothing. -/
theorem rask_halted {s : M.σ} {b : β} (K : List M.σ) (h : M.out s = some b) : rask M (s :: K) = none := by simp [rask, h]

/-- An activation that asks nothing: the whole asks nothing. -/
theorem rask_none {s : M.σ} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = none) : rask M (s :: K) = none := by simp [rask, h1, h2]

/-- A call is not a query of the whole. -/
theorem rask_call {s : M.σ} {a' : α} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = some (Sum.inr a')) : rask M (s :: K) = none := by simp [rask, h1, h2]

/-- A query that is not a call is the query of the whole. -/
theorem rask_query {s : M.σ} {x : Q} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = some (Sum.inl x)) : rask M (s :: K) = some x := by simp [rask, h1, h2]

/-- An own step of the running activation. -/
theorem rstep_step {s : M.σ} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = none) : rstep M (s :: K) = M.step s :: K := by simp [rstep, h1, h2]

/-- A call starts a new activation on top. -/
theorem rstep_call {s : M.σ} {a' : α} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = some (Sum.inr a')) : rstep M (s :: K) = M.init a' :: s :: K := by simp [rstep, h1, h2]

/-- The result of a halted activation goes to the one below it. -/
theorem rstep_pop {s s' : M.σ} {b : β} (K : List M.σ) (h : M.out s = some b) : rstep M (s :: s' :: K) = M.resume s' (Sum.inr b) :: K := by simp [rstep, h]

/-- The size of a stack. -/
theorem size_stack (s : M.σ) (K : List M.σ) : size (s :: K) = size s + 1 + size K := by
  simp only [size_list, List.map_cons, List.sum_cons]; omega

/-! ### The run -/

/-- A run of M from any state, on any stack of waiting activations and with any continuation (see
the head of this file). -/
theorem selfCall_from (O : Q → Option A) (w : Q → ℕ) (Good : α → Prop) (val : α → β) (dep T : α → ℕ) (S : ℕ)
    (H : ∀ a, Good a → M.Within (callOracle O Good val dep a) (Sum.elim w fun a' => T a' + 2) a (T a) S (val a)) :
    ∀ (n : ℕ) (a : α), dep a = n → Good a → ∀ (s : M.σ) (own : ℕ) (L : List (Q ⊕ α)), M.Reaches (callOracle O Good val dep a) S (val a) s own L →
    ∀ (K : List M.σ) (S' tk : ℕ) (b : β), size K + (dep a + 1) * (S + 1) ≤ S' →
      (∀ sh : M.σ, M.out sh = some (val a) → size sh ≤ S → (selfCall M).WithinFrom O w (sh :: K : List M.σ) tk S' b) →
      (selfCall M).WithinFrom O w (s :: K : List M.σ) (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk) S' b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a hn hG s own L hr K S' tk b hS hc
  have hmul : (dep a + 1) * (S + 1) = dep a * (S + 1) + (S + 1) := Nat.succ_mul _ _
  have hsz : ∀ s : M.σ, size s ≤ S → size (s :: K : List M.σ) ≤ S' := fun s hs => by rw [size_stack]; omega
  induction hr with
  | halt h1 h2 => exact wfMono (hc _ h1 h2) (by omega) le_rfl
  | @step s own L h1 h2 h3 _ ih =>
    have h := wfStep (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w) (rout_none M K h1) (rask_none M K h1 h2) (hsz _ h3)
      (by rw [show (selfCall M).step (s :: K : List M.σ) = (M.step s :: K : List M.σ) from rstep_step M K h1 h2]; exact ih)
    exact wfMono h (by omega) le_rfl
  | @query s own L x v h1 h2 h3 h4 _ ih =>
    rcases x with q | a'
    · obtain ⟨v0, hv0, rfl⟩ : ∃ v0, O q = some v0 ∧ Sum.inl v0 = v := by simpa [callOracle] using h3
      have h := wfQuery (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w) (rout_none M K h1) (rask_query M K h1 h2) hv0 (hsz _ h4) ih
      refine wfMono h ?_ le_rfl
      simp only [List.map_cons, List.sum_cons, Sum.elim_inl]; omega
    · obtain ⟨⟨hG', hd⟩, rfl⟩ : (Good a' ∧ dep a' < dep a) ∧ Sum.inr (val a') = v := by
        simpa [callOracle] using h3
      obtain ⟨own', L', hr', hc'⟩ := H a' hG'
      have hle : (dep a' + 1) * (S + 1) ≤ dep a * (S + 1) := Nat.mul_le_mul_right _ hd
      have hsz2 : ∀ sh : M.σ, size sh ≤ S → size (sh :: s :: K : List M.σ) ≤ S' := fun sh hs => by
        have : S + 1 ≤ (dep a' + 1) * (S + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        rw [size_stack, size_stack]; omega
      have hcall := IH (dep a') (hn ▸ hd) a' rfl hG' _ own' L' hr' (s :: K) S' (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk + 1) b
        (by rw [size_stack]; omega)
        (fun sh g1 g2 => wfStep (M := selfCall M) (s := (sh :: s :: K : List M.σ)) rfl (rask_halted M (s :: K) g1) (hsz2 _ g2)
          (by rw [show (selfCall M).step (sh :: s :: K : List M.σ) = (M.resume s (Sum.inr (val a')) :: K : List M.σ) from rstep_pop M K g1]; exact ih))
      have h := wfStep (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w) (rout_none M K h1) (rask_call M K h1 h2) (hsz _ h4)
        (by rw [show (selfCall M).step (s :: K : List M.σ) = (M.init a' :: s :: K : List M.σ) from rstep_call M K h1 h2]; exact hcall)
      refine wfMono h ?_ le_rfl
      simp only [List.map_cons, List.sum_cons, Sum.elim_inr]; omega

/-- `selfCall M` returns `val a` within `T a` operations on every good input a. -/
theorem selfCallRuns : SelfCallRuns := by
  intro Q A α β M O w Good val dep T S H a hG
  obtain ⟨own, L, hr, hc⟩ := H a hG
  have h1 : S + 1 ≤ (dep a + 1) * (S + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h := selfCall_from M O w Good val dep T S H (dep a) a rfl hG _ own L hr [] ((dep a + 1) * (S + 1) + 1) 0 (val a)
    (by simp only [size_list, List.map_nil, List.sum_nil]; omega)
    (fun sh g1 g2 => wfHalt (M := selfCall M) (s := ([sh] : List M.σ)) g1 (by show size ([sh] : List M.σ) ≤ _; rw [size_stack]; simp only [size_list, List.map_nil, List.sum_nil]; omega))
  obtain ⟨own', L', hr', hc'⟩ := h
  exact ⟨own', L', hr', by omega⟩

end QueryMachines.Tower
