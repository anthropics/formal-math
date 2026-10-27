/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.Kernel
public import StepMachines.Prog.Stepped
import Mathlib.Tactic

/-! # Runs of machines with query access

Proofs of `StMono`, `StWithinRules`, `StUnique`, `StClose`, `StQueriesLe`, `StSlowDown`, `StSubst`,
`StPlug`, `StSubstWithin`, `StCloseSubst` (proof/machines/QueryMachines/Kernel.lean). Most rest on
one induction over a run of an arbitrary machine. -/

public section

namespace QueryMachines.QueryMachine

open Groundwork

variable {Q A Q' A' C α β : Type}

/-! ## Bounds may be raised; the result and the queries are determined -/

/-- The bound on the own steps and the bound on the sizes may be raised; the list of queries stays. -/
theorem Reaches.mono {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (ho : own ≤ own') (hS : S ≤ S') : M.Reaches O S' b s own' L := by
  induction h generalizing own' with
  | halt h1 h2 => exact .halt h1 (h2.trans hS)
  | step h1 h2 h3 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, own' = k + 1 := ⟨own' - 1, by omega⟩
    exact .step h1 h2 (h3.trans hS) (ih (by omega))
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 (h4.trans hS) (ih ho)

/-- The same for runs from the input. -/
theorem Runs.mono {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L : List Q} {b : β} {a : α}
    (h : M.Runs O a own L S b) (ho : own ≤ own') (hS : S ≤ S') : M.Runs O a own' L S' b := Reaches.mono h ho hS

/-- The cost and the bound on the sizes may be raised (from a state). -/
theorem WithinFrom.mono {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {S S' T T' : ℕ} {b : β} {s : M.σ}
    (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') : M.WithinFrom O w s T' S' b :=
  let ⟨own, L, hr, hle⟩ := h; ⟨own, L, hr.mono le_rfl hS, hle.trans hT⟩

/-- The cost and the bound on the sizes may be raised. -/
theorem Within.mono {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {S S' T T' : ℕ} {b : β} {a : α}
    (h : M.Within O w a T S b) (hT : T ≤ T') (hS : S ≤ S') : M.Within O w a T' S' b :=
  let ⟨own, L, hr, hle⟩ := h; ⟨own, L, hr.mono le_rfl hS, hle.trans hT⟩

/-- From one state and with one oracle, the result and the list of the queries are determined. -/
theorem Reaches.unique {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L L' : List Q} {b b' : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (h' : M.Reaches O S' b' s own' L') : b = b' ∧ L = L' := by
  induction h generalizing own' L' with
  | halt h1 _ =>
    cases h' with
    | halt g1 _ => exact ⟨Option.some.inj (h1.symm.trans g1), rfl⟩
    | step g1 _ _ _ => rw [h1] at g1; cases g1
    | query g1 _ _ _ _ => rw [h1] at g1; cases g1
  | step h1 h2 _ _ ih =>
    cases h' with
    | halt g1 _ => rw [h1] at g1; cases g1
    | step _ _ _ g => exact ih g
    | query _ g2 _ _ _ => rw [h2] at g2; cases g2
  | query h1 h2 h3 _ _ ih =>
    cases h' with
    | halt g1 _ => rw [h1] at g1; cases g1
    | step _ g2 _ _ => rw [h2] at g2; cases g2
    | query _ g2 g3 _ g =>
      obtain rfl := Option.some.inj (h2.symm.trans g2)
      obtain rfl := Option.some.inj (h3.symm.trans g3)
      obtain ⟨hb, hL⟩ := ih g
      exact ⟨hb, by rw [hL]⟩

/-- At one operation per query, the queries of a list cost its length. -/
theorem sum_map_unitCost (L : List Q) : (L.map unitCost).sum = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, unitCost]; omega

/-- At t operations per query, the queries of a list cost its length times t. -/
theorem sum_map_const (L : List Q) (t : ℕ) : (L.map fun _ => t).sum = L.length * t := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## The oracle built in -/

/-- With the oracle built in: a state that asks nothing makes its own step. -/
theorem close_step_none {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} (h : M.ask s = none) : (M.close O).step s = M.step s := by
  change (match M.ask s with | some x => _ | none => _) = _
  rw [h]

/-- With the oracle built in: a state that asks x goes on with the answer to x. -/
theorem close_step_some {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} {x : Q} {v : A} (h : M.ask s = some x) (hv : O x = some v) :
    (M.close O).step s = M.resume s v := by
  change (match M.ask s with | some x => (match O x with | some v => _ | none => _) | none => _) = _
  rw [h]
  change (match O x with | some v => _ | none => _) = _
  rw [hv]

/-- With the oracle built in: a state that asks a query without an answer stays where it is. -/
theorem close_step_stuck {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} {x : Q} (h : M.ask s = some x) (hv : O x = none) :
    (M.close O).step s = s := by
  change (match M.ask s with | some x => (match O x with | some v => _ | none => _) | none => _) = _
  rw [h]
  change (match O x with | some v => _ | none => _) = _
  rw [hv]

/-- A run of the machine with the oracle built in is a run with query access; its steps are the own
steps and the queries. -/
theorem reaches_of_close {M : QueryMachine Q A α β} {O : Q → Option A} {S T : ℕ} {b : β} {s : (M.close O).σ}
    (h : (M.close O).Reaches S b s T) : ∃ (own : ℕ) (L : List Q), M.Reaches O S b s own L ∧ own + L.length ≤ T := by
  induction h with
  | halt ho hs => exact ⟨0, [], .halt ho hs, by simp⟩
  | @step s t ho hs _ ih =>
    obtain ⟨own, L, hr, hle⟩ := ih
    cases ha : M.ask s with
    | none =>
      rw [close_step_none ha] at hr
      exact ⟨own + 1, L, .step ho ha hs hr, by omega⟩
    | some x =>
      cases hv : O x with
      | none =>
        rw [close_step_stuck ha hv] at hr
        exact ⟨own, L, hr, by omega⟩
      | some v =>
        rw [close_step_some ha hv] at hr
        exact ⟨own, x :: L, .query ho ha hv hs hr, by simp only [List.length_cons]; omega⟩

/-- A run with query access is a run of the machine with the oracle built in; each query is one
step. -/
theorem close_reaches {M : QueryMachine Q A α β} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) : (M.close O).Reaches S b s (own + L.length) := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | @step s own L ho ha hs _ ih =>
    have : (M.close O).Reaches S b s (own + L.length + 1) := .step ho hs (by rw [close_step_none ha]; exact ih)
    exact this.mono (by omega) le_rfl
  | @query s own L x v ho ha hv hs _ ih =>
    have : (M.close O).Reaches S b s (own + L.length + 1) := .step ho hs (by rw [close_step_some ha hv]; exact ih)
    exact this.mono (by simp only [List.length_cons]; omega) le_rfl

/-! ## Queries answered by a machine -/

section Subst

variable [HasSize C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} {O' : Q' → Option A'}

/-- The answering machine, run inside. -/
theorem subst_inner {c : C} {m : M.σ} {r : N.σ} {v : A} {b : β} {t T S' Sg : ℕ} {L₁ L₂ : List Q'} (h : N.Reaches O' S' v r t L₁) (hm : size c + (size m + S' + 1) ≤ Sg)
    (hT : (M.subst N).Reaches O' Sg b (c, .inl (M.resume m v)) T L₂) : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (t + 1 + T) (L₁ ++ L₂) := by
  induction h with
  | @halt r t ho hs =>
    have e : (M.subst N).step (c, .inr (m, r)) = (c, .inl (M.resume m v)) := by
      change (match N.out r with | some v => _ | none => _) = _
      rw [ho]
    have ea : (M.subst N).ask (c, .inr (m, r)) = none := by
      change (match N.out r with | some _ => none | none => N.ask r) = _
      rw [ho]
    have : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (T + 1) L₂ :=
      .step rfl ea (by change size c + (size m + size r + 1) ≤ _; omega) (e ▸ hT)
    exact this.mono (by omega) le_rfl
  | @step r t L ho ha hs _ ih =>
    have e : (M.subst N).step (c, .inr (m, r)) = (c, .inr (m, N.step r)) := by
      change (match N.out r with | some v => _ | none => _) = _
      rw [ho]
    have ea : (M.subst N).ask (c, .inr (m, r)) = none := by
      change (match N.out r with | some _ => none | none => N.ask r) = _
      rw [ho, ha]
    have : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (t + 1 + T + 1) (L ++ L₂) :=
      .step rfl ea (by change size c + (size m + size r + 1) ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query r t L x w ho ha hw hs _ ih =>
    have ea : (M.subst N).ask (c, .inr (m, r)) = some x := by
      change (match N.out r with | some _ => none | none => N.ask r) = _
      rw [ho, ha]
    exact .query rfl ea hw (by change size c + (size m + size r + 1) ≤ _; omega) ih

/-- Queries answered by a machine with query access, from a state of the outer machine: own steps
add up, with two more for each query; the lists of queries of the answering runs are joined. -/
theorem subst_reaches {O : Q → Option A} {c : C} {s : M.σ} {own S S' : ℕ} {L : List Q} {b : β} {t : Q → ℕ} {L' : Q → List Q'} (h : M.Reaches O S b s own L)
    (hN : ∀ x ∈ L, ∀ v, O x = some v → N.Runs O' (c, x) (t x) (L' x) S' v) :
    (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (own + (L.map fun x => t x + 2).sum) (L.flatMap L') := by
  induction h with
  | halt ho hs => exact .halt ho (by change size c + (size _ + 1) ≤ _; omega)
  | @step s own L ho ha hs _ ih =>
    have e : (M.subst N).step (c, .inl s) = (c, .inl (M.step s)) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    have : (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (own + (L.map fun x => t x + 2).sum + 1) (L.flatMap L') :=
      .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ ih hN)
    exact this.mono (by omega) le_rfl
  | @query s own L x v ho ha hv hs _ ih =>
    have e : (M.subst N).step (c, .inl s) = (c, .inr (s, N.init (c, x))) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    have h1 := subst_inner (M := M) (c := c) (m := s) (Sg := size c + S + S' + 1) (hN x List.mem_cons_self v hv) (by omega)
      (ih fun y hy => hN y (List.mem_cons_of_mem _ hy))
    have : (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (t x + 1 + (own + (L.map fun x => t x + 2).sum) + 1) (L' x ++ L.flatMap L') :=
      .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ h1)
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
    exact this.mono (by omega) le_rfl

/-- The same in costs: if the answer to x costs at most t x at the prices w', the whole costs at
most own + Σ (t x + 2). -/
theorem subst_reaches_within {O : Q → Option A} {w' : Q' → ℕ} {c : C} {s : M.σ} {own S S' : ℕ} {L : List Q} {b : β} {t : Q → ℕ} (h : M.Reaches O S b s own L)
    (hN : ∀ x v, O x = some v → N.Within O' w' (c, x) (t x) S' v) :
    ∃ (own₂ : ℕ) (L₂ : List Q'), (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) own₂ L₂ ∧ own₂ + (L₂.map w').sum ≤ own + (L.map fun x => t x + 2).sum := by
  induction h with
  | halt ho hs => exact ⟨0, [], .halt ho (by change size c + (size _ + 1) ≤ _; omega), by simp⟩
  | @step s own L ho ha hs _ ih =>
    obtain ⟨o₂, L₂, hr, hle⟩ := ih
    have e : (M.subst N).step (c, .inl s) = (c, .inl (M.step s)) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    exact ⟨o₂ + 1, L₂, .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ hr), by omega⟩
  | @query s own L x v ho ha hv hs _ ih =>
    obtain ⟨o₂, L₂, hr, hle⟩ := ih
    obtain ⟨o₁, L₁, hr₁, hle₁⟩ := hN x v hv
    have e : (M.subst N).step (c, .inl s) = (c, .inr (s, N.init (c, x))) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    have h1 := subst_inner (M := M) (c := c) (m := s) (Sg := size c + S + S' + 1) hr₁ (by omega) hr
    exact ⟨o₁ + 1 + o₂ + 1, L₁ ++ L₂, .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ h1), by
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]; omega⟩

end Subst

/-! ## Two step machines with the same states are equal if their parts agree -/

/-- Two step machines with the same type of states and the same measure of size are equal if init,
step and out agree at every argument. -/
theorem stepped_eq {σ : Type} [HasSize σ] {i i' : α → σ} {st st' : σ → σ} {o o' : σ → Option β} (h1 : ∀ a, i a = i' a)
    (h2 : ∀ s, st s = st' s) (h3 : ∀ s, o s = o' s) : (⟨σ, i, st, o⟩ : Stepped α β) = ⟨σ, i', st', o'⟩ := by
  obtain rfl : i = i' := funext h1
  obtain rfl : st = st' := funext h2
  obtain rfl : o = o' := funext h3
  rfl

/-- Building the outer oracle into a substitution is plugging in the answering machine with that
oracle built in. -/
@[simp] theorem close_subst [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O' : Q' → Option A') :
    (M.subst N).close O' = M.plug (N.close O') :=
  stepped_eq (fun _ => rfl) (fun s => by
    rcases s with ⟨c, m | ⟨m, r⟩⟩
    · rfl
    · simp only [subst, plug, close]
      cases N.out r <;> simp only []
      cases N.ask r <;> simp only []
      cases O' _ <;> rfl) (fun s => by rcases s with ⟨c, m | p⟩ <;> rfl)

/-- A step machine, seen as a machine that asks nothing, runs as it did. -/
theorem reaches_asksNothing {R : Stepped α β} {O : Q → Option A} {S t : ℕ} {b : β} {s : R.σ} (h : R.Reaches S b s t) :
    ({ R with ask := fun _ => none, resume := fun s _ => s } : QueryMachine Q A α β).Reaches O S b s t [] := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho hs _ ih => exact .step ho rfl hs ih

/-- A run without queries is a run of the step machine underneath. -/
theorem toStepped_reaches {M : QueryMachine Q A α β} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ} (h : M.Reaches O S b s own L) (hL : L = []) :
    M.toStepped.Reaches S b s own := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho _ hs _ ih => exact .step ho hs (ih hL)
  | query _ _ _ _ _ _ => cases hL

end QueryMachines.QueryMachine

namespace QueryMachines

open Groundwork QueryMachine

/-- `StMono`. -/
theorem stMono : StMono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h ho hS => h.mono ho hS

/-- `StUnique`. -/
theorem stUnique : StUnique := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => Reaches.unique h h'

/-- `StWithinRules`. -/
theorem stWithinRules : StWithinRules := fun _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun ho hs => ⟨0, [], .halt ho hs, by simp⟩,
   fun ho ha hs ⟨own, L, hr, hle⟩ => ⟨own + 1, L, .step ho ha hs hr, by omega⟩,
   fun x v ho ha hv hs ⟨own, L, hr, hle⟩ => ⟨own, x :: L, .query ho ha hv hs hr, by simp only [List.map_cons, List.sum_cons]; omega⟩⟩

/-- `StClose`: cost at one operation per query is the number of steps with the oracle built in. -/
theorem stClose : StClose := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => let ⟨own, L, hr, hle⟩ := reaches_of_close h; ⟨own, L, hr, by rw [sum_map_unitCost]; exact hle⟩,
   fun ⟨own, L, hr, hle⟩ => (close_reaches hr).mono (by rw [sum_map_unitCost] at hle; exact hle) le_rfl⟩

/-- `StQueriesLe`: an algorithm that takes at most T operations makes at most T queries. -/
theorem stQueriesLe : StQueriesLe := fun _ _ _ _ _ _ _ _ _ _ ⟨own, L, hr, hle⟩ => ⟨own, L, hr, by rw [sum_map_unitCost] at hle; exact hle⟩

/-- `StSlowDown`: at t ≥ 1 operations per query, T operations become at most T·t. -/
theorem stSlowDown : StSlowDown := fun _ _ _ _ _ _ _ T _ t _ ht ⟨own, L, hr, hle⟩ => ⟨own, L, hr, by
  rw [sum_map_unitCost] at hle
  rw [sum_map_const]
  calc own + L.length * t ≤ own * t + L.length * t := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ ht) _
    _ = (own + L.length) * t := (Nat.add_mul _ _ _).symm
    _ ≤ T * t := Nat.mul_le_mul_right _ hle⟩

/-- `StSubst`. -/
theorem stSubst : StSubst := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hN => subst_reaches h hN

/-- `StPlug`, as the case of `StSubst` in which the answering machine asks nothing. -/
theorem stPlug : StPlug := fun Q A C _ _ _ M R _ c _ _ _ S' _ _ t h hR => by
  have h1 := subst_reaches (M := M) (N := ({ R with ask := fun _ => none, resume := fun s _ => s } : QueryMachine Empty Empty (C × Q) A)) (O' := fun _ => none)
    (c := c) (t := t) (L' := fun _ => []) (S' := S') h fun x hx v hv => reaches_asksNothing (hR x hx v hv)
  exact toStepped_reaches h1 (by simp)

/-- `StSubstWithin`. -/
theorem stSubstWithin : StSubstWithin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, L, hr, hle⟩ hN hw => by
  obtain ⟨own₂, L₂, h2, hle₂⟩ := subst_reaches_within hr hN
  exact ⟨own₂, L₂, h2, by
    have := List.sum_le_sum (l := L) fun x _ => hw x
    omega⟩

/-- `StCloseSubst`. -/
theorem stCloseSubst : StCloseSubst := fun _ _ _ _ _ _ _ _ M N O' => close_subst M N O'

end QueryMachines
