/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.CombRunsStatement
public import QueryMachines.Runs
import Mathlib.Tactic

/-! # How the constructions run

Proofs of the statements of proof/machines/QueryMachines/CombRunsStatement.lean. Each follows the
corresponding proof for step machines (`Stepped`), with the list of queries carried along. -/

public section

namespace QueryMachines.QueryMachine

open Groundwork Finset

variable {Q Q' A α α₁ α₂ β γ τ : Type}

/-- A step machine asks nothing (from a state). -/
theorem lift_reaches {R : Stepped α β} {O : Q → Option A} {S t : ℕ} {b : β} {s : R.σ} (h : R.Reaches S b s t) :
    (lift R : QueryMachine Q A α β).Reaches O S b s t [] := reaches_asksNothing h

/-- Queries rewritten by h (from a state). -/
theorem mapAsk_reaches {h : Q → Q'} {M : QueryMachine Q A α β} {O : Q' → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches (fun x => O (h x)) S b s own L) : (mapAsk h M).Reaches O S b s own (L.map h) := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih => exact .step ho (by change (M.ask _).map h = none; rw [ha]; rfl) hs ih
  | query ho ha hv hs _ ih => exact .query ho (by change (M.ask _).map h = _; rw [ha]; rfl) hv hs ih

/-- A function applied to the input (from a state). -/
theorem mapIn_reaches {g : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {S own : ℕ} {L : List Q} {c : γ} {s : M.σ}
    (hr : M.Reaches O S c s own L) : (mapIn g M).Reaches O S c s own L := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih => exact .step ho ha hs ih
  | query ho ha hv hs _ ih => exact .query ho ha hv hs ih

/-- A function applied to the result (from a state). -/
theorem mapOut_reaches {M : QueryMachine Q A α β} {g : β → γ} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches O S b s own L) : (mapOut M g).Reaches O S (g b) s own L := by
  induction hr with
  | halt ho hs => exact .halt (by change (M.out _).map g = _; rw [ho]; rfl) hs
  | step ho ha hs _ ih => exact .step (by change (M.out _).map g = _; rw [ho]; rfl) ha hs ih
  | query ho ha hv hs _ ih => exact .query (by change (M.out _).map g = _; rw [ho]; rfl) ha hv hs ih

/-- The second machine of `bind`, run inside. -/
theorem bind_reaches_inr [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {S t : ℕ} {L : List Q} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) : (bind M N).Reaches O (S + 1) c (.inr s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih

/-- `bind`, from a state of the first machine. -/
theorem bind_reaches [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {a : α} {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O (a, b) t' L' S' c) : (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s)) (t + 1 + t') (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (bind M N).step (.inl (a, s)) = .inr (N.init (a, b)) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (bind M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have : (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s)) (t' + 1) L' :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ (bind_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (bind M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (bind M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have : (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s)) (t + 1 + t' + 1) (L ++ L') :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query s t L x v ho ha hv hs _ ih =>
    have ea : (bind M N).ask (.inl (a, s)) = some x := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size a + size s + 1 ≤ _; omega) ih

/-- The second machine of `both`, run inside. -/
theorem both_reaches_inr [HasSize α] [HasSize β] {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) : (both M N).Reaches O (size b + S + 1) (b, c) (.inr (b, s)) t L := by
  induction h with
  | @halt s t ho hs => exact .halt (by change (N.out s).map _ = _; rw [ho]; rfl) (by change size b + size s + 1 ≤ _; omega)
  | @step s t L ho ha hs _ ih => exact .step (by change (N.out s).map _ = _; rw [ho]; rfl) ha (by change size b + size s + 1 ≤ _; omega) ih
  | @query s t L x v ho ha hv hs _ ih => exact .query (by change (N.out s).map _ = _; rw [ho]; rfl) ha hv (by change size b + size s + 1 ≤ _; omega) ih

/-- `both`, from a state of the first machine. -/
theorem both_reaches [HasSize α] [HasSize β] {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A} {a : α} {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O a t' L' S' c) : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t') (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (both M N).step (.inl (a, s)) = .inr (b, N.init a) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (both M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t' + 1) L' :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ (both_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (both M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (both M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t' + 1) (L ++ L') :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query s t L x v ho ha hv hs _ ih =>
    have ea : (both M N).ask (.inl (a, s)) = some x := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size a + size s + 1 ≤ _; omega) ih

/-- The left machine of `branch`, run inside. -/
theorem branch_reaches_inl {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₁.σ}
    (h : M₁.Reaches O S b s t L) : (branch sel M₁ M₂).Reaches O (S + 1) b (.inl s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih

/-- The right machine of `branch`, run inside. -/
theorem branch_reaches_inr {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₂.σ}
    (h : M₂.Reaches O S b s t L) : (branch sel M₁ M₂).Reaches O (S + 1) b (.inr s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih

section foldWhile

variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}

/-- The body, run inside the loop. -/
theorem foldWhile_body {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} {L L' : List Q} (h : M.Reaches O Sm b s t L) (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches O S r (Stepped.foldGo M.toStepped (g c x b) (nxt x)) T L') :
    (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (t + 1 + T) (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = Stepped.foldGo M.toStepped (g c x b) (nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have : (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (T + 1) L' :=
      .step rfl ea (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have : (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (t + 1 + T + 1) (L ++ L') :=
      .step rfl ea (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query s t L y v ho ha hv hs _ ih =>
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = some y := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size x + (size c + size s) + 1 ≤ _; omega) ih

/-- The loop, from the state with accumulator c and next point o. -/
theorem foldWhile_reaches {xs : List τ} {o : Option τ} (ho : Stepped.Orbit nxt o xs) (t : τ → ℕ) (Lq : τ → List Q) (v : τ → β) (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ xs, M.Runs O x (t x) (Lq x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx) (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches O (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) c) (Stepped.foldGo M.toStepped c o) (xs.map fun x => t x + 1).sum (xs.flatMap Lq) := by
  induction ho generalizing c with
  | nil =>
    have := hc [] (List.nil_prefix)
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at this; omega)
  | @cons x xs _ ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons, List.flatMap_cons]
    refine foldWhile_body (hM x List.mem_cons_self) ?_
      (ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl))
    have h1 := hx x List.mem_cons_self
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    omega

end foldWhile

/-- The points of the loop over y < N a. -/
theorem orbit_range (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Stepped.Orbit (Stepped.rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by
  induction k generalizing y with
  | zero => rw [if_neg (by omega)]; exact .nil
  | succ k ih =>
    rw [if_pos (by omega), List.range'_succ, List.map_cons]
    exact .cons (ih (y + 1) (by omega))

/-- A sum over a list of numbers 0, …, n − 1 as a sum over a range. -/
theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The loop over a range. -/
theorem foldRange_runs [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {a : α}
    (t : ℕ → ℕ) (Lq : ℕ → List Q) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs O (a, y) (t y) (Lq y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs O a (∑ y ∈ range (N a), (t y + 1)) ((List.range (N a)).flatMap Lq) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have ho := orbit_range N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have := foldWhile_reaches (start := Stepped.rangeStart N) (M := M) (g := Stepped.rangeG g) (c₀ := c₀) (O := O) ho (fun x => t x.2) (fun x => Lq x.2) (fun x => v x.2)
    (size a + size (N a)) Sc Sm (c₀ a)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size (List.mem_range.1 hy).le
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      exact hc _ (min_le_right _ _))
  rw [List.map_map, List.foldl_map, List.flatMap_map] at this
  rw [← sum_map_range]
  exact this

end QueryMachines.QueryMachine

namespace QueryMachines

open Groundwork Finset QueryMachine

/-- `StLiftRuns`. -/
theorem stLiftRuns : StLiftRuns := fun _ _ _ _ _ _ _ _ _ _ h => lift_reaches h

/-- `StQueryRuns`. -/
theorem stQueryRuns : StQueryRuns := fun _ _ _ _ _ _ _ a v hv =>
  .query rfl rfl hv (by change size a + 1 ≤ _; omega) (.halt rfl (by change size v + 1 ≤ _; omega))

/-- `StMapAskRuns`. -/
theorem stMapAskRuns : StMapAskRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => mapAsk_reaches h

/-- `StMapInRuns`. -/
theorem stMapInRuns : StMapInRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => mapIn_reaches h

/-- `StMapOutRuns`. -/
theorem stMapOutRuns : StMapOutRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => mapOut_reaches h

/-- `StBindRuns`. -/
theorem stBindRuns : StBindRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => bind_reaches h h'

/-- `StBothRuns`. -/
theorem stBothRuns : StBothRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' => both_reaches h h'

/-- `StBranchRuns`. -/
theorem stBranchRuns : StBranchRuns := fun _ _ _ _ _ _ sel M₁ M₂ _ a _ _ _ _ =>
  ⟨fun x hs h => by
    have e : (branch sel M₁ M₂).init a = .inl (M₁.init x) := by
      change (match sel a with | .inl x => _ | .inr y => _) = _
      rw [hs]
    unfold Runs
    rw [e]
    exact branch_reaches_inl h,
   fun y hs h => by
    have e : (branch sel M₁ M₂).init a = .inr (M₂.init y) := by
      change (match sel a with | .inl x => _ | .inr y => _) = _
      rw [hs]
    unfold Runs
    rw [e]
    exact branch_reaches_inr h⟩

/-- `StFoldWhileRuns`. -/
theorem stFoldWhileRuns : StFoldWhileRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ c₀ _ a _ ho t Lq v Sx Sc Sm hM hx hc =>
  foldWhile_reaches ho t Lq v Sx Sc Sm (c₀ a) hM hx hc

/-- `StFoldRangeRuns`. -/
theorem stFoldRangeRuns : StFoldRangeRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ t Lq v Sc Sm hM hc => foldRange_runs t Lq v Sc Sm hM hc

end QueryMachines
