/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Stepped

/-! Further combinators: a choice between two computations (branch, ite, optBind), two computations
on one input
(both, map2, mul2), constants. -/

namespace Groundwork.Stepped

variable {α α₁ α₂ β γ δ ι : Type}

/-! ### Choice -/

/-- M₁ on x if sel a = inl x, M₂ on y if sel a = inr y. No further step. -/
@[expose] public def branch (sel : α → α₁ ⊕ α₂) (M₁ : Stepped α₁ β) (M₂ : Stepped α₂ β) : Stepped α β where
  σ := M₁.σ ⊕ M₂.σ
  init a := match sel a with | .inl x => .inl (M₁.init x) | .inr y => .inr (M₂.init y)
  step s := match s with | .inl s => .inl (M₁.step s) | .inr s => .inr (M₂.step s)
  out s := match s with | .inl s => M₁.out s | .inr s => M₂.out s

theorem branch_reaches_inl {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {S t : ℕ} {b : β}
    {s : M₁.σ} (h : M₁.Reaches S b s t) : (branch sel M₁ M₂).Reaches (S + 1) b (.inl s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih

theorem branch_reaches_inr {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {S t : ℕ} {b : β}
    {s : M₂.σ} (h : M₂.Reaches S b s t) : (branch sel M₁ M₂).Reaches (S + 1) b (.inr s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih

public theorem branch_runs_inl {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {a : α} {x : α₁}
    {S t : ℕ} {b : β} (hs : sel a = .inl x) (h : M₁.Runs x t S b) : (branch sel M₁ M₂).Runs a t (S + 1) b := by
  have e : (branch sel M₁ M₂).init a = .inl (M₁.init x) := by
    change (match sel a with | .inl x => _ | .inr y => _) = _
    rw [hs]
  unfold Runs
  rw [e]
  exact branch_reaches_inl h

public theorem branch_runs_inr {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {a : α} {y : α₂}
    {S t : ℕ} {b : β} (hs : sel a = .inr y) (h : M₂.Runs y t S b) : (branch sel M₁ M₂).Runs a t (S + 1) b := by
  have e : (branch sel M₁ M₂).init a = .inr (M₂.init y) := by
    change (match sel a with | .inl x => _ | .inr y => _) = _
    rw [hs]
  unfold Runs
  rw [e]
  exact branch_reaches_inr h

/-- Left if p a, else right. -/
@[expose] public def iteSel (p : α → Bool) (a : α) : α ⊕ α := if p a then .inl a else .inr a

/-- M if p a, else N, on the same input. No further step. -/
@[expose] public def ite (p : α → Bool) (M N : Stepped α β) : Stepped α β := branch (iteSel p) M N

public theorem ite_runs_true {p : α → Bool} {M N : Stepped α β} {a : α} {S t : ℕ} {b : β} (hp : p a = true)
    (h : M.Runs a t S b) : (ite p M N).Runs a t (S + 1) b :=
  branch_runs_inl (by simp [iteSel, hp]) h

public theorem ite_runs_false {p : α → Bool} {M N : Stepped α β} {a : α} {S t : ℕ} {b : β} (hp : p a = false)
    (h : N.Runs a t S b) : (ite p M N).Runs a t (S + 1) b :=
  branch_runs_inr (by simp [iteSel, hp]) h

/-- The result b, whatever the input; one step. -/
@[expose] public def const [HasSize α] [HasSize β] (b : β) : Stepped α β := ofFun (Function.const α b)

public theorem const_runs [HasSize α] [HasSize β] (b : β) (a : α) :
    (const b : Stepped α β).Runs a 1 (max (size a) (size b) + 1) b := ofFun_runs _ a

/-- Left with (a, i) at (a, some i), right with a at (a, none). -/
@[expose] public def optSel (x : α × Option ι) : (α × ι) ⊕ α :=
  match x.2 with | some i => .inl (x.1, i) | none => .inr x.1

/-- M; if its result is some i, then N on (a, i); if none, then dflt a. -/
@[expose] public def optBind [HasSize α] [HasSize β] (M : Stepped α (Option ι)) (N : Stepped (α × ι) β)
    (dflt : α → β) : Stepped α β :=
  bind M (branch optSel N (ofFun dflt))

public theorem optBind_runs_some [HasSize α] [HasSize β] {M : Stepped α (Option ι)} {N : Stepped (α × ι) β}
    {dflt : α → β} {a : α} {i : ι} {t t' S S' : ℕ} {b : β} (h : M.Runs a t S (some i))
    (h' : N.Runs (a, i) t' S' b) : (optBind M N dflt).Runs a (t + 1 + t') (max (size a + S) (S' + 1) + 1) b :=
  bind_runs h (branch_runs_inl rfl h')

/-! ### Two computations on one input -/

/-- M, then N, on the same input; both results. -/
@[expose] public def both [HasSize α] [HasSize β] (M : Stepped α β) (N : Stepped α γ) : Stepped α (β × γ) where
  σ := (α × M.σ) ⊕ (β × N.σ)
  init a := .inl (a, M.init a)
  step s := match s with
    | .inl p => match M.out p.2 with
      | some b => .inr (b, N.init p.1)
      | none => .inl (p.1, M.step p.2)
    | .inr p => .inr (p.1, N.step p.2)
  out s := match s with | .inl _ => none | .inr p => (N.out p.2).map fun c => (p.1, c)

theorem both_reaches_inr [HasSize α] [HasSize β] {M : Stepped α β} {N : Stepped α γ} {S t : ℕ} {b : β} {c : γ}
    {s : N.σ} (h : N.Reaches S c s t) : (both M N).Reaches (size b + S + 1) (b, c) (.inr (b, s)) t := by
  induction h with
  | @halt s t ho hs =>
    exact .halt (by change (N.out s).map _ = _; rw [ho]; rfl) (by change size b + size s + 1 ≤ _; omega)
  | @step s t ho hs _ ih =>
    exact .step (by change (N.out s).map _ = _; rw [ho]; rfl) (by change size b + size s + 1 ≤ _; omega) ih

public theorem both_runs [HasSize α] [HasSize β] {M : Stepped α β} {N : Stepped α γ} {a : α} {t t' S S' : ℕ}
    {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (both M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (b, c) := by
  unfold Runs at *
  change (both M N).Reaches _ (b, c) (.inl (a, M.init a)) _
  generalize M.init a = s at h
  induction h with
  | @halt s t ho hs =>
    have e : (both M N).step (.inl (a, s)) = .inr (b, N.init a) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (both M N).Reaches (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega)
        (e ▸ (both_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (both M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (both M N).Reaches (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl

/-- f of the results of M and N on the same input. -/
@[expose] public def map2 [HasSize α] [HasSize β] (f : β → γ → δ) (M : Stepped α β) (N : Stepped α γ) :
    Stepped α δ :=
  mapOut (both M N) (Function.uncurry f)

public theorem map2_runs [HasSize α] [HasSize β] {f : β → γ → δ} {M : Stepped α β} {N : Stepped α γ} {a : α}
    {t t' S S' : ℕ} {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (map2 f M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (f b c) :=
  mapOut_runs (both_runs h h')

/-- The product of the results of M and N on the same input. -/
@[expose] public def mul2 [HasSize α] (M N : Stepped α ℤ) : Stepped α ℤ := map2 Int.mul M N

public theorem mul2_runs [HasSize α] {M N : Stepped α ℤ} {a : α} {t t' S S' : ℕ} {b c : ℤ}
    (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (mul2 M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (b * c) :=
  map2_runs h h'

end Groundwork.Stepped
