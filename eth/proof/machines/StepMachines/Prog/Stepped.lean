/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachineStatements

/-! Computations cut into steps: lemmas on the model of StepMachineStatements.lean (HasSize,
Stepped, Reaches, Runs), what `Runs` means
for plain iteration of the step function, and basic ways to
build machines. -/

namespace Groundwork

section sizes

variable {α β : Type}

@[simp] public theorem size_nat (n : ℕ) : size n = n.size + 1 := rfl
@[simp] public theorem size_int (z : ℤ) : size z = z.natAbs.size + 1 := rfl
@[simp] public theorem size_bool (b : Bool) : size b = 1 := rfl
@[simp] public theorem size_unit (u : Unit) : size u = 1 := rfl
@[simp] public theorem size_prod [HasSize α] [HasSize β] (p : α × β) : size p = size p.1 + size p.2 := rfl
@[simp] public theorem size_inl [HasSize α] [HasSize β] (a : α) : size (Sum.inl a : α ⊕ β) = size a + 1 := rfl
@[simp] public theorem size_inr [HasSize α] [HasSize β] (b : β) : size (Sum.inr b : α ⊕ β) = size b + 1 := rfl
@[simp] public theorem size_none [HasSize α] : size (none : Option α) = 1 := rfl
@[simp] public theorem size_some [HasSize α] (a : α) : size (some a) = size a + 1 := rfl
@[simp] public theorem size_list [HasSize α] (l : List α) :
    size l = (l.map fun x => size x + 1).sum + 1 := rfl

end sizes

namespace Stepped

variable {α β γ τ : Type}

/-- One step of the iteration: a halted state stays as it is. -/
@[expose] public def next (M : Stepped α β) (s : M.σ) : M.σ :=
  match M.out s with
  | some _ => s
  | none => M.step s

/-- The state after exactly n steps of the iteration. -/
@[expose] public def run (M : Stepped α β) (a : α) (n : ℕ) : M.σ := M.next^[n] (M.init a)

public theorem Reaches.mono {M : Stepped α β} {S S' t t' : ℕ} {b : β} {s : M.σ} (h : M.Reaches S b s t)
    (ht : t ≤ t') (hS : S ≤ S') : M.Reaches S' b s t' := by
  induction h generalizing t' with
  | halt ho hs => exact .halt ho (hs.trans hS)
  | step ho hs _ ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    exact .step ho (hs.trans hS) (ih (by omega))

public theorem Runs.mono {M : Stepped α β} {S S' t t' : ℕ} {a : α} {b : β} (h : M.Runs a t S b)
    (ht : t ≤ t') (hS : S ≤ S') : M.Runs a t' S' b := Reaches.mono h ht hS

theorem next_iterate_of_out {M : Stepped α β} {s : M.σ} {b : β} (h : M.out s = some b) (n : ℕ) :
    M.next^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, next, h]

/-- What Reaches means for the iteration, run for a fixed number T ≥ t of steps. -/
public theorem Reaches.iterate {M : Stepped α β} {S t : ℕ} {b : β} {s : M.σ} (h : M.Reaches S b s t) :
    (∀ T, t ≤ T → M.out (M.next^[T] s) = some b) ∧ ∀ n, size (M.next^[n] s) ≤ S := by
  induction h with
  | halt ho hs => exact ⟨fun T _ => by rw [next_iterate_of_out ho, ho], fun n => by rwa [next_iterate_of_out ho]⟩
  | @step s t ho hs _ ih =>
    have e : M.next s = M.step s := by rw [next, ho]
    refine ⟨fun T hT => ?_, fun n => ?_⟩
    · obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      rw [Function.iterate_succ_apply, e]
      exact ih.1 T' (by omega)
    · cases n with
      | zero => exact hs
      | succ n => rw [Function.iterate_succ_apply, e]; exact ih.2 n

/-- After exactly T ≥ t steps of the iteration the result is there. -/
public theorem Runs.out_run {M : Stepped α β} {S t : ℕ} {a : α} {b : β} (h : M.Runs a t S b) {T : ℕ}
    (hT : t ≤ T) : M.out (M.run a T) = some b := (Reaches.iterate h).1 T hT

/-- The converse of `Reaches.iterate`: if the iteration has the result after t steps and all its
states have size ≤ S, then Runs holds. -/
public theorem runs_of_run {M : Stepped α β} {S t : ℕ} {a : α} {b : β} (ho : M.out (M.run a t) = some b)
    (hs : ∀ n, size (M.run a n) ≤ S) : M.Runs a t S b := by
  unfold Runs run at *
  generalize M.init a = s at ho hs
  induction t generalizing s with
  | zero => exact .halt ho (hs 0)
  | succ t ih =>
    cases h : M.out s with
    | some b' =>
      rw [next_iterate_of_out h, h] at ho
      exact .halt (h.trans ho) (hs 0)
    | none =>
      have e : M.next s = M.step s := by rw [next, h]
      refine .step h (hs 0) (ih _ ?_ fun n => ?_)
      · rwa [Function.iterate_succ_apply, e] at ho
      · have := hs (n + 1)
        rwa [Function.iterate_succ_apply, e] at this

/-- The result is unique. -/
public theorem Runs.unique {M : Stepped α β} {S S' t t' : ℕ} {a : α} {b b' : β} (h : M.Runs a t S b)
    (h' : M.Runs a t' S' b') : b = b' := by
  have h1 := h.out_run (le_max_left t t')
  have h2 := h'.out_run (le_max_right t t')
  exact Option.some.inj (h1.symm.trans h2)

/-! ### One step, pre- and post-composition -/

/-- f in one step. -/
@[expose] public def ofFun [HasSize α] [HasSize β] (f : α → β) : Stepped α β where
  σ := α ⊕ β
  init := .inl
  step s := match s with | .inl a => .inr (f a) | .inr b => .inr b
  out s := match s with | .inl _ => none | .inr b => some b

public theorem ofFun_runs [HasSize α] [HasSize β] (f : α → β) (a : α) :
    (ofFun f).Runs a 1 (max (size a) (size (f a)) + 1) (f a) :=
  .step rfl (by change size a + 1 ≤ _; omega) (.halt rfl (by change size (f a) + 1 ≤ _; omega))

/-- M on f a. No further step. -/
@[expose] public def mapIn (f : α → β) (M : Stepped β γ) : Stepped α γ where
  σ := M.σ
  init a := M.init (f a)
  step := M.step
  out := M.out

theorem mapIn_reaches {f : α → β} {M : Stepped β γ} {s : M.σ} {t S : ℕ} {c : γ} (h : M.Reaches S c s t) :
    (mapIn f M).Reaches S c s t := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho hs _ ih => exact .step ho hs ih

public theorem mapIn_runs {f : α → β} {M : Stepped β γ} {a : α} {t S : ℕ} {c : γ} (h : M.Runs (f a) t S c) :
    (mapIn f M).Runs a t S c := mapIn_reaches h

/-- f applied to the result of M. No further step. -/
@[expose] public def mapOut (M : Stepped α β) (f : β → γ) : Stepped α γ where
  σ := M.σ
  init := M.init
  step := M.step
  out s := (M.out s).map f

theorem mapOut_reaches {M : Stepped α β} {f : β → γ} {s : M.σ} {t S : ℕ} {b : β} (h : M.Reaches S b s t) :
    (mapOut M f).Reaches S (f b) s t := by
  induction h with
  | halt ho hs => exact .halt (by change (M.out _).map f = _; rw [ho]; rfl) hs
  | step ho hs _ ih => exact .step (by change (M.out _).map f = _; rw [ho]; rfl) hs ih

public theorem mapOut_runs {M : Stepped α β} {f : β → γ} {a : α} {t S : ℕ} {b : β} (h : M.Runs a t S b) :
    (mapOut M f).Runs a t S (f b) := mapOut_reaches h

/-! ### Composition -/

/-- M, then N on the input together with the result of M. -/
@[expose] public def bind [HasSize α] (M : Stepped α β) (N : Stepped (α × β) γ) : Stepped α γ where
  σ := (α × M.σ) ⊕ N.σ
  init a := .inl (a, M.init a)
  step s := match s with
    | .inl p => match M.out p.2 with
      | some b => .inr (N.init (p.1, b))
      | none => .inl (p.1, M.step p.2)
    | .inr s => .inr (N.step s)
  out s := match s with | .inl _ => none | .inr s => N.out s

theorem bind_reaches_inr [HasSize α] {M : Stepped α β} {N : Stepped (α × β) γ} {S t : ℕ} {c : γ} {s : N.σ}
    (h : N.Reaches S c s t) : (bind M N).Reaches (S + 1) c (.inr s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih

public theorem bind_runs [HasSize α] {M : Stepped α β} {N : Stepped (α × β) γ} {a : α} {t t' S S' : ℕ}
    {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs (a, b) t' S' c) :
    (bind M N).Runs a (t + 1 + t') (max (size a + S) S' + 1) c := by
  unfold Runs at *
  change (bind M N).Reaches _ c (.inl (a, M.init a)) _
  generalize M.init a = s at h
  induction h with
  | @halt s t ho hs =>
    have e : (bind M N).step (.inl (a, s)) = .inr (N.init (a, b)) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (bind M N).Reaches (max (size a + S) S' + 1) c (.inl (a, s)) (t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega)
        (e ▸ (bind_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (bind M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (bind M N).Reaches (max (size a + S) S' + 1) c (.inl (a, s)) (t + 1 + t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl

/-! ### The loop -/

/-- Orbit nxt o xs: xs is the list x, nxt x, nxt (nxt x), … from o = some x up to the point where
nxt gives none;
xs = [] if o = none. -/
public inductive Orbit (nxt : τ → Option τ) : Option τ → List τ → Prop
  | nil : Orbit nxt none []
  | cons {x : τ} {xs : List τ} : Orbit nxt (nxt x) xs → Orbit nxt (some x) (x :: xs)

/-- The loop's state with accumulator c and next point x: the body starts at x, or the loop halts
with c if x = none. -/
@[expose] public def foldGo (M : Stepped τ β) (c : γ) (x : Option τ) :
    (τ × γ × M.σ) ⊕ γ :=
  match x with
  | some x' => .inl (x', c, M.init x')
  | none => .inr c

/-- The loop: run M at x = start a, fold its result into the accumulator by g, go on to nxt x; halt
at none. -/
@[expose] public def foldWhile [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ)
    (M : Stepped τ β) (g : γ → τ → β → γ) (c₀ : α → γ) : Stepped α γ where
  σ := (τ × γ × M.σ) ⊕ γ
  init a := foldGo M (c₀ a) (start a)
  step s := match s with
    | .inl p => match M.out p.2.2 with
      | some b => foldGo M (g p.2.1 p.1 b) (nxt p.1)
      | none => .inl (p.1, p.2.1, M.step p.2.2)
    | .inr c => .inr c
  out s := match s with | .inl _ => none | .inr c => some c

section foldWhile

variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β}
  {g : γ → τ → β → γ} {c₀ : α → γ}

/-- The body, run inside the loop. -/
theorem foldWhile_body {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm b s t)
    (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches S r (foldGo M (g c x b) (nxt x)) T) :
    (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T) := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = foldGo M (g c x b) (nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl

theorem foldWhile_reaches {xs : List τ} {o : Option τ} (ho : Orbit nxt o xs) (t : τ → ℕ) (v : τ → β)
    (Sx Sc Sm : ℕ) (c : γ) (hM : ∀ x ∈ xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) c)
      (foldGo M c o) (xs.map fun x => t x + 1).sum := by
  induction ho generalizing c with
  | nil =>
    have := hc [] (List.nil_prefix)
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at this; omega)
  | @cons x xs _ ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    refine foldWhile_body (hM x List.mem_cons_self) ?_
      (ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy))
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl))
    have h1 := hx x List.mem_cons_self
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    omega

/-- The loop: steps = Σ over the orbit of (steps of the body + 1); result = the fold over the orbit. -/
public theorem foldWhile_runs {a : α} {xs : List τ} (ho : Orbit nxt (start a) xs) (t : τ → ℕ) (v : τ → β)
    (Sx Sc Sm : ℕ) (hM : ∀ x ∈ xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) :
    (foldWhile start nxt M g c₀).Runs a (xs.map fun x => t x + 1).sum (Sx + (Sc + Sm) + 1)
      (xs.foldl (fun c x => g c x (v x)) (c₀ a)) :=
  foldWhile_reaches ho t v Sx Sc Sm (c₀ a) hM hx hc

end foldWhile

end Stepped

end Groundwork
