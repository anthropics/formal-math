/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.CombDefs
import QueryMachines.Runs
import Mathlib.Tactic

/-! # A machine that runs step for step as another, on a wider input

Let w : α → α' widen the input (for instance: put K and g, in unary, beside it).
`Follows M M' w d φ` says that the map φ from the states of M to the states of M' carries the run of
M on a to the run of M' on w a: it commutes with `init`, `step` and `resume`, keeps `out` and `ask`,
and makes a state larger by at most d.
`Mirrors M M' w d` says that there is such a map. Then every run of M on a is a run of M' on w a
with the same result, the same number of own steps and the same list of queries, on states larger by
at most d (`Mirrors.runs`).
For each way to build machines of proof/machines/QueryMachines/CombDefs.lean that the programs of
the proof of Lemma 1 use there is one lemma: if the parts mirror each other, and the plain functions
agree along w, then so do the machines built. The number d is counted along: a construction that
keeps the input in its state (`bind`, the loops) adds the growth of the input. -/

@[expose] public section

namespace ExplicitCost

open Groundwork QueryMachines

variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}

/-- φ carries the runs of M on a to the runs of M' on w a; states grow by at most d. -/
structure Follows (M : QueryMachine Q A α β) (M' : QueryMachine Q A α' β) (w : α → α') (d : ℕ) (φ : M.σ → M'.σ) : Prop where
  init : ∀ a, M'.init (w a) = φ (M.init a)
  out : ∀ s, M'.out (φ s) = M.out s
  ask : ∀ s, M'.ask (φ s) = M.ask s
  step : ∀ s, M'.step (φ s) = φ (M.step s)
  resume : ∀ s v, M'.resume (φ s) v = φ (M.resume s v)
  size : ∀ s, size (φ s) ≤ size s + d

/-- M' on w a runs step for step as M on a; states grow by at most d. -/
def Mirrors (M : QueryMachine Q A α β) (M' : QueryMachine Q A α' β) (w : α → α') (d : ℕ) : Prop := ∃ φ : M.σ → M'.σ, Follows M M' w d φ

/-- A run from s gives a run from φ s. -/
theorem Follows.reaches {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} {φ : M.σ → M'.σ} (h : Follows M M' w d φ) {O : Q → Option A} {S own : ℕ} {b : β} {s : M.σ} {L : List Q}
    (r : M.Reaches O S b s own L) : M'.Reaches O (S + d) b (φ s) own L := by
  induction r with
  | halt ho hs => exact .halt ((h.out _).trans ho) ((h.size _).trans (Nat.add_le_add_right hs d))
  | step ho ha hs _ ih => exact .step ((h.out _).trans ho) ((h.ask _).trans ha) ((h.size _).trans (Nat.add_le_add_right hs d)) (by rw [h.step]; exact ih)
  | query ho ha hv hs _ ih => exact .query ((h.out _).trans ho) ((h.ask _).trans ha) hv ((h.size _).trans (Nat.add_le_add_right hs d)) (by rw [h.resume]; exact ih)

/-- **The same result, own steps and queries**, on states larger by at most d. -/
theorem Mirrors.runs {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) {O : Q → Option A} {a : α} {own S : ℕ} {L : List Q} {b : β}
    (r : M.Runs O a own L S b) : M'.Runs O (w a) own L (S + d) b := by
  obtain ⟨φ, h⟩ := h
  unfold QueryMachine.Runs
  rw [h.init]
  exact h.reaches r

/-- The same in costs. -/
theorem Mirrors.within {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) {O : Q → Option A} {p : Q → ℕ} {a : α} {T S : ℕ} {b : β}
    (r : M.Within O p a T S b) : M'.Within O p (w a) T (S + d) b := by
  obtain ⟨own, L, r, hle⟩ := r
  exact ⟨own, L, h.runs r, hle⟩

/-- The bound on the growth may be raised. -/
theorem Mirrors.mono {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d d' : ℕ} (h : Mirrors M M' w d) (hd : d ≤ d') : Mirrors M M' w d' := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ, { h with size := fun s => (h.size s).trans (Nat.add_le_add_left hd _) }⟩

/-! ## One lemma for each construction -/

/-- One query. -/
theorem mirrors_query [HasSize α] [HasSize α'] [HasSize A] {h : α → Q} {h' : α' → Q} {w : α → α'} {d : ℕ} (hh : ∀ a, h' (w a) = h a) (hw : ∀ a, size (w a) ≤ size a + d) :
    Mirrors (QueryMachine.query h : QueryMachine Q A α A) (QueryMachine.query h') w d :=
  ⟨(Sum.map w id : α ⊕ A → α' ⊕ A),
    { init := fun _ => rfl
      out := fun s => by rcases s with a | v <;> rfl
      ask := fun s => by
        rcases s with a | v
        · exact congrArg some (hh a)
        · rfl
      step := fun _ => rfl
      resume := fun _ _ => rfl
      size := fun s => by
        rcases s with a | v
        · change size (w a) + 1 ≤ size a + 1 + d
          have := hw a
          omega
        · change size v + 1 ≤ size v + 1 + d
          omega }⟩

/-- A constant. -/
theorem mirrors_const [HasSize α] [HasSize α'] [HasSize β] (b : β) {w : α → α'} {d : ℕ} (hw : ∀ a, size (w a) ≤ size a + d) :
    Mirrors (QueryMachine.const b : QueryMachine Q A α β) (QueryMachine.const b) w d :=
  ⟨(Sum.map w id : α ⊕ β → α' ⊕ β),
    { init := fun _ => rfl
      out := fun s => by rcases s with a | v <;> rfl
      ask := fun _ => rfl
      step := fun s => by rcases s with a | v <;> rfl
      resume := fun _ _ => rfl
      size := fun s => by
        rcases s with a | v
        · change size (w a) + 1 ≤ size a + 1 + d
          have := hw a
          omega
        · change size v + 1 ≤ size v + 1 + d
          omega }⟩

/-- A function applied to the input. -/
theorem Mirrors.mapIn {M : QueryMachine Q A β γ} {M' : QueryMachine Q A β' γ} {w₂ : β → β'} {d : ℕ} (h : Mirrors M M' w₂ d) {g : α → β} {g' : α' → β'} {w : α → α'} (hg : ∀ a, g' (w a) = w₂ (g a)) :
    Mirrors (QueryMachine.mapIn g M) (QueryMachine.mapIn g' M') w d := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ,
    { init := fun a => by
        change M'.init (g' (w a)) = φ (M.init (g a))
        rw [hg, h.init]
      out := h.out, ask := h.ask, step := h.step, resume := h.resume, size := h.size }⟩

/-- A function applied to the result. -/
theorem Mirrors.mapOut {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) (g : β → γ) :
    Mirrors (QueryMachine.mapOut M g) (QueryMachine.mapOut M' g) w d := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ,
    { init := h.init
      out := fun s => congrArg (Option.map g) (h.out s)
      ask := h.ask, step := h.step, resume := h.resume, size := h.size }⟩

/-- A choice between two machines. -/
theorem Mirrors.branch {M₁ : QueryMachine Q A α₁ β} {M₁' : QueryMachine Q A α₁' β} {M₂ : QueryMachine Q A α₂ β} {M₂' : QueryMachine Q A α₂' β} {w₁ : α₁ → α₁'} {w₂ : α₂ → α₂'} {d : ℕ}
    (h₁ : Mirrors M₁ M₁' w₁ d) (h₂ : Mirrors M₂ M₂' w₂ d) {sel : α → α₁ ⊕ α₂} {sel' : α' → α₁' ⊕ α₂'} {w : α → α'} (hs : ∀ a, sel' (w a) = Sum.map w₁ w₂ (sel a)) :
    Mirrors (QueryMachine.branch sel M₁ M₂) (QueryMachine.branch sel' M₁' M₂') w d := by
  obtain ⟨φ₁, h₁⟩ := h₁
  obtain ⟨φ₂, h₂⟩ := h₂
  exact ⟨(Sum.map φ₁ φ₂ : M₁.σ ⊕ M₂.σ → M₁'.σ ⊕ M₂'.σ),
    { init := fun a => by
        change (match sel' (w a) with | .inl x => (.inl (M₁'.init x) : M₁'.σ ⊕ M₂'.σ) | .inr y => .inr (M₂'.init y)) =
          Sum.map φ₁ φ₂ (match sel a with | .inl x => (.inl (M₁.init x) : M₁.σ ⊕ M₂.σ) | .inr y => .inr (M₂.init y))
        rw [hs]
        cases sel a with
        | inl x => exact congrArg Sum.inl (h₁.init x)
        | inr y => exact congrArg Sum.inr (h₂.init y)
      out := fun s => by
        rcases s with s | s
        · exact h₁.out s
        · exact h₂.out s
      ask := fun s => by
        rcases s with s | s
        · exact h₁.ask s
        · exact h₂.ask s
      step := fun s => by
        rcases s with s | s
        · exact congrArg Sum.inl (h₁.step s)
        · exact congrArg Sum.inr (h₂.step s)
      resume := fun s v => by
        rcases s with s | s
        · exact congrArg Sum.inl (h₁.resume s v)
        · exact congrArg Sum.inr (h₂.resume s v)
      size := fun s => by
        rcases s with s | s
        · change size (φ₁ s) + 1 ≤ size s + 1 + d
          have := h₁.size s
          omega
        · change size (φ₂ s) + 1 ≤ size s + 1 + d
          have := h₂.size s
          omega }⟩

/-- A choice by a test. -/
theorem Mirrors.ite {M N : QueryMachine Q A α β} {M' N' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (hM : Mirrors M M' w d) (hN : Mirrors N N' w d) {p : α → Bool} {p' : α' → Bool} (hp : ∀ a, p' (w a) = p a) :
    Mirrors (QueryMachine.ite p M N) (QueryMachine.ite p' M' N') w d :=
  Mirrors.branch hM hN fun a => by
    unfold Stepped.iteSel
    rw [hp a]
    cases p a <;> rfl

/-- One machine after the other. The first part runs beside a copy of the input. -/
theorem Mirrors.bind [HasSize α] [HasSize α'] {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {N : QueryMachine Q A (α × β) γ} {N' : QueryMachine Q A (α' × β) γ} {w : α → α'} {d₁ d₂ dw d : ℕ}
    (hM : Mirrors M M' w d₁) (hN : Mirrors N N' (Prod.map w id) d₂) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) (h2 : d₂ ≤ d) :
    Mirrors (QueryMachine.bind M N) (QueryMachine.bind M' N') w d := by
  obtain ⟨φ, hM⟩ := hM
  obtain ⟨ψ, hN⟩ := hN
  exact ⟨(Sum.map (Prod.map w φ) ψ : (α × M.σ) ⊕ N.σ → (α' × M'.σ) ⊕ N'.σ),
    { init := fun a => congrArg (fun s => (Sum.inl (w a, s) : (α' × M'.σ) ⊕ N'.σ)) (hM.init a)
      out := fun s => by
        rcases s with p | s
        · rfl
        · exact hN.out s
      ask := fun s => by
        rcases s with p | s
        · change (match M'.out (φ p.2) with | some _ => none | none => M'.ask (φ p.2)) = (match M.out p.2 with | some _ => none | none => M.ask p.2)
          rw [hM.out, hM.ask]
        · exact hN.ask s
      step := fun s => by
        rcases s with p | s
        · change (match M'.out (φ p.2) with | some b => (.inr (N'.init (w p.1, b)) : (α' × M'.σ) ⊕ N'.σ) | none => .inl (w p.1, M'.step (φ p.2))) =
            Sum.map (Prod.map w φ) ψ (match M.out p.2 with | some b => (.inr (N.init (p.1, b)) : (α × M.σ) ⊕ N.σ) | none => .inl (p.1, M.step p.2))
          rw [hM.out]
          cases M.out p.2 with
          | none => exact congrArg (fun s => (Sum.inl (w p.1, s) : (α' × M'.σ) ⊕ N'.σ)) (hM.step p.2)
          | some b => exact congrArg Sum.inr (hN.init (p.1, b))
        · exact congrArg Sum.inr (hN.step s)
      resume := fun s v => by
        rcases s with p | s
        · exact congrArg (fun s => (Sum.inl (w p.1, s) : (α' × M'.σ) ⊕ N'.σ)) (hM.resume p.2 v)
        · exact congrArg Sum.inr (hN.resume s v)
      size := fun s => by
        rcases s with p | s
        · change size (w p.1) + size (φ p.2) + 1 ≤ size p.1 + size p.2 + 1 + d
          have := hw p.1
          have := hM.size p.2
          omega
        · change size (ψ s) + 1 ≤ size s + 1 + d
          have := hN.size s
          omega }⟩

/-- The loop. The body runs beside the point of the loop, which holds a copy of the input. -/
theorem Mirrors.foldWhile [HasSize τ] [HasSize τ'] [HasSize γ] {M : QueryMachine Q A τ β} {M' : QueryMachine Q A τ' β} {wt : τ → τ'} {d₁ dw d : ℕ} (hM : Mirrors M M' wt d₁)
    {start : α → Option τ} {start' : α' → Option τ'} {nxt : τ → Option τ} {nxt' : τ' → Option τ'} {g : γ → τ → β → γ} {g' : γ → τ' → β → γ} {c₀ : α → γ} {c₀' : α' → γ} {w : α → α'}
    (hs : ∀ a, start' (w a) = (start a).map wt) (hn : ∀ t, nxt' (wt t) = (nxt t).map wt) (hg : ∀ c t b, g' c (wt t) b = g c t b) (hc : ∀ a, c₀' (w a) = c₀ a)
    (hw : ∀ t, size (wt t) ≤ size t + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.foldWhile start nxt M g c₀) (QueryMachine.foldWhile start' nxt' M' g' c₀') w d := by
  obtain ⟨φ, hM⟩ := hM
  have key : ∀ (c : γ) (o : Option τ), Stepped.foldGo M'.toStepped c (o.map wt) =
      (Sum.map (fun p : τ × γ × M.σ => ((wt p.1, p.2.1, φ p.2.2) : τ' × γ × M'.σ)) id : (τ × γ × M.σ) ⊕ γ → (τ' × γ × M'.σ) ⊕ γ) (Stepped.foldGo M.toStepped c o) := by
    intro c o
    cases o with
    | none => rfl
    | some x => exact congrArg (fun s => (Sum.inl (wt x, c, s) : (τ' × γ × M'.σ) ⊕ γ)) (hM.init x)
  exact ⟨(Sum.map (fun p : τ × γ × M.σ => ((wt p.1, p.2.1, φ p.2.2) : τ' × γ × M'.σ)) id : (τ × γ × M.σ) ⊕ γ → (τ' × γ × M'.σ) ⊕ γ),
    { init := fun a => by
        change Stepped.foldGo M'.toStepped (c₀' (w a)) (start' (w a)) = _
        rw [hc, hs]
        exact key _ _
      out := fun s => by rcases s with p | c <;> rfl
      ask := fun s => by
        rcases s with p | c
        · change (match M'.out (φ p.2.2) with | some _ => none | none => M'.ask (φ p.2.2)) = (match M.out p.2.2 with | some _ => none | none => M.ask p.2.2)
          rw [hM.out, hM.ask]
        · rfl
      step := fun s => by
        rcases s with p | c
        · change (match M'.out (φ p.2.2) with | some b => Stepped.foldGo M'.toStepped (g' p.2.1 (wt p.1) b) (nxt' (wt p.1)) | none => .inl (wt p.1, p.2.1, M'.step (φ p.2.2))) =
            Sum.map (fun p : τ × γ × M.σ => ((wt p.1, p.2.1, φ p.2.2) : τ' × γ × M'.σ)) id
              (match M.out p.2.2 with | some b => Stepped.foldGo M.toStepped (g p.2.1 p.1 b) (nxt p.1) | none => .inl (p.1, p.2.1, M.step p.2.2))
          rw [hM.out]
          cases M.out p.2.2 with
          | none => exact congrArg (fun s => (Sum.inl (wt p.1, p.2.1, s) : (τ' × γ × M'.σ) ⊕ γ)) (hM.step p.2.2)
          | some b =>
            change Stepped.foldGo M'.toStepped (g' p.2.1 (wt p.1) b) (nxt' (wt p.1)) = _
            rw [hg, hn]
            exact key _ _
        · rfl
      resume := fun s v => by
        rcases s with p | c
        · exact congrArg (fun s => (Sum.inl (wt p.1, p.2.1, s) : (τ' × γ × M'.σ) ⊕ γ)) (hM.resume p.2.2 v)
        · rfl
      size := fun s => by
        rcases s with p | c
        · change size (wt p.1) + (size p.2.1 + size (φ p.2.2)) + 1 ≤ size p.1 + (size p.2.1 + size p.2.2) + 1 + d
          have := hw p.1
          have := hM.size p.2.2
          omega
        · change size c + 1 ≤ size c + 1 + d
          omega }⟩

/-- The loop over a range. -/
theorem Mirrors.foldRange [HasSize α] [HasSize α'] [HasSize γ] {M : QueryMachine Q A (α × ℕ) β} {M' : QueryMachine Q A (α' × ℕ) β} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (g : γ → ℕ → β → γ) {c₀ : α → γ} {c₀' : α' → γ} (hN : ∀ a, N' (w a) = N a) (hc : ∀ a, c₀' (w a) = c₀ a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.foldRange N M g c₀) (QueryMachine.foldRange N' M' g c₀') w d :=
  Mirrors.foldWhile hM
    (fun a => by
      unfold Stepped.rangeStart
      rw [hN a]
      split <;> rfl)
    (fun t => by
      unfold Stepped.rangeNext
      change (if t.2 + 1 < N' (w t.1) then some (w t.1, t.2 + 1) else none) = _
      rw [hN t.1]
      split <;> rfl)
    (fun _ _ _ => rfl) hc
    (fun t => by
      change size (w t.1) + size t.2 ≤ size t.1 + size t.2 + dw
      have := hw t.1
      omega) h1

/-- The sum over a range. -/
theorem Mirrors.sumRange [HasSize α] [HasSize α'] {M : QueryMachine Q A (α × ℕ) ℤ} {M' : QueryMachine Q A (α' × ℕ) ℤ} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (hN : ∀ a, N' (w a) = N a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.sumRange N M) (QueryMachine.sumRange N' M') w d :=
  Mirrors.foldRange hM Stepped.addG hN (fun _ => rfl) hw h1

/-- The product over a range. -/
theorem Mirrors.prodRange [HasSize α] [HasSize α'] {M : QueryMachine Q A (α × ℕ) ℤ} {M' : QueryMachine Q A (α' × ℕ) ℤ} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (hN : ∀ a, N' (w a) = N a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.prodRange N M) (QueryMachine.prodRange N' M') w d :=
  Mirrors.foldRange hM Stepped.mulG hN (fun _ => rfl) hw h1

/-- A machine behind a test. The test runs beside a copy of the input. -/
theorem Mirrors.gated [HasSize α] [HasSize α'] {M : QueryMachine Q A α Bool} {M' : QueryMachine Q A α' Bool} {N : QueryMachine Q A α ℤ} {N' : QueryMachine Q A α' ℤ} {w : α → α'} {d₁ d₂ dw d : ℕ}
    (hM : Mirrors M M' w d₁) (hN : Mirrors N N' w d₂) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) (h2 : d₂ ≤ d) :
    Mirrors (QueryMachine.gated M N) (QueryMachine.gated M' N') w d :=
  Mirrors.bind hM
    (Mirrors.ite ((hN.mapIn (w := Prod.map w id) fun _ => rfl).mono h2)
      (mirrors_const 0 fun p : α × Bool => by
        change size (w p.1) + size p.2 ≤ size p.1 + size p.2 + d
        have := hw p.1
        omega) fun _ => rfl)
    hw h1 le_rfl

end ExplicitCost
