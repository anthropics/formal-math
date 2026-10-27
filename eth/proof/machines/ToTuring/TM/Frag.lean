/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Run

/-! Fragments: programs of multi-stack machines over fixed stacks, alphabets and local state; they
differ in their labels only.
So gluing is a matter of labels: one after the other, a choice between two, a loop. -/

@[expose] public section

namespace Groundwork.TM

open Turing

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-- A fragment: a finite set of labels, a first label, a program. -/
structure Frag (Γ : K → Type) (σ : Type) where
  /-- the labels -/
  Λ : Type
  [fin : Fintype Λ]
  /-- the first label -/
  entry : Λ
  /-- the program -/
  m : Λ → TM2.Stmt Γ Λ σ

attribute [instance] Frag.fin

/-- From its first label, with local state v and stacks S, the fragment halts after exactly n steps
with local state v and
stacks S'. -/
def Frag.Runs (P : Frag Γ σ) (v : σ) (S : ∀ k, List (Γ k)) (n : ℕ) (S' : ∀ k, List (Γ k)) : Prop :=
  Run (TM2.step P.m) ⟨some P.entry, v, S⟩ n ⟨none, v, S'⟩

/-- P, then Q. -/
def Frag.seq (P Q : Frag Γ σ) : Frag Γ σ where
  Λ := P.Λ ⊕ Q.Λ
  entry := .inl P.entry
  m
    | .inl l => place Sum.inl (some (.inr Q.entry)) (P.m l)
    | .inr l => place Sum.inr none (Q.m l)

/-- A run of P followed by a run of Q is a run of `P.seq Q`; the numbers of steps add up. -/
theorem Frag.seq_runs {P Q : Frag Γ σ} {v : σ} {S S' S'' : ∀ k, List (Γ k)} {n n' : ℕ} (hP : P.Runs v S n S')
    (hQ : Q.Runs v S' n' S'') : (P.seq Q).Runs v S (n + n') S'' :=
  (run_place (M' := (P.seq Q).m) Sum.inl (some (.inr Q.entry)) (fun _ => rfl) hP).trans
    (run_place (M' := (P.seq Q).m) Sum.inr none (fun _ => rfl) hQ)

/-- One step of a larger machine at a label that holds a placed statement. -/
theorem run_head {Λ Λ' : Type} {M' : Λ' → TM2.Stmt Γ Λ' σ} (ι : Λ → Λ') (e : Option Λ') {l' : Λ'} {q : TM2.Stmt Γ Λ σ}
    (hM : M' l' = place ι e q) {v : σ} {S : ∀ k, List (Γ k)} {c : TM2.Cfg Γ Λ σ} (h : TM2.stepAux q v S = c) :
    Run (TM2.step M') ⟨some l', v, S⟩ 1 (placeCfg ι e c) :=
  Run.one (by simp only [TM2.step, hM, stepAux_place, h])

/-- One statement without jumps. -/
def Frag.ofStmt (q : TM2.Stmt Γ Empty σ) : Frag Γ σ where
  Λ := Unit
  entry := ()
  m _ := place Empty.elim none q

/-- If the statement halts with the local state unchanged, the fragment runs in one step. -/
theorem Frag.ofStmt_runs {q : TM2.Stmt Γ Empty σ} {v : σ} {S S' : ∀ k, List (Γ k)}
    (h : TM2.stepAux q v S = ⟨none, v, S'⟩) : (Frag.ofStmt q).Runs v S 1 S' :=
  run_head (M' := (Frag.ofStmt q).m) (l' := ()) Empty.elim none rfl h

/-- A head statement that ends in `goto true`, `goto false` or `halt`; then P, or Q, or nothing. -/
def Frag.branch (q : TM2.Stmt Γ Bool σ) (P Q : Frag Γ σ) : Frag Γ σ where
  Λ := Unit ⊕ (P.Λ ⊕ Q.Λ)
  entry := .inl ()
  m
    | .inl _ => place (fun b : Bool => if b then .inr (.inl P.entry) else .inr (.inr Q.entry)) none q
    | .inr (.inl l) => place (fun l => .inr (.inl l)) none (P.m l)
    | .inr (.inr l) => place (fun l => .inr (.inr l)) none (Q.m l)

/-- If the head ends in `goto true`, the branch takes one step and then runs as P. -/
theorem Frag.branch_runs_true {q : TM2.Stmt Γ Bool σ} {P Q : Frag Γ σ} {v : σ} {S S₁ S' : ∀ k, List (Γ k)} {n : ℕ}
    (h : TM2.stepAux q v S = ⟨some true, v, S₁⟩) (hP : P.Runs v S₁ n S') : (Frag.branch q P Q).Runs v S (n + 1) S' := by
  rw [Nat.add_comm n 1]
  exact (run_head (M' := (Frag.branch q P Q).m) (l' := Sum.inl ()) _ none rfl h).trans
    (run_place (M' := (Frag.branch q P Q).m) (fun l => Sum.inr (Sum.inl l)) none (fun _ => rfl) hP)

/-- If the head ends in `goto false`, the branch takes one step and then runs as Q. -/
theorem Frag.branch_runs_false {q : TM2.Stmt Γ Bool σ} {P Q : Frag Γ σ} {v : σ} {S S₁ S' : ∀ k, List (Γ k)} {n : ℕ}
    (h : TM2.stepAux q v S = ⟨some false, v, S₁⟩) (hQ : Q.Runs v S₁ n S') : (Frag.branch q P Q).Runs v S (n + 1) S' := by
  rw [Nat.add_comm n 1]
  exact (run_head (M' := (Frag.branch q P Q).m) (l' := Sum.inl ()) _ none rfl h).trans
    (run_place (M' := (Frag.branch q P Q).m) (fun l => Sum.inr (Sum.inr l)) none (fun _ => rfl) hQ)

/-- A loop: the head statement ends in `halt` (leave the loop) or in `goto ()` (the body, then the
head again). -/
def Frag.loop (q : TM2.Stmt Γ Unit σ) (B : Frag Γ σ) : Frag Γ σ where
  Λ := Unit ⊕ B.Λ
  entry := .inl ()
  m
    | .inl _ => place (fun _ => .inr B.entry) none q
    | .inr l => place Sum.inr (some (.inl ())) (B.m l)

/-- If the head halts, the loop ends after one step. -/
theorem Frag.loop_runs_exit {q : TM2.Stmt Γ Unit σ} {B : Frag Γ σ} {v : σ} {S S' : ∀ k, List (Γ k)}
    (h : TM2.stepAux q v S = ⟨none, v, S'⟩) : (Frag.loop q B).Runs v S 1 S' :=
  run_head (M' := (Frag.loop q B).m) (l' := Sum.inl ()) _ none rfl h

/-- If the head ends in `goto ()`, the loop takes one step, runs the body, then runs as the loop
again. -/
theorem Frag.loop_runs_iter {q : TM2.Stmt Γ Unit σ} {B : Frag Γ σ} {v : σ} {S S₁ S₂ S' : ∀ k, List (Γ k)} {n m : ℕ}
    (h : TM2.stepAux q v S = ⟨some (), v, S₁⟩) (hB : B.Runs v S₁ n S₂) (hL : (Frag.loop q B).Runs v S₂ m S') :
    (Frag.loop q B).Runs v S (1 + n + m) S' :=
  ((run_head (M' := (Frag.loop q B).m) (l' := Sum.inl ()) _ none rfl h).trans
    (run_place (M' := (Frag.loop q B).m) Sum.inr (some (Sum.inl ())) (fun _ => rfl) hB)).trans hL

/-! ### Runs with an upper bound on the number of steps. The local state is an optional symbol, `none` before and after. -/

section within

variable {τ : Type}

/-- P leads from S to S' within t steps (local state none before and after). -/
def Frag.Within (P : Frag Γ (Option τ)) (S : ∀ k, List (Γ k)) (t : ℕ) (S' : ∀ k, List (Γ k)) : Prop :=
  ∃ n ≤ t, P.Runs none S n S'

theorem Frag.Within.mono {P : Frag Γ (Option τ)} {S S' : ∀ k, List (Γ k)} {t t' : ℕ} (h : P.Within S t S') (ht : t ≤ t') :
    P.Within S t' S' := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn.trans ht, hr⟩

theorem Frag.Within.seq {P Q : Frag Γ (Option τ)} {S S' S'' : ∀ k, List (Γ k)} {t t' : ℕ} (h : P.Within S t S')
    (h' : Q.Within S' t' S'') : (P.seq Q).Within S (t + t') S'' := by
  obtain ⟨n, hn, hr⟩ := h
  obtain ⟨n', hn', hr'⟩ := h'
  exact ⟨n + n', Nat.add_le_add hn hn', Frag.seq_runs hr hr'⟩

theorem Frag.Within.of_runs {P : Frag Γ (Option τ)} {S S' : ∀ k, List (Γ k)} {n : ℕ} (h : P.Runs none S n S') :
    P.Within S n S' := ⟨n, le_rfl, h⟩

end within

end Groundwork.TM
