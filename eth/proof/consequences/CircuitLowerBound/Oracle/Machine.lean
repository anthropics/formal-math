/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
public import ToTuring.TM.Run
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): from a machine that is started again after every answer to an oracle machine: the machine

Given a machine M that is started on (x, answers so far) and returns the result or the next query,
the oracle machine `otm M` has the stacks of M and three stacks of bits: `io` (its input and output;
it keeps x, first bit on
top, until the end), `ans` (the answers, the last one on top) and `sp` (a spare stack, empty between
the loops). Its query stack is the output stack of M. Its state is the state of M and a register for
one popped bit, empty
between the steps. A round:

* `cpA`: the answers go from `ans` to `sp`, and a copy of each on the input stack of M; `mvA`: they
  go back from `sp` to `ans`; `sep`: a 0 on the input stack of M;
* `mvX`: x goes from `io` to `sp`; `cpX`: it goes back, and for each bit b the bits b and 1 are
  pushed on the input stack of M, which now holds the input of the round;
* the program of M, in which «halt» is a jump to `after`;
* `after`: the first bit of the output of M is popped. If it is 1, what is left on the output stack
  of M is the query: `ask`; at `yes` and `no` the answer is pushed on `ans` and the next round
  begins.
  If it is 0: `drX` and `drA` empty `io` and `ans`, and `fin` moves the result from the output stack
  of M to `io` and halts.

This file has the definitions, one step of the machine at a label other than `ask` and at `ask`, and
the runs of M inside the machine. -/

@[expose] public section

namespace CircuitLowerBound.Oracle

open ENP Turing Groundwork.TM

/-- The three new stacks. -/
inductive NS | io | ans | sp
  deriving DecidableEq

instance : Fintype NS := ⟨{.io, .ans, .sp}, fun x => by cases x <;> simp⟩

/-- The new labels. -/
inductive Ctl | cpA | mvA | sep | mvX | cpX | after | ask | yes | no | drX | drA | fin
  deriving DecidableEq

instance : Fintype Ctl := ⟨{.cpA, .mvA, .sep, .mvX, .cpX, .after, .ask, .yes, .no, .drX, .drA, .fin}, fun x => by cases x <;> simp⟩

variable (M : TM2ComputableAux Bool Bool)

/-- The alphabets. -/
abbrev Γ' : M.tm.K ⊕ NS → Type
  | .inl k => M.tm.Γ k
  | .inr _ => Bool

/-- The labels. -/
abbrev Λ' : Type := M.tm.Λ ⊕ Ctl

/-- The states: the state of M and the register. -/
abbrev σ' : Type := M.tm.σ × Option Bool

/-- The statements. -/
abbrev St : Type := TM2.Stmt (Γ' M) (Λ' M) (σ' M)

/-- The configurations. -/
abbrev Cf : Type := TM2.Cfg (Γ' M) (Λ' M) (σ' M)

/-- A statement of M in the new machine; «halt» is a jump to `after`. -/
def lift : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → St M
  | .push k f q => .push (.inl k) (fun v => f v.1) (lift q)
  | .peek k f q => .peek (.inl k) (fun v o => (f v.1 o, v.2)) (lift q)
  | .pop k f q => .pop (.inl k) (fun v o => (f v.1 o, v.2)) (lift q)
  | .load f q => .load (fun v => (f v.1, v.2)) (lift q)
  | .branch p q₁ q₂ => .branch (fun v => p v.1) (lift q₁) (lift q₂)
  | .goto l => .goto fun v => .inl (l v.1)
  | .halt => .goto fun _ => .inr .after

/-- A loop that moves the stack s to the stack d; it stands at the label me and leaves to nx. -/
def mvS (s d : NS) (me nx : Λ' M) : St M :=
  .pop (.inr s) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (.inr d) (fun v => v.2.getD false) <| .load (fun v => (v.1, none)) <| .goto fun _ => me)
      (.goto fun _ => nx)

/-- A loop that empties the stack s. -/
def drS (s : NS) (me nx : Λ' M) : St M :=
  .pop (.inr s) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome) (.load (fun v => (v.1, none)) <| .goto fun _ => me) (.goto fun _ => nx)

/-- A loop that moves the stack s to the stack d and pushes every bit on the input stack of M,
followed by a 1 if `mark`. -/
def cpS (s d : NS) (mark : Bool) (me nx : Λ' M) : St M :=
  .pop (.inr s) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (.inr d) (fun v => v.2.getD false) <| .push (.inl M.tm.k₀) (fun v => M.inputAlphabet.invFun (v.2.getD false)) <|
        .branch (fun _ => mark)
          (.push (.inl M.tm.k₀) (fun _ => M.inputAlphabet.invFun true) <| .load (fun v => (v.1, none)) <| .goto fun _ => me)
          (.load (fun v => (v.1, none)) <| .goto fun _ => me))
      (.goto fun _ => nx)

/-- The program. -/
def prog : Λ' M → St M
  | .inl l => lift M (M.tm.m l)
  | .inr .cpA => cpS M .ans .sp false (.inr .cpA) (.inr .mvA)
  | .inr .mvA => mvS M .sp .ans (.inr .mvA) (.inr .sep)
  | .inr .sep => .push (.inl M.tm.k₀) (fun _ => M.inputAlphabet.invFun false) <| .goto fun _ => .inr .mvX
  | .inr .mvX => mvS M .io .sp (.inr .mvX) (.inr .cpX)
  | .inr .cpX => cpS M .sp .io true (.inr .cpX) (.inl M.tm.main)
  | .inr .after => .pop (.inl M.tm.k₁) (fun v o => (v.1, o.map M.outputAlphabet)) <|
      .branch (fun v => v.2 == some true) (.load (fun v => (v.1, none)) <| .goto fun _ => .inr .ask)
        (.load (fun v => (v.1, none)) <| .goto fun _ => .inr .drX)
  | .inr .ask => .halt
  | .inr .yes => .push (.inr .ans) (fun _ => true) <| .goto fun _ => .inr .cpA
  | .inr .no => .push (.inr .ans) (fun _ => false) <| .goto fun _ => .inr .cpA
  | .inr .drX => drS M .io (.inr .drX) (.inr .drA)
  | .inr .drA => drS M .ans (.inr .drA) (.inr .fin)
  | .inr .fin => .pop (.inl M.tm.k₁) (fun v o => (v.1, o.map M.outputAlphabet)) <|
      .push (.inr .io) (fun v => v.2.getD false) <| .load (fun v => (v.1, none)) .halt

/-- The machine. -/
def tm' : FinTM2 where
  K := M.tm.K ⊕ NS
  kFin := by haveI := M.tm.kFin; infer_instance
  k₀ := .inr .io
  k₁ := .inr .io
  Γ := Γ' M
  Λ := Λ' M
  main := .inr .cpA
  ΛFin := by haveI := M.tm.ΛFin; infer_instance
  σ := σ' M
  initialState := (M.tm.initialState, none)
  σFin := by haveI := M.tm.σFin; infer_instance
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog M

/-- The oracle machine: the query stack is the output stack of M. -/
def otm : OTM where
  tm := tm' M
  inp := Equiv.refl Bool
  out := Equiv.refl Bool
  q := .inl M.tm.k₁
  qry := M.outputAlphabet
  ask := .inr .ask
  yes := .inr .yes
  no := .inr .no

/-- One step of the oracle machine with the oracle O. -/
noncomputable def stp (O : Lang) : Cf M → Option (Cf M) := (otm M).step O

/-! ### The stacks -/

/-- The stacks of M and the new stacks. -/
def stk (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) : ∀ k, List (Γ' M k)
  | .inl k => T k
  | .inr j => n j

variable {M}

@[simp] theorem stk_inl (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (k : M.tm.K) : stk M T n (.inl k) = T k := rfl

@[simp] theorem stk_inr (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (j : NS) : stk M T n (.inr j) = n j := rfl

@[simp] theorem update_inl (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (k : M.tm.K) (w : List (M.tm.Γ k)) :
    Function.update (stk M T n) (.inl k) w = stk M (Function.update T k w) n := by
  funext k'
  rcases k' with k' | j
  · by_cases h : k' = k
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]; simp [Function.update_of_ne h]
  · rfl

@[simp] theorem update_inr (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (j : NS) (w : List Bool) :
    Function.update (stk M T n) (.inr j) w = stk M T (Function.update n j w) := by
  funext k'
  rcases k' with k | j'
  · rfl
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]; simp [Function.update_of_ne h]

/-- The contents of the three new stacks. -/
def ns (a b c : List Bool) : NS → List Bool
  | .io => a
  | .ans => b
  | .sp => c

section
variable (a b c w : List Bool)
@[simp] theorem ns_io : ns a b c .io = a := rfl
@[simp] theorem ns_ans : ns a b c .ans = b := rfl
@[simp] theorem ns_sp : ns a b c .sp = c := rfl
@[simp] theorem upd_io : Function.update (ns a b c) .io w = ns w b c := by funext k; cases k <;> simp [Function.update, ns]
@[simp] theorem upd_ans : Function.update (ns a b c) .ans w = ns a w c := by funext k; cases k <;> simp [Function.update, ns]
@[simp] theorem upd_sp : Function.update (ns a b c) .sp w = ns a b w := by funext k; cases k <;> simp [Function.update, ns]
end

/-- All stacks of M are empty but one. -/
def one (k : M.tm.K) (w : List (M.tm.Γ k)) : ∀ k', List (M.tm.Γ k') := Function.update (fun _ => []) k w

@[simp] theorem one_self (k : M.tm.K) (w : List (M.tm.Γ k)) : one k w k = w := by simp [one]

@[simp] theorem update_one (k : M.tm.K) (w w' : List (M.tm.Γ k)) : Function.update (one k w) k w' = one k w' := by simp [one]

theorem one_nil (k k' : M.tm.K) : (one k [] : ∀ k', List (M.tm.Γ k')) = one k' [] := by
  funext j
  simp only [one]
  rw [Function.update_eq_self_iff.2 rfl, Function.update_eq_self_iff.2 rfl]

theorem initList_stk (s : List (M.tm.Γ M.tm.k₀)) : (initList M.tm s).stk = one M.tm.k₀ s := by
  funext k
  by_cases h : k = M.tm.k₀
  · subst h; simp [initList]
  · simp [initList, one, h]

theorem haltList_stk (s : List (M.tm.Γ M.tm.k₁)) : (haltList M.tm s).stk = one M.tm.k₁ s := by
  funext k
  by_cases h : k = M.tm.k₁
  · subst h; simp [haltList]
  · simp [haltList, one, h]

/-! ### Single steps -/

/-- A step at a label other than `ask` runs the statement at that label. -/
theorem stp_of_ne (O : Lang) {l : Λ' M} (hl : l ≠ .inr .ask) (v : σ' M) (S : ∀ k, List (Γ' M k)) :
    stp M O ⟨some l, v, S⟩ = some (TM2.stepAux (prog M l) v S) := by
  have h : (some l : Option (Λ' M)) ≠ some (.inr .ask) := fun h => hl (Option.some.inj h)
  exact if_neg h

open Classical in
/-- A step at `ask`. -/
theorem stp_ask (O : Lang) (v : σ' M) (S : ∀ k, List (Γ' M k)) :
    stp M O ⟨some (.inr .ask), v, S⟩ =
      some ⟨some (if O ((S (.inl M.tm.k₁)).map M.outputAlphabet) then .inr .yes else .inr .no), v, Function.update S (.inl M.tm.k₁) []⟩ :=
  if_pos rfl

/-! ### The runs of M -/

/-- A configuration of M in the new machine, with the register empty and the new stacks n. -/
def liftCfg (n : NS → List Bool) (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) : Cf M :=
  ⟨c.l.elim (some (.inr .after)) fun l => some (.inl l), (c.var, none), stk M c.stk n⟩

theorem stepAux_lift (n : NS → List Bool) (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) (v : M.tm.σ) (T : ∀ k, List (M.tm.Γ k)) :
    TM2.stepAux (lift M q) (v, none) (stk M T n) = liftCfg n (TM2.stepAux q v T) := by
  induction q generalizing v T with
  | push k f q ih => simp only [lift, TM2.stepAux, update_inl, stk_inl]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [lift, TM2.stepAux, update_inl, stk_inl]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ => simp only [lift, TM2.stepAux, ih₁, ih₂]; cases p v <;> rfl
  | goto l => rfl
  | halt => rfl

/-- A run of M is a run of the new machine of the same length; where M halts, the new machine is at
`after`. -/
theorem run_lift (O : Lang) (n : NS → List Bool) :
    ∀ {t : ℕ} {a b : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ}, Run (TM2.step M.tm.m) a t b → Run (stp M O) (liftCfg n a) t (liftCfg n b)
  | 0, _, _, h => by cases h; exact rfl
  | t + 1, ⟨none, v, S⟩, b, ⟨c, hc, _⟩ => by simp [TM2.step] at hc
  | t + 1, ⟨some l, v, S⟩, b, ⟨c, hc, h⟩ => by
    refine ⟨liftCfg n c, ?_, run_lift O n h⟩
    simp only [TM2.step, Option.some.injEq] at hc
    subst hc
    exact (stp_of_ne O (by simp) _ _).trans (congrArg some (stepAux_lift n _ _ _))

/-- Mathlib's form of a run, read back. -/
theorem run_of_iterate {C : Type} {f : C → Option C} : ∀ {t : ℕ} {a b : C}, (flip bind f)^[t] (some a) = some b → Run f a t b
  | 0, _, _, h => Option.some.inj h
  | t + 1, a, b, h => by
    rw [Function.iterate_succ_apply] at h
    have hn : ∀ t : ℕ, (flip bind f)^[t] none = none := fun t => by
      induction t with
      | zero => rfl
      | succ t ih => rw [Function.iterate_succ_apply]; exact ih
    cases hfa : f a with
    | none =>
      have : flip bind f (some a) = none := hfa
      rw [this, hn] at h
      exact absurd h (by simp)
    | some c =>
      have : flip bind f (some a) = some c := hfa
      rw [this] at h
      exact ⟨c, hfa, run_of_iterate h⟩

end CircuitLowerBound.Oracle
