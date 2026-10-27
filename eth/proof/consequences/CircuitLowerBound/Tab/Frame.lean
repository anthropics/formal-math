/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Tab.Spec
import Mathlib.Tactic

/-! # For the circuit lower bound for E^NP (Section 7): one step of a multi-stack machine sees and changes only the tops of the stacks

`stepAux_frame`: a statement with at most d stack operations, run on stacks A k ++ R k with A k of
length at least d (or R k empty), does to the A k what it does to them alone, and leaves the R k
alone. `stay_eq`: the step of the machine
(a halted machine stays as it is) written with the case of the configuration. `stay_of_evals`,
`evals_of_stay`: runs of Mathlib's step function and runs of the step function that stays. -/

@[expose] public section

namespace CircuitLowerBound.Tab

open ENP Turing

section generic

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem update_append (A R : ∀ k, List (Γ k)) (k : K) (w : List (Γ k)) :
    Function.update (fun k => A k ++ R k) k (w ++ R k) = fun k' => Function.update A k w k' ++ R k' := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- What lies below the top d symbols is neither seen nor changed. -/
theorem stepAux_frame (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (A R : ∀ k, List (Γ k)), (∀ k, ops q ≤ (A k).length ∨ R k = []) →
    TM2.stepAux q v (fun k => A k ++ R k) =
      ⟨(TM2.stepAux q v A).l, (TM2.stepAux q v A).var, fun k => (TM2.stepAux q v A).stk k ++ R k⟩ := by
  induction q with
  | push k f q ih =>
    intro v A R h
    simp only [TM2.stepAux]
    rw [← List.cons_append, update_append, ih]
    intro k'
    rcases h k' with h | h
    · left
      by_cases e : k' = k
      · subst e; simp [ops] at h ⊢; omega
      · simp [Function.update_of_ne e, ops] at h ⊢; omega
    · exact Or.inr h
  | peek k f q ih =>
    intro v A R h
    have hh : (A k ++ R k).head? = (A k).head? := by
      rcases h k with h | h
      · cases hA : A k with
        | nil => simp [hA, ops] at h
        | cons a l => simp
      · simp [h]
    simp only [TM2.stepAux, hh]
    exact ih _ A R fun k' => (h k').imp (fun h => by simp [ops] at h; omega) id
  | pop k f q ih =>
    intro v A R h
    have hh : (A k ++ R k).head? = (A k).head? ∧ (A k ++ R k).tail = (A k).tail ++ R k := by
      rcases h k with h | h
      · cases hA : A k with
        | nil => simp [hA, ops] at h
        | cons a l => simp
      · simp [h]
    simp only [TM2.stepAux, hh.1, hh.2]
    rw [update_append, ih]
    intro k'
    rcases h k' with h | h
    · left
      by_cases e : k' = k
      · subst e; simp [ops] at h ⊢; omega
      · simp [Function.update_of_ne e, ops] at h ⊢; omega
    · exact Or.inr h
  | load a q ih =>
    intro v A R h
    simp only [TM2.stepAux]
    exact ih _ A R h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v A R h
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ v A R fun k => (h k).imp (fun h => le_trans (le_max_right _ _) h) id
    · exact ih₁ v A R fun k => (h k).imp (fun h => le_trans (le_max_left _ _) h) id
  | goto f => intro v A R _; rfl
  | halt => intro v A R _; rfl

/-- A statement with d stack operations makes a stack longer by at most d. -/
theorem length_stepAux_le (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (A : ∀ k, List (Γ k)) (k : K),
    ((TM2.stepAux q v A).stk k).length ≤ (A k).length + ops q := by
  induction q with
  | push k f q ih =>
    intro v A k'
    simp only [TM2.stepAux]
    refine (ih _ _ k').trans ?_
    by_cases e : k' = k
    · subst e; simp [ops]; omega
    · simp [Function.update_of_ne e, ops]
  | peek k f q ih => intro v A k'; simp only [TM2.stepAux]; exact (ih _ _ k').trans (by simp [ops])
  | pop k f q ih =>
    intro v A k'
    simp only [TM2.stepAux]
    refine (ih _ _ k').trans ?_
    by_cases e : k' = k
    · subst e; simp [ops]; omega
    · simp [Function.update_of_ne e, ops]
  | load a q ih => intro v A k'; simp only [TM2.stepAux]; exact ih _ _ k'
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v A k'
    simp only [TM2.stepAux]
    cases f v
    · exact (ih₂ v A k').trans (by simp [ops])
    · exact (ih₁ v A k').trans (by simp [ops])
  | goto f => intro v A k'; simp [TM2.stepAux, ops]
  | halt => intro v A k'; simp [TM2.stepAux, ops]

end generic

/-! ### Cells -/

theorem length_pref_le {α : Type} : ∀ L : List (Option α), (pref L).length ≤ L.length
  | [] => le_rfl
  | none :: L => by simp [pref]
  | some a :: L => by simpa [pref] using length_pref_le L

/-- The first d cells of a stack give back its top d symbols. -/
theorem pref_ofFn {α : Type} (d : ℕ) : ∀ S : List α, pref (List.ofFn fun j : Fin d => S[j.val]?) = S.take d := by
  induction d with
  | zero => intro S; simp [pref]
  | succ d ih =>
    intro S
    rw [List.ofFn_succ]
    cases S with
    | nil => simp [pref]
    | cons a S => simpa [pref] using ih S

/-- In a list of cells in which a blank is followed by blanks only, the symbols up to the first
blank have the cells as their entries. -/
theorem getElem?_pref {α : Type} : ∀ L : List (Option α), (∀ i, L[i]? = some none → ∀ x, L[i + 1]? = some x → x = none) →
    ∀ q, q < L.length → (pref L)[q]? = (L[q]?).getD none
  | [], _, q, hq => by simp at hq
  | none :: L, h, q, hq => by
    have : ∀ q, q < (none :: L).length → (none :: L)[q]? = some none := by
      intro q
      induction q with
      | zero => intro _; rfl
      | succ q ih =>
        intro hq
        obtain ⟨x, hx⟩ : ∃ x, (none :: L)[q + 1]? = some x := ⟨_, List.getElem?_eq_getElem hq⟩
        rw [hx, h q (ih (by omega)) x hx]
    rw [this q hq]
    simp [pref]
  | some a :: L, h, 0, _ => by simp [pref]
  | some a :: L, h, q + 1, hq => by
    have := getElem?_pref L (fun i hi x hx => h (i + 1) (by simpa using hi) x (by simpa using hx)) q (by simpa using hq)
    simpa [pref] using this

/-! ### The step that stays -/

variable (N : TM2ComputableAux Bool Bool)

/-- The case of a configuration. -/
def caseOf (c : N.tm.Cfg) : Case N := (c.l, c.var, fun k j => (c.stk k)[j.val]?)

/-- One step; a halted machine stays as it is. -/
def stay (c : N.tm.Cfg) : N.tm.Cfg := (N.tm.step c).getD c

theorem ops_le_dep (l : N.tm.Λ) : ops (N.tm.m l) ≤ dep N :=
  le_trans (Finset.le_sup (f := fun l : N.tm.Λ => ops (N.tm.m l)) (Finset.mem_univ l)) (le_max_right _ _)

theorem one_le_dep : 1 ≤ dep N := le_max_left _ _

/-- The step, written with the case of the configuration. -/
theorem stay_eq (c : N.tm.Cfg) : stay N c =
    ⟨(nxt N (caseOf N c)).l, (nxt N (caseOf N c)).var, fun k => (nxt N (caseOf N c)).stk k ++ (c.stk k).drop (dep N)⟩ := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    simp only [stay, FinTM2.step, TM2.step, nxt, caseOf, pref_ofFn, List.take_append_drop]
    rfl
  | some l =>
    have := stepAux_frame (N.tm.m l) v (fun k => (S k).take (dep N)) (fun k => (S k).drop (dep N)) fun k => by
      by_cases h : dep N ≤ (S k).length
      · left; rw [List.length_take, min_eq_left h]; exact ops_le_dep N l
      · right; exact List.drop_eq_nil_of_le (by omega)
    simp only [List.take_append_drop] at this
    simp only [stay, FinTM2.step, TM2.step, nxt, caseOf, pref_ofFn, this]
    rfl

/-- The new top of a stack has at most 2d symbols. -/
theorem length_nxt_le (γ : Case N) (k : N.tm.K) : ((nxt N γ).stk k).length ≤ 2 * dep N := by
  obtain ⟨l, v, w⟩ := γ
  have h1 : (pref (List.ofFn (w k))).length ≤ dep N := (length_pref_le _).trans (by simp)
  cases l with
  | none => simp only [nxt]; omega
  | some l =>
    simp only [nxt]
    have := length_stepAux_le (N.tm.m l) v (fun k => pref (List.ofFn (w k))) k
    have := ops_le_dep N l
    omega

theorem stay_of_halted {c : N.tm.Cfg} (h : c.l = none) : stay N c = c := by
  obtain ⟨l, v, S⟩ := c
  subst h
  rfl

theorem iterate_stay_of_halted {c : N.tm.Cfg} (h : c.l = none) (n : ℕ) : (stay N)^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, stay_of_halted N h, ih]

/-- A run of n steps of Mathlib's step function is a run of the step that stays. -/
theorem stay_of_evals {c₀ c : N.tm.Cfg} : ∀ n : ℕ, (flip bind N.tm.step)^[n] (some c₀) = some c → (stay N)^[n] c₀ = c := by
  intro n
  induction n generalizing c with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h ⊢
    cases h' : (flip bind N.tm.step)^[n] (some c₀) with
    | none =>
      rw [h'] at h
      exact (Option.some_ne_none c (h.symm.trans rfl)).elim
    | some c' =>
      rw [h'] at h
      rw [ih h']
      have : N.tm.step c' = some c := h
      rw [stay, this]; rfl

/-- What the step that stays reaches in T steps, Mathlib's step function reaches in at most T steps. -/
theorem evals_of_stay {h : N.tm.Cfg} : ∀ (T : ℕ) (c₀ : N.tm.Cfg), (stay N)^[T] c₀ = h →
    ∃ n ≤ T, (flip bind N.tm.step)^[n] (some c₀) = some h := by
  intro T
  induction T with
  | zero => intro c₀ e; exact ⟨0, le_rfl, by simpa using e⟩
  | succ T ih =>
    intro c₀ e
    by_cases h0 : c₀.l = none
    · rw [iterate_stay_of_halted N h0] at e
      exact ⟨0, Nat.zero_le _, by simpa using e⟩
    · rw [Function.iterate_succ_apply] at e
      obtain ⟨n, hn, hr⟩ := ih _ e
      refine ⟨n + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      have : flip bind N.tm.step (some c₀) = some (stay N c₀) := by
        obtain ⟨l, v, S⟩ := c₀
        cases l with
        | none => exact absurd rfl h0
        | some l => rfl
      rw [this, hr]

end CircuitLowerBound.Tab
