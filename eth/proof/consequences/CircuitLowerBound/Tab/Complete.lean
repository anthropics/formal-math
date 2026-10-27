/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Tab.Sound
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): a run of the machine satisfies the conditions

`spec_of_acc`: if the machine accepts 1^P 0 y within 2^b steps, the rows of its run satisfy the
conditions `Spec`. With `acc_of_spec` this gives `stSpec`. -/

public section

namespace CircuitLowerBound.Tab

open ENP Turing

variable (N : TM2ComputableAux Bool Bool) [Finite (Case N)]

open Classical in
/-- The truth values of all statements about the rows c 0, c 1, … -/
noncomputable def rows (c : ℕ → N.tm.Cfg) (P : ℕ) : Atom N → ℕ → ℕ → Bool
  | .lab x, t, _ => decide (x = (c t).l)
  | .var x, t, _ => decide (x = (c t).var)
  | .len k n, t, _ => decide ((n : ℕ) = ((nxt N (caseOf N (c t))).stk k).length)
  | .cell k x, t, q => decide (x = ((c t).stk k)[q]?)
  | .cs γ, t, _ => decide (γ = caseOf N (c t))
  | .pre i, t, _ => decide (((ec N (caseOf N (c t)) : Fin (nc N)) : ℕ) < i)
  | .u, _, q => decide (q ≤ P)

variable {N}

omit [Finite (Case N)] in
theorem getElem?_input (P : ℕ) (y : List Bool) {q : ℕ} (hq : q < P) :
    ((unary P ++ y).map N.inputAlphabet.invFun)[q]? = some (N.inputAlphabet.symm true) := by
  simp [unary, List.getElem?_append_left, hq]

omit [Finite (Case N)] in
theorem getElem?_input_self (P : ℕ) (y : List Bool) :
    ((unary P ++ y).map N.inputAlphabet.invFun)[P]? = some (N.inputAlphabet.symm false) := by
  simp [unary]

/-- If the machine accepts, the conditions can be satisfied. -/
theorem spec_of_acc {b P : ℕ} (Q : ℕ) (h : Acc N P (2 ^ b)) : ∃ α, Spec N α b Q P := by
  classical
  obtain ⟨y, ⟨hrun⟩⟩ := h
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = (unary P ++ y).map N.inputAlphabet.invFun := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → N.tm.Cfg, ∀ t, c t = (stay N)^[t] (initList N.tm S₀) := ⟨_, fun _ => rfl⟩
  have hc0 : c 0 = initList N.tm S₀ := by rw [hcdef]; rfl
  have hcs : ∀ t, c (t + 1) = ⟨(nxt N (caseOf N (c t))).l, (nxt N (caseOf N (c t))).var,
      fun k => (nxt N (caseOf N (c t))).stk k ++ ((c t).stk k).drop (dep N)⟩ := by
    intro t
    rw [hcdef, Function.iterate_succ_apply', ← hcdef, stay_eq]
  have hcT : c (2 ^ b) = haltList N.tm [N.outputAlphabet.invFun true] := by
    have h1 := stay_of_evals N hrun.steps (c₀ := initList N.tm S₀) (c := haltList N.tm [N.outputAlphabet.invFun true]) (by rw [hS₀]; exact hrun.evals_in_steps)
    rw [hcdef, show 2 ^ b = (2 ^ b - hrun.steps) + hrun.steps from (Nat.sub_add_cancel hrun.steps_le_m).symm, Function.iterate_add_apply, h1,
      iterate_stay_of_halted N rfl]
  refine ⟨rows N c P, ?_⟩
  constructor
  case preTop => intro t _; simp [rows]
  case preBot => intro t _; simp [rows]
  case preStep =>
    intro t _ i
    simp only [rows, decide_eq_true_eq, decide_eq_false_iff_not, Fin.val_succ, Fin.val_castSucc]
    by_cases h1 : ((ec N (caseOf N (c t)) : Fin (nc N)) : ℕ) < i
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : ((ec N (caseOf N (c t)) : Fin (nc N)) : ℕ) = i
      · exact Or.inr (Or.inr (by rw [← Fin.ext h2, Equiv.symm_apply_apply]))
      · exact Or.inl (by omega)
  case csLab => intro t _ γ hγ; simp only [rows, decide_eq_true_eq] at hγ ⊢; rw [hγ]; rfl
  case csVar => intro t _ γ hγ; simp only [rows, decide_eq_true_eq] at hγ ⊢; rw [hγ]; rfl
  case csCell => intro t _ γ k j hγ; simp only [rows, decide_eq_true_eq] at hγ ⊢; rw [hγ]; rfl
  case nxLab => intro t _ γ x hγ; simp only [rows, decide_eq_true_eq] at hγ ⊢; rw [hγ, hcs]
  case nxVar => intro t _ γ x hγ; simp only [rows, decide_eq_true_eq] at hγ ⊢; rw [hγ, hcs]
  case nxLen => intro t _ γ k n hγ; simp only [rows, decide_eq_true_eq] at hγ ⊢; rw [hγ]
  case nxCell =>
    intro t _ γ k x j hj hγ
    simp only [rows, decide_eq_true_eq] at hγ ⊢
    subst hγ
    rw [hcs]
    simp only [List.getElem?_append_left hj]
  case copy =>
    intro t _ q _ k n x hn
    simp only [rows, decide_eq_true_eq] at hn ⊢
    rw [hcs]
    simp only
    rw [List.getElem?_append_right (by omega), hn, Nat.add_sub_cancel, List.getElem?_drop, Nat.add_comm]
  case iLab => intro x; simp only [rows, decide_eq_true_eq, hc0]; rfl
  case iVar => intro x; simp only [rows, decide_eq_true_eq, hc0]; rfl
  case iCell => intro q _ k hk x; simp only [rows, decide_eq_true_eq, hc0, initList_stk_of_ne N _ hk]; simp
  case iSome =>
    intro q _
    simp only [rows, decide_eq_true_eq, hc0, initList_stk_self]
    cases hz : S₀[q]? with
    | none => exact Or.inl rfl
    | some z =>
      have : z = N.inputAlphabet.symm (N.inputAlphabet z) := (Equiv.symm_apply_apply _ _).symm
      cases hb : N.inputAlphabet z with
      | false => rw [hb] at this; exact Or.inr (Or.inl (by rw [this]))
      | true => rw [hb] at this; exact Or.inr (Or.inr (by rw [this]))
  case iMost =>
    intro q _ x x' hne
    simp only [rows, decide_eq_false_iff_not]
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hne (hc.1.trans hc.2.symm)
  case iBlank =>
    intro q _ hq
    simp only [rows, decide_eq_true_eq, hc0, initList_stk_self] at hq ⊢
    have := List.getElem?_eq_none_iff.1 hq.symm
    exact (List.getElem?_eq_none (by omega)).symm
  case uStep => intro q _ hq; simp only [rows, decide_eq_true_eq] at hq ⊢; omega
  case uP => simp [rows]
  case uP1 => simp [rows]
  case uOne =>
    intro q _ hq
    simp only [rows, decide_eq_true_eq, hc0, initList_stk_self] at hq ⊢
    rw [hS₀, getElem?_input P y (by omega)]
  case cellP => simp only [rows, decide_eq_true_eq, hc0, initList_stk_self]; rw [hS₀, getElem?_input_self]
  case fLab => simp only [rows, decide_eq_true_eq, hcT]; rfl
  case fVar => simp only [rows, decide_eq_true_eq, hcT]; rfl
  case fOut0 => simp only [rows, decide_eq_true_eq, hcT, haltList_stk_self]; rfl
  case fOut1 => simp only [rows, decide_eq_true_eq, hcT, haltList_stk_self]; rfl
  case fOther => intro k hk; simp only [rows, decide_eq_true_eq, hcT, haltList_stk_of_ne N _ hk]; rfl

end CircuitLowerBound.Tab

namespace CircuitLowerBound

open Tab

/-- The conditions hold for some truth values if and only if the machine accepts. -/
theorem stSpec : StSpec := fun _ _ _ _ _ hP => ⟨fun ⟨_, h⟩ => acc_of_spec hP h, fun h => spec_of_acc _ h⟩

end CircuitLowerBound
