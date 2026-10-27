/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Tab.Frame
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): rows that satisfy the conditions are a run of the machine

`acc_of_spec`: if some truth values satisfy the conditions `Spec`, then the machine accepts 1^P 0 y
for some y within 2^b steps. The first row is the start on such a word (`exists_init`); if row t is
a configuration at the positions below V, then
row t + 1 is the next configuration at the positions below V − d (`Enc.step`); the last row is the
halted configuration with the output 1 (`eq_haltList`). -/

public section

namespace CircuitLowerBound.Tab

open ENP Turing

variable (N : TM2ComputableAux Bool Bool)

/-- Row t is the configuration c, as far as the positions below V go. -/
structure Enc (α : Atom N → ℕ → ℕ → Bool) (t V : ℕ) (c : N.tm.Cfg) : Prop where
  lab : ∀ x, α (.lab x) t 0 = true ↔ x = c.l
  var : ∀ x, α (.var x) t 0 = true ↔ x = c.var
  cell : ∀ k x q, q < V → (α (.cell k x) t q = true ↔ x = (c.stk k)[q]?)

theorem initList_stk_self (s : List (N.tm.Γ N.tm.k₀)) : (initList N.tm s).stk N.tm.k₀ = s := by simp [initList]

theorem initList_stk_of_ne (s : List (N.tm.Γ N.tm.k₀)) {k : N.tm.K} (h : k ≠ N.tm.k₀) : (initList N.tm s).stk k = [] := by simp [initList, h]

theorem haltList_stk_self (s : List (N.tm.Γ N.tm.k₁)) : (haltList N.tm s).stk N.tm.k₁ = s := by simp [haltList]

theorem haltList_stk_of_ne (s : List (N.tm.Γ N.tm.k₁)) {k : N.tm.K} (h : k ≠ N.tm.k₁) : (haltList N.tm s).stk k = [] := by simp [haltList, h]

variable {N} [Finite (Case N)] {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}

/-- At every time before the last some case holds. -/
theorem exists_case (h : Spec N α b Q P) {t : ℕ} (ht : t < 2 ^ b) : ∃ γ, α (.cs γ) t 0 = true := by
  have key : ∀ (i : ℕ) (hi : i < nc N + 1), α (.pre ⟨i, hi⟩) t 0 = true → ∃ γ, α (.cs γ) t 0 = true := by
    intro i
    induction i with
    | zero =>
      intro hi h0
      have := h.preBot t ht
      rw [show (0 : Fin (nc N + 1)) = ⟨0, hi⟩ from rfl, h0] at this
      cases this
    | succ i ih =>
      intro hi h1
      rcases h.preStep t ht ⟨i, by omega⟩ with h2 | h2 | h2
      · rw [show (Fin.succ ⟨i, by omega⟩ : Fin (nc N + 1)) = ⟨i + 1, hi⟩ from rfl, h1] at h2
        cases h2
      · exact ih _ h2
      · exact ⟨_, h2⟩
  exact key _ _ (h.preTop t ht)

/-- From a row to the next. -/
theorem Enc.step (h : Spec N α b Q P) {t V : ℕ} {c : N.tm.Cfg} (ht : t < 2 ^ b) (hE : Enc N α t V c) (hd : dep N ≤ V) (hV : V ≤ 2 ^ Q) :
    Enc N α (t + 1) (V - dep N) (stay N c) := by
  obtain ⟨γ, hγ⟩ := exists_case h ht
  have e : γ = caseOf N c := by
    refine Prod.ext ((hE.lab _).1 (h.csLab t ht γ hγ)) (Prod.ext ((hE.var _).1 (h.csVar t ht γ hγ)) ?_)
    funext k j
    exact (hE.cell k _ j (lt_of_lt_of_le j.2 hd)).1 (h.csCell t ht γ k j hγ)
  subst e
  rw [stay_eq]
  refine ⟨fun x => h.nxLab t ht _ x hγ, fun x => h.nxVar t ht _ x hγ, fun k x q hq => ?_⟩
  change α (.cell k x) (t + 1) q = true ↔ x = ((nxt N (caseOf N c)).stk k ++ (c.stk k).drop (dep N))[q]?
  by_cases hqn : q < ((nxt N (caseOf N c)).stk k).length
  · rw [List.getElem?_append_left hqn]
    exact h.nxCell t ht _ k x q hqn hγ
  · have hqn : ((nxt N (caseOf N c)).stk k).length ≤ q := by omega
    have hn := length_nxt_le N (caseOf N c) k
    have hlen := (h.nxLen t ht _ k ⟨((nxt N (caseOf N c)).stk k).length, by omega⟩ hγ).2 rfl
    have hc := h.copy t ht (q - ((nxt N (caseOf N c)).stk k).length) (by omega) k _ x hlen
    simp only [Nat.sub_add_cancel hqn] at hc
    rw [hc, hE.cell k x _ (by omega), List.getElem?_append_right hqn, List.getElem?_drop, Nat.add_comm]

/-- The first row is the start of the machine on 1^P 0 y, for some y. -/
theorem exists_init (h : Spec N α b Q P) (hP : P + 1 < 2 ^ Q) :
    ∃ y : List Bool, Enc N α 0 (2 ^ Q) (initList N.tm ((unary P ++ y).map N.inputAlphabet.invFun)) := by
  classical
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → Option (N.tm.Γ N.tm.k₀), ∀ q, f q = if α (.cell N.tm.k₀ none) 0 q = true then none
      else if α (.cell N.tm.k₀ (some (N.inputAlphabet.symm false))) 0 q = true then some (N.inputAlphabet.symm false) else some (N.inputAlphabet.symm true) := ⟨_, fun _ => rfl⟩
  have hf : ∀ q < 2 ^ Q, ∀ x, α (.cell N.tm.k₀ x) 0 q = true ↔ x = f q := by
    intro q hq x
    have hone : α (.cell N.tm.k₀ (f q)) 0 q = true := by
      rw [hfdef]
      split_ifs with h1 h2
      · exact h1
      · exact h2
      · rcases h.iSome q hq with h3 | h3 | h3
        · exact absurd h3 h1
        · exact absurd h3 h2
        · exact h3
    constructor
    · intro hx
      by_contra hne
      rcases h.iMost q hq x (f q) hne with h4 | h4
      · rw [hx] at h4; cases h4
      · rw [hone] at h4; cases h4
    · rintro rfl
      exact hone
  obtain ⟨S, hSdef⟩ : ∃ S, S = pref ((List.range (2 ^ Q)).map f) := ⟨_, rfl⟩
  have hL : ∀ i, ((List.range (2 ^ Q)).map f)[i]? = if i < 2 ^ Q then some (f i) else none := by
    intro i
    by_cases hi : i < 2 ^ Q <;> simp [hi]
  have hS : ∀ q < 2 ^ Q, S[q]? = f q := by
    intro q hq
    rw [hSdef, getElem?_pref _ ?_ q (by simpa using hq), hL, if_pos hq]
    · rfl
    · intro i hi x hx
      rw [hL] at hi hx
      split_ifs at hi hx with hi1 hx1
      have hi2 : f i = none := Option.some.inj hi
      have hx2 : f (i + 1) = x := Option.some.inj hx
      have := h.iBlank i hi1 ((hf i hi1 none).2 hi2.symm)
      rw [← hx2]
      exact ((hf (i + 1) hx1 none).1 this).symm
  have hu : ∀ i, i ≤ P → α .u 0 (P - i) = true := by
    intro i
    induction i with
    | zero => intro _; exact h.uP
    | succ i ih =>
      intro hi
      have := h.uStep (P - (i + 1)) (by omega)
      rw [show P - (i + 1) + 1 = P - i by omega] at this
      exact this (ih (by omega))
  have h1 : ∀ q < P, f q = some (N.inputAlphabet.symm true) := by
    intro q hq
    have := hu (P - (q + 1)) (by omega)
    rw [show P - (P - (q + 1)) = q + 1 by omega] at this
    exact ((hf q (by omega) _).1 (h.uOne q (by omega) this)).symm
  have h0 : f P = some (N.inputAlphabet.symm false) := ((hf P (by omega) _).1 h.cellP).symm
  have htake : S.take (P + 1) = (unary P).map N.inputAlphabet.invFun := by
    apply List.ext_getElem?
    intro q
    by_cases hq : q < P + 1
    · rw [List.getElem?_take_of_lt hq, hS q (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq' | rfl
      · rw [h1 q hq']
        simp [unary, List.getElem?_append_left, hq']
      · rw [h0]
        simp [unary]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp [unary]; omega)]
  refine ⟨(S.drop (P + 1)).map N.inputAlphabet, ?_⟩
  have hS' : (unary P ++ (S.drop (P + 1)).map N.inputAlphabet).map N.inputAlphabet.invFun = S := by
    rw [List.map_append, ← htake, List.map_map]
    have : (N.inputAlphabet.invFun ∘ N.inputAlphabet) = id := by funext z; simp
    rw [this, List.map_id, List.take_append_drop]
  rw [hS']
  refine ⟨h.iLab, h.iVar, fun k x q hq => ?_⟩
  by_cases hk : k = N.tm.k₀
  · subst hk
    rw [initList_stk_self, hS q hq]
    exact hf q hq x
  · rw [initList_stk_of_ne N _ hk]
    simpa using h.iCell q hq k hk x

/-- The last row is the halted configuration with the output 1. -/
theorem eq_haltList (h : Spec N α b Q P) {V : ℕ} {c : N.tm.Cfg} (hE : Enc N α (2 ^ b) V c) (hV : 2 ≤ V) :
    c = haltList N.tm [N.outputAlphabet.invFun true] := by
  obtain ⟨l, v, S⟩ := c
  have hl : none = l := (hE.lab none).1 h.fLab
  have hv : N.tm.initialState = v := (hE.var _).1 h.fVar
  have hS : S = (haltList N.tm [N.outputAlphabet.invFun true]).stk := by
    funext k
    by_cases hk : k = N.tm.k₁
    · subst hk
      rw [haltList_stk_self]
      have a0 : some (N.outputAlphabet.symm true) = (S N.tm.k₁)[0]? := (hE.cell _ _ 0 (by omega)).1 h.fOut0
      have a1 : none = (S N.tm.k₁)[1]? := (hE.cell _ _ 1 (by omega)).1 h.fOut1
      cases hS : S N.tm.k₁ with
      | nil => simp [hS] at a0
      | cons z r =>
        cases r with
        | nil => simp [hS] at a0; rw [← a0]; rfl
        | cons z' r => simp [hS] at a1
    · rw [haltList_stk_of_ne N _ hk]
      have a0 : none = (S k)[0]? := (hE.cell _ _ 0 (by omega)).1 (h.fOther k hk)
      cases hS : S k with
      | nil => rfl
      | cons z r => simp [hS] at a0
  subst hl hv hS
  rfl

/-- If the conditions can be satisfied, the machine accepts. -/
theorem acc_of_spec (hP : P + 2 ≤ 2 ^ b) (h : Spec N α b (b + lamOf N) P) : Acc N P (2 ^ b) := by
  have hlam : 2 * dep N + 2 < 2 ^ lamOf N := Nat.lt_size_self _
  have hQ : 2 ^ (b + lamOf N) = 2 ^ b * 2 ^ lamOf N := pow_add _ _ _
  have hb : 0 < 2 ^ b := by positivity
  have hbig : 2 ^ b * dep N + 2 ^ b * 2 ≤ 2 ^ (b + lamOf N) := by
    rw [hQ, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨y, h0⟩ := exists_init h (by omega)
  have hrun : ∀ t, t ≤ 2 ^ b → Enc N α t (2 ^ (b + lamOf N) - t * dep N) ((stay N)^[t] (initList N.tm ((unary P ++ y).map N.inputAlphabet.invFun))) := by
    intro t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      have hle : (t + 1) * dep N ≤ 2 ^ b * dep N := Nat.mul_le_mul_right _ ht
      rw [Function.iterate_succ_apply', Nat.add_mul, Nat.one_mul, ← Nat.sub_sub]
      rw [Nat.add_mul, Nat.one_mul] at hle
      exact (ih (by omega)).step h (by omega) (by omega) (Nat.sub_le _ _)
  have hfin := eq_haltList h (hrun _ le_rfl) (by omega)
  obtain ⟨n, hn, hr⟩ := evals_of_stay N _ _ hfin
  exact ⟨y, ⟨⟨⟨n, hr⟩, hn⟩⟩⟩

end CircuitLowerBound.Tab
