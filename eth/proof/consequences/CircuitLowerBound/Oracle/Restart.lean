/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Oracle.Runs
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): a machine that is started again after every answer can be replaced by an oracle machine

`stRestart`: a language that is in E^NP in the second form (an ordinary machine, started again after
every answer, at most 2^{c(n+1)} rounds of at most 2^{c(n+1)} steps) is in E^NP in the first form
(an oracle machine); the oracle
machine of `Machine.lean` takes at most 2^{(2c+7)(n+1)} steps. -/

public section

namespace CircuitLowerBound

open ENP Turing Groundwork.TM

namespace Oracle

variable {M : TM2ComputableAux Bool Bool}

theorem one_nil_apply (k k' : M.tm.K) : (one k [] : ∀ k', List (M.tm.Γ k')) k' = [] := by
  by_cases h : k' = k
  · subst h; simp
  · simp [one, h]

theorem initList_self (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : (initList tm s).stk tm.k₀ = s := by simp [initList]

theorem initList_ne (tm : FinTM2) (s : List (tm.Γ tm.k₀)) {k : tm.K} (h : k ≠ tm.k₀) : (initList tm s).stk k = [] := by simp [initList, h]

theorem haltList_self (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk tm.k₁ = s := by simp [haltList]

theorem haltList_ne (tm : FinTM2) (s : List (tm.Γ tm.k₁)) {k : tm.K} (h : k ≠ tm.k₁) : (haltList tm s).stk k = [] := by simp [haltList, h]

/-- The first configuration of the oracle machine. -/
theorem initList_otm (x : List Bool) :
    initList (otm M).tm (x.map (otm M).inp.symm) = (⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x [] [])⟩ : Cf M) := by
  have hs : (initList (otm M).tm (x.map (otm M).inp.symm)).stk = stk M (one M.tm.k₀ []) (ns x [] []) := by
    funext k
    rcases k with k | j
    · rw [stk_inl, one_nil_apply]
      exact initList_ne (otm M).tm _ (show (Sum.inl k : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
    · cases j
      · exact (initList_self (otm M).tm _).trans (List.map_id x)
      · exact initList_ne (otm M).tm _ (show (Sum.inr NS.ans : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
      · exact initList_ne (otm M).tm _ (show (Sum.inr NS.sp : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
  exact congrArg (fun S => (⟨some (.inr .cpA), (M.tm.initialState, none), S⟩ : Cf M)) hs

/-- The last configuration of the oracle machine. -/
theorem haltList_otm (b : Bool) :
    haltList (otm M).tm [(otm M).out.symm b] = (⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ : Cf M) := by
  have hs : (haltList (otm M).tm [(otm M).out.symm b]).stk = stk M (one M.tm.k₀ []) (ns [b] [] []) := by
    funext k
    rcases k with k | j
    · rw [stk_inl, one_nil_apply]
      exact haltList_ne (otm M).tm _ (show (Sum.inl k : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
    · cases j
      · exact haltList_self (otm M).tm _
      · exact haltList_ne (otm M).tm _ (show (Sum.inr NS.ans : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
      · exact haltList_ne (otm M).tm _ (show (Sum.inr NS.sp : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
  exact congrArg (fun S => (⟨none, (M.tm.initialState, none), S⟩ : Cf M)) hs

/-- The time: (Y + 1)·(4Y + 3n + 12) ≤ 2^{(2c+7)(n+1)} for Y = 2^{c(n+1)}. -/
theorem time_le (c n : ℕ) :
    (2 ^ (c * (n + 1)) + 1) * (3 * (0 + 2 ^ (c * (n + 1))) + 3 * n + 2 ^ (c * (n + 1)) + 12) ≤ 2 ^ ((2 * c + 7) * (n + 1)) := by
  have hY : 1 ≤ 2 ^ (c * (n + 1)) := Nat.one_le_two_pow
  have hn : n + 1 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self.le
  have h6 : 2 ^ 6 ≤ 2 ^ (6 * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ ((2 * c + 7) * (n + 1)) = 2 ^ (c * (n + 1)) * 2 ^ (c * (n + 1)) * (2 ^ (6 * (n + 1)) * 2 ^ (n + 1)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [e]
  generalize 2 ^ (c * (n + 1)) = Y at hY ⊢
  generalize 2 ^ (n + 1) = Z at hn ⊢
  generalize 2 ^ (6 * (n + 1)) = U at h6 ⊢
  have h1 : Y + 1 ≤ 2 * Y := by omega
  have hZ : 1 ≤ Z := by omega
  have h2 : 3 * (0 + Y) + 3 * n + Y + 12 ≤ 19 * (Y * Z) := by nlinarith
  calc (Y + 1) * (3 * (0 + Y) + 3 * n + Y + 12) ≤ 2 * Y * (19 * (Y * Z)) := Nat.mul_le_mul h1 h2
    _ = Y * Y * (38 * Z) := by ring
    _ ≤ Y * Y * (U * Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num at h6; omega))

end Oracle

open Oracle in
/-- A machine that is started again after every answer can be replaced by an oracle machine. -/
theorem stRestart : StRestart := by
  rintro L ⟨M, c, hfin, h⟩
  refine ⟨otm M, 2 * c + 7, fun k => ?_, fun x => ?_⟩
  · rcases k with k | j
    · exact hfin k
    · exact (inferInstance : Finite Bool)
  · obtain ⟨b, hb, hP⟩ := h x
    obtain ⟨t, ht, hr⟩ := run_protocol hP
    refine ⟨b, hb, ⟨⟨⟨t, ?_⟩, ht.trans (time_le c x.length)⟩⟩⟩
    rw [initList_otm, haltList_otm]
    exact hr.iterate

end CircuitLowerBound
