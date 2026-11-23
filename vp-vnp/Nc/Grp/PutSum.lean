/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.PutDef
import Nc.Cut.Units
import Nc.Plus.UnitBits

/-!
# Writing the units of a string into a store
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

theorem putAll_congr (keys : List (List Bool)) {u u' : ℕ → List Bool} (t : Tree)
    (h : ∀ i < keys.length, u i = u' i) : putAll keys u t = putAll keys u' t := by
  induction keys generalizing u u' t with
  | nil => rfl
  | cons k ks ih =>
    simp only [putAll]
    rw [h 0 (by simp)]
    exact ih _ fun i hi => h (i + 1) (by simpa using hi)

theorem padTake_eq (ub : ℕ) (r : List Bool) :
    padTake ub r = List.ofFn fun b : Fin ub => r.getD b false := by
  apply List.ext_getElem
  · simp only [padTake, List.length_append, List.length_take, List.length_replicate, List.length_ofFn]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem?_getD]
    simp only [padTake]
    by_cases hi : i < r.length
    · have h3 : i < ub := by simpa using h2
      rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem?_eq_getElem hi, Option.getD_some]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate, List.getElem?_eq_none (by omega),
        Option.getD_none]

theorem putL_gen {ub : ℕ} (hub : 0 < ub) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    putL ub keys r t = if (r.length + ub - 1) / ub = keys.length then
      [putAll keys (fun k => List.ofFn fun b : Fin ub => r.getD (k * ub + b) false) t] else [] := by
  induction keys generalizing r t with
  | nil =>
    simp only [putL, putAll, List.length_nil]
    refine if_congr ?_ rfl rfl
    rw [Nat.div_eq_zero_iff, ← List.length_eq_zero_iff]
    omega
  | cons k ks ih =>
    rw [putL]
    by_cases hr : r = []
    · subst hr
      rw [if_pos rfl, if_neg]
      rw [List.length_nil, zero_add, Nat.div_eq_of_lt (by omega)]
      simp
    · rw [if_neg hr, ih]
      have hl : 0 < r.length := List.length_pos_iff.2 hr
      have hc : (r.length + ub - 1) / ub = ((r.drop ub).length + ub - 1) / ub + 1 := by
        rw [List.length_drop]
        rcases le_or_gt ub r.length with h | h
        · have e1 : r.length + ub - 1 = (r.length - ub + ub - 1) + ub := by omega
          rw [e1, Nat.add_div_right _ hub]
        · have e1 : r.length - ub + ub - 1 = ub - 1 := by omega
          have e2 : r.length + ub - 1 = r.length - 1 + ub := by omega
          rw [e1, e2, Nat.add_div_right _ hub, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
      refine if_congr ?_ ?_ rfl
      · rw [hc, List.length_cons]
        omega
      · simp only [putAll, zero_mul, zero_add, padTake_eq]
        congr 1
        refine putAll_congr _ _ fun i _ => ?_
        congr 1
        funext b
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2
        ring

theorem putL_eq {ub : ℕ} (hub : 0 < ub) (keys : List (List Bool)) (L : List Bool) (t : Tree) :
    putL ub keys (L ++ [true]) t = if ucount ub L = keys.length then
      [putAll keys (fun k => uwBits (unitsOf ub L k)) t] else [] := by
  rw [putL_gen hub]
  have hc : ((L ++ [true]).length + ub - 1) / ub = ucount ub L := by
    have e : (L ++ [true]).length + ub - 1 = L.length + ub := by simp
    rw [e, Nat.add_div_right _ hub, ucount]
  rw [hc]
  split_ifs with h
  · congr 1
    refine putAll_congr _ _ fun i hi => ?_
    rw [unitsOf, if_pos (by omega)]
    rfl
  · rfl

theorem tget_putAll (keys : List (List Bool)) (hk : keys.Nodup) (u : ℕ → List Bool) (t : Tree) (p : List Bool) :
    tget p (putAll keys u t) = if p ∈ keys then ofBits (u (keys.idxOf p)) else tget p t := by
  induction keys generalizing u t with
  | nil => simp [putAll]
  | cons k ks ih =>
    rw [List.nodup_cons] at hk
    rw [putAll, ih hk.2, tget_tset]
    by_cases h1 : p ∈ ks
    · have hne : k ≠ p := fun h => hk.1 (h ▸ h1)
      rw [if_pos h1, if_pos (List.mem_cons_of_mem _ h1), List.idxOf_cons_ne _ hne]
    · rw [if_neg h1]
      by_cases h2 : p = k
      · subst h2
        rw [if_pos rfl, if_pos List.mem_cons_self, List.idxOf_cons_self]
      · rw [if_neg h2, if_neg (by simp [h1, h2])]

end Nc.Grp
