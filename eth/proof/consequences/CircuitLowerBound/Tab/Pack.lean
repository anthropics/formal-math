/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Tab.Spec
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): triples (kind, time, position) and numbers of variables

`stPack`: the formula of a table, whose variables are numbers, is satisfiable if and only if the
clauses of the table, read with triples as variables, are satisfiable in all shifts. The number of a
triple determines the triple, the numbers of the
clauses are the triples (place in the table, t, q), and the places beyond the end of the table only
say that the variable 0, which is no triple of the table, is false. -/

public section

namespace CircuitLowerBound

open ENP

namespace Pack

theorem div_pack {x y M : ℕ} (h : y < M) : (x * M + y) / M = x := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem mod_pack {x y M : ℕ} (h : y < M) : (x * M + y) % M = y := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

theorem tval_le {b t : ℕ} (ht : t < 2 ^ b) (mode : ℕ) : tval b t mode ≤ 2 ^ b := by
  unfold tval
  split_ifs <;> omega

theorem qval_lt {Q P q : ℕ} (hq : q < 2 ^ Q) (hP : P < 2 ^ Q) (mode : ℕ) : qval P q mode < 2 ^ Q := by
  unfold qval
  split_ifs <;> omega

variable {e : MCode} {L P : ℕ}

theorem bt_le_bq (e : MCode) (L : ℕ) : 2 ^ bt e L ≤ 2 ^ bq e L := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)

theorem lam_le_bq (e : MCode) (L : ℕ) : 2 ^ lam e ≤ 2 ^ bq e L := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)

/-- The number of a variable of the table, without reductions. -/
theorem vidx_eq (hg : GoodCode e) (hF : Fits e L P) {c : TCl} (hc : c ∈ tab e) {l : TLit} (hl : l ∈ lits c) {t q : ℕ} (ht : t < 2 ^ bt e L)
    (hq : q < 2 ^ bq e L) :
    vidx e L P t q l = (l.1 * 2 ^ (bt e L + 1) + tval (bt e L) t l.2.1) * 2 ^ (bq e L + 1) + (qval P q l.2.2.1 + l.2.2.2.1) ∧
      tval (bt e L) t l.2.1 < 2 ^ (bt e L + 1) ∧ qval P q l.2.2.1 + l.2.2.2.1 < 2 ^ (bq e L + 1) := by
  obtain ⟨-, h2, h3⟩ := hg c hc l hl
  have h4 := tval_le ht l.2.1
  have h5 := qval_lt (P := P) hq (by have := hF.2; have := bt_le_bq e L; omega) l.2.2.1
  have h6 := lam_le_bq e L
  have h7 : 0 < 2 ^ bt e L := by positivity
  have hA : tval (bt e L) t l.2.1 < 2 ^ (bt e L + 1) := by rw [pow_succ]; omega
  have hB : qval P q l.2.2.1 + l.2.2.2.1 < 2 ^ (bq e L + 1) := by rw [pow_succ]; omega
  exact ⟨by rw [vidx, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hB], hA, hB⟩

/-- The number of the clause at the place r of the table in the shift (t, q). -/
theorem clauseAt_pack (e : MCode) (L P : ℕ) {r t q : ℕ} (ht : t < 2 ^ bt e L) (hq : q < 2 ^ bq e L) :
    clauseAt e L P ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) = (lits ((tab e).getD r zeroCl)).map (litAt e L P t q) := by
  have h1 : ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) / 2 ^ bq e L = r * 2 ^ bt e L + t := div_pack hq
  have h2 : ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) % 2 ^ bq e L = q := mod_pack hq
  have h3 : ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) / 2 ^ (bt e L + bq e L) = r := by
    rw [Nat.add_comm (bt e L), pow_add, ← Nat.div_div_eq_div_mul, h1, div_pack ht]
  rw [clauseAt, h1, h2, h3, mod_pack ht]
  rfl

/-- Every number of a clause is of this form. -/
theorem exists_pack (e : MCode) (L : ℕ) (j : ℕ) : ∃ r t q, t < 2 ^ bt e L ∧ q < 2 ^ bq e L ∧ j = (r * 2 ^ bt e L + t) * 2 ^ bq e L + q :=
  ⟨j / 2 ^ bq e L / 2 ^ bt e L, j / 2 ^ bq e L % 2 ^ bt e L, j % 2 ^ bq e L, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), by
    rw [Nat.div_add_mod', Nat.div_add_mod']⟩

theorem pack_lt {e : MCode} {L r t q : ℕ} (hr : r < 2 ^ rb e) (ht : t < 2 ^ bt e L) (hq : q < 2 ^ bq e L) :
    (r * 2 ^ bt e L + t) * 2 ^ bq e L + q < 2 ^ nb e L := by
  have h1 : r * 2 ^ bt e L + t < 2 ^ rb e * 2 ^ bt e L := by nlinarith
  have h2 : (r * 2 ^ bt e L + t) * 2 ^ bq e L + q < 2 ^ rb e * 2 ^ bt e L * 2 ^ bq e L := by nlinarith
  rwa [nb, pow_add, pow_add]

end Pack

open Pack

/-- Triples and numbers of variables. -/
theorem stPack : StPack := by
  intro e L P hg hF
  have hsat : Sat (tabF e L P) ↔ ∃ a : ℕ → Bool, ∀ j < 2 ^ nb e L, ∃ l ∈ clauseAt e L P j, a l.1 = l.2 := by
    unfold Sat tabF
    simp only [List.forall_mem_map, List.mem_range]
  rw [hsat]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun k t q => a ((k * 2 ^ (bt e L + 1) + t) * 2 ^ (bq e L + 1) + q), fun c hc t ht q hq => ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨l', hl', hal⟩ := ha _ (pack_lt (hr.trans (Nat.lt_size_self _)) ht hq)
    rw [clauseAt_pack e L P ht hq, List.getD_eq_getElem _ _ hr] at hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    refine ⟨l, hl, ?_⟩
    rw [litAt, (vidx_eq hg hF hc hl ht hq).1] at hal
    exact hal
  · rintro ⟨α, hα⟩
    refine ⟨fun v => if v / 2 ^ (bq e L + 1) / 2 ^ (bt e L + 1) = 0 then false
      else α (v / 2 ^ (bq e L + 1) / 2 ^ (bt e L + 1)) (v / 2 ^ (bq e L + 1) % 2 ^ (bt e L + 1)) (v % 2 ^ (bq e L + 1)), fun j _ => ?_⟩
    obtain ⟨r, t, q, ht, hq, rfl⟩ := exists_pack e L j
    rw [clauseAt_pack e L P ht hq]
    by_cases hr : r < (tab e).length
    · rw [List.getD_eq_getElem _ _ hr]
      have hc := List.getElem_mem hr
      obtain ⟨l, hl, hh⟩ := hα _ hc t ht q hq
      refine ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
      obtain ⟨h1, h2, h3⟩ := vidx_eq hg hF hc hl ht hq
      have hk := (hg _ hc l hl).1
      simp only [litAt, h1, div_pack h3, mod_pack h3, div_pack h2, mod_pack h2]
      rw [if_neg (by omega)]
      exact hh
    · rw [List.getD_eq_default _ _ (by omega)]
      refine ⟨_, List.mem_map.2 ⟨zeroCl.1, by simp [lits], rfl⟩, ?_⟩
      have : vidx e L P t q zeroCl.1 = 0 := by simp [vidx, zeroCl, tval, qval]
      simp only [litAt, this]
      simp [zeroCl]

end CircuitLowerBound
