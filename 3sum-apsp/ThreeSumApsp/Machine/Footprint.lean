/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Machine.Steps

/-!
# What a run of the word RAM reads and writes

* One step writes at most one cell (`step_mem`) and reads at most two (`reads`, `card_reads_le`,
  `step_congr`).
* A run that ends within `t` steps changes at most `t` cells (`changed_cells`) and depends on at
  most `2t` cells (`exec_congr`); two runs from one configuration have the same result
  (`exec_unique`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec)

variable {W : ℕ}

/-! ## One step -/

/-- One step changes at most one cell. -/
theorem step_mem (P : List Instr) (c next : Cfg W) (h : step P c = .inl next) :
    ∃ i : ℤ, AgreeOutside {i} c.mem next.mem := by
  cases hI : P.getD c.pc .reject <;> simp only [step, hI, Sum.inl.injEq, reduceCtorEq] at h <;>
    subst h
  case bltz => exact ⟨0, fun _ _ => rfl⟩
  all_goals exact ⟨_, fun a ha => if_neg ha⟩

/-- The cells that an instruction reads. -/
def reads (m : ℤ → BitVec W) : Instr → Finset ℤ
  | .one _ => ∅
  | .add _ j k => {j, k}
  | .sub _ j k => {j, k}
  | .mul _ j k => {j, k}
  | .load _ j => {j, (m j).toInt}
  | .store i j => {i, j}
  | .bltz i _ => {i}
  | .accept => ∅
  | .reject => ∅

/-- An instruction reads at most two cells. -/
theorem card_reads_le (m : ℤ → BitVec W) (ins : Instr) : (reads m ins).card ≤ 2 := by
  cases ins <;> simp only [reads, Finset.card_empty, Finset.card_singleton] <;>
    first | omega | exact Finset.card_le_two

/-- A step from a second configuration at the same position whose memory agrees on the cells that
are read: the same verdict, or the same next position, and every cell on which the memories agreed
is a cell on which they agree afterwards. -/
theorem step_congr (P : List Instr) (c c₂ : Cfg W) (hpc : c₂.pc = c.pc)
    (hr : ∀ a ∈ reads c.mem (P.getD c.pc .reject), c₂.mem a = c.mem a) :
    (∀ v, step P c = .inr v → step P c₂ = .inr v) ∧
      ∀ next, step P c = .inl next → ∃ next₂, step P c₂ = .inl next₂ ∧ next₂.pc = next.pc ∧
        ∀ a, c₂.mem a = c.mem a → next₂.mem a = next.mem a := by
  cases hI : P.getD c.pc .reject <;> rw [hI] at hr <;>
    simp only [reads, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Finset.notMem_empty, false_imp_iff, implies_true] at hr <;>
    simp only [step, hI, hpc, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_imp_iff,
      implies_true, true_and, and_true, forall_eq']
  case bltz => exact ⟨_, rfl, by simp only [hr], fun a ha => ha⟩
  all_goals exact ⟨_, rfl, rfl, fun a ha => by
    first | simp only [hr.1, hr.2] | simp only
    split_ifs <;> [rfl; exact ha]⟩

/-! ## Runs -/

/-- A run of `t` steps changes at most `t` cells. -/
theorem changed_cells (P : List Instr) : ∀ (t : ℕ) (c : Cfg W) (m' : ℤ → BitVec W) (verdict : Bool),
    exec P t c.pc c.mem = some (verdict, m') →
      ∃ S : Finset ℤ, S.card ≤ t ∧ AgreeOutside S c.mem m'
  | 0, _, _, _, h => by simp [WordRam.exec_zero] at h
  | t + 1, c, m', verdict, h => by
    cases hs : step P c with
    | inr v =>
      rw [WordRam.exec_succ_of_verdict hs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨∅, by simp, h.2 ▸ .refl _ _⟩
    | inl n =>
      rw [WordRam.exec_succ_of_step hs] at h
      obtain ⟨S, hS, hm⟩ := changed_cells P t n m' verdict h
      obtain ⟨i, hi⟩ := step_mem P c n hs
      refine ⟨insert i S, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
      rw [Finset.coe_insert, Set.insert_eq]
      exact hi.trans_union hm

/-- A run of `t` steps reads at most `2t` cells: a run from the same position on a memory that
agrees on these cells gives the same verdict after the same number of steps. -/
theorem exec_congr (P : List Instr) : ∀ (t : ℕ) (c : Cfg W) (r : Bool × (ℤ → BitVec W)),
    exec P t c.pc c.mem = some r →
      ∃ R : Finset ℤ, R.card ≤ 2 * t ∧
        ∀ c₂ : Cfg W, c₂.pc = c.pc → (∀ a ∈ R, c₂.mem a = c.mem a) →
          ∃ m₂', exec P t c₂.pc c₂.mem = some (r.1, m₂')
  | 0, _, _, h => by simp [WordRam.exec_zero] at h
  | t + 1, c, r, h => by
    cases hs : step P c with
    | inr v =>
      rw [WordRam.exec_succ_of_verdict hs] at h
      refine ⟨reads c.mem (P.getD c.pc .reject), (card_reads_le _ _).trans (by omega),
        fun c₂ hpc hr => ?_⟩
      rw [WordRam.exec_succ_of_verdict ((step_congr P c c₂ hpc hr).1 v hs)]
      simp only [Option.some.injEq] at h
      exact ⟨c₂.mem, by rw [← h]⟩
    | inl n =>
      rw [WordRam.exec_succ_of_step hs] at h
      obtain ⟨R, hR, hc⟩ := exec_congr P t n r h
      have hcard := card_reads_le c.mem (P.getD c.pc .reject)
      refine ⟨reads c.mem (P.getD c.pc .reject) ∪ R,
        (Finset.card_union_le _ _).trans (by omega), fun c₂ hpc hr => ?_⟩
      obtain ⟨n₂, hs₂, hpc₂, hm₂⟩ :=
        (step_congr P c c₂ hpc fun a ha => hr a (Finset.mem_union_left _ ha)).2 n hs
      rw [WordRam.exec_succ_of_step hs₂]
      exact hc n₂ hpc₂ fun a ha => hm₂ a (hr a (Finset.mem_union_right _ ha))

/-- Two runs of a program from the same configuration have the same result. -/
theorem exec_unique {P : List Instr} {t t' : ℕ} {c : Cfg W} {r r' : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (h' : exec P t' c.pc c.mem = some r') : r = r' := by
  have hmax := WordRam.exec_mono h (le_max_left t t')
  rw [WordRam.exec_mono h' (le_max_right t t')] at hmax
  exact (Option.some.inj hmax).symm

end ThreeSumApsp.WordRam
