/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Layer

/-!
# The chain of subgroups
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

variable {h n : ℕ} [NeZero h]

/-- The kernel of the value at s = 0. -/
noncomputable def Ker (h n : ℕ) [NeZero h] : Subgroup (G h n) := (evG : G h n →* SL2 h).ker

theorem mem_Ker {g : G h n} : g ∈ Ker h n ↔ evG g = 1 := Iff.rfl

/-- **Paper: Section sec:tower.** "Let K_n be the kernel of s ↦ 0; it is a 2-group of order 2^((h²−1)n)." -/
theorem _root_.Paper.prop_tower_kernel (h n : ℕ) [NeZero h] :
    IsPGroup 2 (Ker h n) ∧ Nat.card (Ker h n) = 2 ^ ((h ^ 2 - 1) * n) :=
  ⟨IsPGroup.of_card card_ker_evG, card_ker_evG⟩

/-- The exponent of the number b of chambers at a vertex: b = 2^e. -/
def ee (h : ℕ) : ℕ := h * (h - 1) / 2

/-- The number of steps of the tower. -/
def JJ (h n : ℕ) : ℕ := (h ^ 2 - 1) * n / ee h

theorem exists_chain (h n : ℕ) [NeZero h] : ∃ Γ : ℕ → Subgroup (G h n), Γ 0 = ⊥ ∧ (∀ j, Γ j ≤ Γ (j + 1)) ∧
    (∀ j, Γ j ≤ Ker h n) ∧ ∀ j ≤ JJ h n, Nat.card (Γ j) = (2 ^ ee h) ^ j := by
  classical
  have step : ∀ j, ∀ H : Subgroup (Ker h n), Nat.card H = 2 ^ (ee h * j) → j < JJ h n →
      ∃ H' : Subgroup (Ker h n), Nat.card H' = 2 ^ (ee h * (j + 1)) ∧ H ≤ H' := by
    intro j H hH hj
    refine Sylow.exists_subgroup_card_pow_prime_le 2 ?_ H hH (Nat.mul_le_mul_left _ (Nat.le_succ j))
    rw [(Paper.prop_tower_kernel h n).2]
    refine pow_dvd_pow 2 ?_
    calc ee h * (j + 1) ≤ ee h * JJ h n := Nat.mul_le_mul_left _ hj
      _ ≤ _ := Nat.mul_div_le _ _
  have h0 : Nat.card (⊥ : Subgroup (Ker h n)) = 2 ^ (ee h * min 0 (JJ h n)) := by simp
  have step' : ∀ j, ∀ H : {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min j (JJ h n))},
      ∃ H' : {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min (j + 1) (JJ h n))}, H.1 ≤ H'.1 := by
    intro j H
    by_cases hj : j < JJ h n
    · obtain ⟨H', h1, h2⟩ := step j H.1 (by rw [H.2, min_eq_left hj.le]) hj
      exact ⟨⟨H', by rw [h1, min_eq_left (Nat.succ_le_of_lt hj)]⟩, h2⟩
    · refine ⟨⟨H.1, ?_⟩, le_rfl⟩
      rw [H.2, min_eq_right (not_lt.1 hj), min_eq_right ((not_lt.1 hj).trans (Nat.le_succ j))]
  choose nxt hnxt using step'
  let f : (j : ℕ) → {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min j (JJ h n))} := fun j =>
    Nat.rec ⟨⊥, h0⟩ nxt j
  have hf : ∀ j, (f j).1 ≤ (f (j + 1)).1 := fun j => hnxt j (f j)
  refine ⟨fun j => (f j).1.map (Ker h n).subtype, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_bot _
  · exact fun j => Subgroup.map_mono (hf j)
  · intro j g hg
    obtain ⟨k, -, rfl⟩ := hg
    exact k.2
  · intro j hj
    rw [Nat.card_congr ((f j).1.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm, (f j).2,
      min_eq_left hj, pow_mul]

end Nc.Tower
