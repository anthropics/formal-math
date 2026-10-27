/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
import all StepMachines.Math.SatNet
import all StepMachines.Prog.Count

/-! # The value of the network of one sparse formula is the number of its satisfying assignments

`proof/machines/StepMachines/Math/SatNet.lean` proves that the value of the network of a formula is
the number of its good states, and that the good states are the
states of the models: the satisfying assignments that are false on every variable that does not
occur. Here the variables are natural numbers. If exactly
the variables below n occur, the models are the satisfying assignments to x₀ … xₙ₋₁, continued by
false (`value_net_eq_cntN`, `value_wordNet_eq_cntN`). -/

public section

namespace CountKSat

open Finset Groundwork Groundwork.Prog Groundwork.SatNet

namespace Value

/-- Below n the continued assignment is the assignment. -/
theorem ext_val {n : ℕ} (a : Fin n → Bool) (i : Fin n) : ext a i.val = a i := by
  simp [ext]

/-- From n on the continued assignment is false. -/
theorem ext_of_le {n i : ℕ} (a : Fin n → Bool) (h : n ≤ i) : ext a i = false := by
  simp [ext, Nat.not_lt.2 h]

/-- The value of the network of a formula in which exactly the variables below n occur is the number
of its satisfying assignments on n variables. -/
theorem value_net_eq_cntN {g μ k n : ℕ} {x : Fml} (hk : ∀ C ∈ x, C.length ≤ k) (hm : x.length ≤ g * μ)
    (hlt : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) (hocc : ∀ i < n, ∃ C ∈ x, ∃ l ∈ C, l.1 = i) :
    (net x g μ k).value = cntN n x := by
  rw [value_eq_card_good]
  congr 1
  symm
  have hmod : ∀ a : Fin n → Bool, (∀ C ∈ x, ∃ l ∈ C, ext a l.1 = l.2) → IsModel x (ext a) := by
    intro a ha
    refine ⟨ha, fun v hv => ?_⟩
    by_cases h : v < n
    · obtain ⟨C, hC, l, hl, rfl⟩ := hocc v h
      exact absurd rfl (hv C hC l hl)
    · exact ext_of_le a (Nat.not_lt.1 h)
  refine Finset.card_bij (fun a _ => toState x (ext a)) ?_ ?_ ?_
  · intro a ha
    simpa using good_toState hk (hmod a (Finset.mem_filter.1 ha).2)
  · intro a ha a' ha' h
    have := toState_inj hk hm (hmod a (Finset.mem_filter.1 ha).2) (hmod a' (Finset.mem_filter.1 ha').2) h
    funext i
    have h2 := congrFun this i.val
    rwa [ext_val, ext_val] at h2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_model hm (Finset.mem_filter.1 hz).2
    have he : ext (fun i : Fin n => a i.val) = a := by
      funext v
      by_cases h : v < n
      · exact ext_val (fun i : Fin n => a i.val) ⟨v, h⟩
      · rw [ext_of_le _ (Nat.not_lt.1 h)]
        exact (ha.2 v fun C hC l hl e => h (e ▸ hlt C hC l hl)).symm
    exact ⟨fun i => a i.val, by simpa [he] using ha.1, by rw [he]⟩

/-- The same for the network that the program builds. -/
theorem value_wordNet_eq_cntN {g k n : ℕ} (hg : 0 < g) {x : Fml} (hk : ∀ C ∈ x, C.length ≤ k)
    (hlt : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) (hocc : ∀ i < n, ∃ C ∈ x, ∃ l ∈ C, l.1 = i) :
    (Count.wordNet g k x).value = cntN n x := by
  rw [Count.value_wordNet hg]
  exact value_net_eq_cntN hk (Count.le_mul_mu hg x) hlt hocc

end Value

end CountKSat
