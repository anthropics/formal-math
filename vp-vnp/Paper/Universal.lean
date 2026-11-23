/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.UniversalSteps
import Nc.Dl.Cut
import NS1.Main

/-!
# The paper, section "Cutting computations": the universal automaton
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A]

theorem map_word {Γ : Type} (f : Bool → Γ) (z : Tree) :
    (Nc.Uni.word z).map f = Nc.Dl.wordG (f false) (f true) z := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [Nc.Uni.word, Nc.Dl.wordG, List.map_cons, List.map_append, iha, ihb]

/-- **Paper: Proposition prop:universal.** "There are a tape automaton and a constant C such that its value, on the standard
code of an instance z as a word, in t steps, is pv(z) whenever z is τ-plain and t ≥ C(|z|+τ) lg(|z|+τ)²." -/
theorem prop_universal (θ : List Bool → A) (hθ : (Function.support θ).Finite) :
    ∃ (S Γ Q : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : Fintype Γ) (_ : DecidableEq Γ) (_ : Fintype Q)
      (_ : DecidableEq Q) (mu : Nc.Letter S Unit Γ → Matrix Q Q A) (i e : Q) (b0 b1 : Γ) (C : ℕ),
      ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
        Nc.runVal mu i e t (fun _ => Nc.Dl.wordG b0 b1 z) = pv θ z := by
  classical
  have hs : ∀ q, q ∉ hθ.toFinset → θ q = 0 := by
    intro q hq
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hq
    exact hq
  obtain ⟨S₀, h1, C, h2⟩ := prop_universal_series θ hθ.toFinset hs
  obtain ⟨Q, iQ, dQ, mu, i, e, -, h3⟩ := Nc.exists_run_val h1
  refine ⟨_, _, Q, inferInstance, inferInstance, inferInstance, inferInstance, iQ, dQ, mu, i, e, .bit false, .bit true,
    27 * (2 * C + 2), fun τ z t hp ht => ?_⟩
  obtain ⟨a1, a2⟩ := h2 τ z hp
  rw [← map_word Nc.Uni.Sy.bit z, ← a2]
  refine h3 _ _ _ a1 (le_trans ?_ ht)
  simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, map_word, Nc.Dl.length_wordG]
  have hn : 1 ≤ z.size + τ := by
    have := Tree.size_pos z
    omega
  have hlg : lg (z.size + τ + 2) ≤ 3 * lg (z.size + τ) := by
    have h3 : z.size + τ + 2 < 2 ^ (lg (z.size + τ) + 2) := by
      have := lt_two_pow_lg (z.size + τ)
      rw [pow_add]
      omega
    have h4 : lg (z.size + τ + 2) ≤ lg (z.size + τ) + 2 := Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow' (by omega) h3)
    have h5 : 1 ≤ lg (z.size + τ) := Nat.succ_le_succ (Nat.zero_le _)
    omega
  have h6 : 1 ≤ lg (z.size + τ + 2) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h7 : z.size + 1 ≤ 2 * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2) := by
    have := Nat.le_mul_of_pos_right (z.size + τ + 2) (show 0 < lg (z.size + τ + 2) ^ 2 by omega)
    omega
  calc 2 * (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) + z.size + 1
      ≤ (2 * C + 2) * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2) := by
        rw [add_mul (2 * C) 2, mul_assoc 2 C]; omega
    _ ≤ (2 * C + 2) * ((3 * (z.size + τ)) * (3 * lg (z.size + τ)) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hlg 2))
    _ = _ := by ring

end Paper
