/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCounted.Trimmed
import PiecesCounted.PaddedData
import PiecesCounted.Sizes
import Mathlib.Tactic

/-! # All numbers of bits at most 2λ: the new algorithm answers every question
The data `trimmed D` and the algorithm `assumeAlg Alg` are defined in `Trimmed.lean`, after the
remark following Definition 7 that all numbers of bits may be taken at most 2λ, with c + 2 for c.
Here: question by question, the new algorithm returns the right answer for the new data within
2^{(c+2)λ} operations (`assume_computes`), and the statement `MayAssume` follows. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-- The smaller of two natural numbers, computed on integers. -/
theorem ite_cast_min (n m : ℕ) : (if (n : ℤ) ≤ (m : ℤ) then (n : ℤ) else (m : ℤ)) = ((min n m : ℕ) : ℤ) := by
  by_cases h : n ≤ m
  · rw [if_pos (by exact_mod_cast h), min_eq_left h]
  · rw [if_neg (by exact_mod_cast h), min_eq_right (by omega)]

/-- The new algorithm computes the new data within 2^{(c+2)λ} operations. -/
theorem assume_computes {D : Data} {ρ : ℝ} {c : ℕ} {Alg : Stepped (List Unit × Question) Answer} (hD : D.Is ρ c) (hC : Computes Alg D c) : Computes (assumeAlg Alg) (trimmed D) (c + 2) := by
  intro g a hg
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  have s1 := (trimmed_is hD).size_question_le' hg
  have s2 := (trimmed_is hD).size_answer_le' hg
  have b1 := four_steps_le c hl
  have b2 := two_room_le hD.c_pos hl
  have b3 := room_eq c g.1.length
  have b4 : 1 ≤ steps c g.1.length := Nat.one_le_two_pow
  have one : ∀ a₀, Alg.Runs (firstQ g) (steps c g.1.length) (room c g.1.length) a₀ → afterFirst (g, a₀) = .inl a → (assumeAlg Alg).Runs g (steps (c + 2) g.1.length) (room (c + 2) g.1.length) a :=
    fun a₀ h1 h2 => (assumeAlg_runs_one h1 h2).mono (by omega) (by omega)
  have two : ∀ a₀ g', Alg.Runs (firstQ g) (steps c g.1.length) (room c g.1.length) a₀ → afterFirst (g, a₀) = .inr g' → Alg.Runs g' (steps c g.1.length) (room c g.1.length) a →
      (assumeAlg Alg).Runs g (steps (c + 2) g.1.length) (room (c + 2) g.1.length) a :=
    fun a₀ g' h1 h2 h3 => (assumeAlg_runs_two h1 h2 h3).mono (by omega) (by omega)
  clear s1 s2 b1 b2 b3 b4
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha one two ⊢
  rcases q with q | q | q | q | q
  · exact one a (hC _ a hg) rfl
  · exact one a (hC _ a hg) rfl
  · obtain ⟨tr, i⟩ := q
    simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      have hi' : i ∈ (D.fam u.length).I := hi
      have ea : a = .inl ((trimmed D).cap u.length tr i : ℤ) := (Option.some.inj ha).symm
      subst ea
      have e : afterFirst ((u, .inr (.inr (.inl (tr, i)))), .inl (D.cap u.length tr i : ℤ)) = .inl (.inl ((trimmed D).cap u.length tr i : ℤ)) := by
        rw [trimmed_cap, ← ite_cast_min]
        rfl
      exact one _ (hC _ _ (oracle_cap hl hi' tr)) e
    · cases ha
  · exact one a (hC _ a hg) rfl
  · obtain ⟨⟨tr, side⟩, i, l1, l2, θ⟩ := q
    simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      have ea : a = .inl ((trimmed D).fn u.length tr side i (toBits _ l1, toBits _ l2) θ) := (Option.some.inj ha).symm
      obtain ⟨hi, e1, e2, e3⟩ := hi
      have hi' : i ∈ (D.fam u.length).I := hi
      have e1' : l1.length = u.length := e1
      have e2' : l2.length = u.length := e2
      have e3' : θ.length = min (D.cap u.length tr i) (2 * u.length) := e3.trans (trimmed_cap D _ _ _)
      have r1 := hC _ _ (oracle_cap hl hi' tr)
      by_cases hc : D.cap u.length tr i ≤ 2 * u.length
      · rw [min_eq_left hc] at e3'
        have hp : ((D.cap u.length tr i : ℕ) : ℤ) ≤ ((2 * u.length : ℕ) : ℤ) := by exact_mod_cast hc
        have e : afterFirst ((u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))), .inl (D.cap u.length tr i : ℤ)) = .inr (u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))) :=
          if_pos hp
        rw [trimmed_fn_of_le hc] at ea
        subst ea
        exact two _ _ r1 e (hC _ _ (oracle_fn hl hi' side e1' e2' e3'))
      · rw [min_eq_right (by omega)] at e3'
        have hn : ¬ ((D.cap u.length tr i : ℕ) : ℤ) ≤ ((2 * u.length : ℕ) : ℤ) := by exact_mod_cast hc
        have t1 : (θ.take u.length).length = u.length := by rw [List.length_take]; omega
        have t2 : (θ.drop u.length).length = u.length := by rw [List.length_drop]; omega
        cases side
        · have e : afterFirst ((u, .inr (.inr (.inr (.inr ((tr, false), i, l1, l2, θ))))), .inl (D.cap u.length tr i : ℤ)) = .inl (.inl (if l1 ++ l2 = θ then 1 else 0)) := if_neg hn
          rw [trimmed_fn_first hc, bitsOf_toBits e1', bitsOf_toBits e2'] at ea
          subst ea
          exact one _ r1 e
        · cases tr
          · have e : afterFirst ((u, .inr (.inr (.inr (.inr ((false, true), i, l1, l2, θ))))), .inl (D.cap u.length false i : ℤ)) =
                .inr (u, .inr (.inr (.inr (.inl (i, θ.take u.length, θ.drop u.length, l1, l2))))) := if_neg hn
            rw [trimmed_fn_row hc] at ea
            subst ea
            exact two _ _ r1 e (hC _ _ (oracle_value hl hi' t1 t2 e1' e2'))
          · have e : afterFirst ((u, .inr (.inr (.inr (.inr ((true, true), i, l1, l2, θ))))), .inl (D.cap u.length true i : ℤ)) =
                .inr (u, .inr (.inr (.inr (.inl (i, θ.take u.length, l1, θ.drop u.length, l2))))) := if_neg hn
            rw [trimmed_fn_col hc] at ea
            subst ea
            exact two _ _ r1 e (hC _ _ (oracle_value hl hi' t1 e1' t2 e2'))
    · cases ha

/-- `MayAssume`: pieces with parameters (ρ, c) give pieces with parameters (ρ, c + 2) with the same
d, 𝓘 and A_i and with all numbers of bits at most 2λ. -/
theorem mayAssume : MayAssume := fun _ c D Alg h =>
  ⟨trimmed D, assumeAlg Alg, ⟨(trimmed_is h.is).grow le_rfl h.is.rho_lt (Nat.le_add_right c 2), assumeAlg_polyT h.polyTimeSteps, assume_computes h.is h.computes⟩,
    fun lam => ⟨rfl, rfl, rfl, fun tr i => by rw [trimmed_cap]; exact min_le_right _ _⟩⟩

end PiecesCounted
