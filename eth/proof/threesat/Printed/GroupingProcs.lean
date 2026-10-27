/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Close
import Mathlib.Tactic

/-! # Lemma 1 for networks given by procedures

A machine for networks (`Printed.NetMachine`) asks the queries of Definition 2(iii) and is charged τ
operations for each. Here the queries are answered by the four procedures of `SecNetworks.Procs`,
step machines that take at most τ steps each (`SecNetworks.IsNetwork`).
* `map_range_eq_ofFn`, `inputOf_eq`: the input written down from the numbers that the procedures
  give is the input that belongs to the network;
* `answerOf_runs`: the four procedures as one machine answer every query that `netOracle` answers,
  within τ steps;
* `stOnProcedures`: so a machine that does what Lemma 1 says outputs the value within three times
  the bound of Lemma 1 (a query costs τ + 2 ≤ 3τ steps: `QueryMachines.stPlug`). -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Eight Eight.SecNetworks QueryMachines QueryMachines.QueryMachine

/-- A list written with `List.range` and the same list written with `List.ofFn`. -/
theorem map_range_eq_ofFn {α : Type} {g : ℕ} (F : ℕ → α) (f : Fin g → α) (h : ∀ a : Fin g, F a.val = f a) : (List.range g).map F = List.ofFn f := by
  refine List.ext_getElem (by simp) fun i h1 _ => ?_
  have hi : i < g := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact h ⟨i, hi⟩

/-- The input written down from numbers that agree with those of the network N is the input that
belongs to N. -/
theorem inputOf_eq {g : ℕ} (N : Net g) (P B : ℕ) (len : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) (hl : ∀ a : Fin g, len a = N.len a) (hc : ∀ a b : Fin g, a ≠ b → cap a b = N.c a b) :
    inputOf g P B len cap = netInput N P B := by
  unfold inputOf netInput
  rw [map_range_eq_ofFn (fun a => unary (len a)) (fun a : Fin g => unary (N.len a)) fun a => by rw [hl],
    map_range_eq_ofFn (fun a => (List.range g).map fun b => if a = b then [] else unary (cap a b)) (fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b)) fun a =>
      map_range_eq_ofFn _ _ fun b => by
        by_cases hab : a = b
        · rw [if_pos hab, if_pos (congrArg Fin.val hab)]
        · rw [if_neg hab, if_neg fun e => hab (Fin.ext e), hc a b hab]]

/-- The four procedures, as one machine, answer every query of Definition 2(iii) that `netOracle`
answers, within τ steps. -/
theorem answerOf_runs {C : Type} {g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : Np.Give c N P B τ S) {x : NetQuery} {v : ℤ} (hx : netOracle N x = some v) :
    (answerOf Np).Runs (c, x) τ (S + 3) v := by
  rcases x with x | x | x | x
  · simp only [netOracle] at hx
    by_cases h1 : x.1 < g
    · rw [dif_pos h1] at hx
      by_cases h2 : x.2.length = N.len ⟨x.1, h1⟩
      · rw [if_pos h2] at hx
        obtain rfl := Option.some.inj hx
        have r := Stepped.mapOut_runs (f := fun b : Bool => if b = true then (1 : ℤ) else 0) (h.mem_runs ⟨x.1, h1⟩ x.2 h2)
        simp only [decide_eq_true_eq] at r
        exact (Stepped.branch_runs_inl (sel := dist) (a := (c, Sum.inl x)) rfl r).mono le_rfl (by omega)
      · rw [if_neg h2] at hx
        cases hx
    · rw [dif_neg h1] at hx
      cases hx
  · simp only [netOracle] at hx
    split_ifs at hx with h1 h2
    · obtain rfl := Option.some.inj hx
      exact (Stepped.branch_runs_inr (sel := dist) rfl (Stepped.branch_runs_inl (sel := dist) rfl (h.W_runs ⟨x.1, h1⟩ x.2 h2))).mono le_rfl (by omega)
  · simp only [netOracle] at hx
    split_ifs at hx with h1 h2
    · obtain rfl := Option.some.inj hx
      exact Stepped.branch_runs_inr (sel := dist) rfl (Stepped.branch_runs_inr (sel := dist) rfl (Stepped.branch_runs_inl (sel := dist) rfl
        (h.Ψ_runs ⟨x.1.1, h1.1⟩ ⟨x.1.2, h1.2⟩ (fun e => h2.1 (congrArg Fin.val e)) x.2.1 h2.2.1 x.2.2 h2.2.2)))
  · simp only [netOracle] at hx
    split_ifs at hx with h1 h2
    · obtain rfl := Option.some.inj hx
      exact Stepped.branch_runs_inr (sel := dist) rfl (Stepped.branch_runs_inr (sel := dist) rfl (Stepped.branch_runs_inr (sel := dist) rfl
        (h.f_runs ⟨x.1.1, h1.1⟩ ⟨x.1.2, h1.2⟩ (fun e => h2.1 (congrArg Fin.val e)) x.2.1 h2.2.1 x.2.2 h2.2.2)))

/-- **Lemma 1 for networks given by procedures.** -/
theorem stOnProcedures : StOnProcedures := by
  intro NM C₁ g K e hNM C _ Np c N P B τ S hN
  obtain ⟨T, ⟨own, L, hrun, hle⟩, hT⟩ := hNM N P B τ hN.is hN.τ_pos
  have hτ := hN.τ_pos
  have hp := stPlug _ _ _ _ _ NM (answerOf Np) (netOracle N) c (netInput N P B) own _ (S + 3) L N.value (fun _ => τ) hrun fun x _ v hv => answerOf_runs hN.given hv
  rw [sum_map_const] at hle hp
  have hin : inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c) = netInput N P B := by
    rw [hN.given.P_eq, hN.given.B_eq]
    exact inputOf_eq N P B _ _ hN.given.len_eq hN.given.cap_eq
  refine ⟨own + L.length * (τ + 2), ?_, ?_⟩
  · refine Stepped.Runs.mono (Stepped.mapIn_runs ?_) le_rfl (le_refl _)
    rw [hin]
    exact hp.mono le_rfl (by omega)
  · have h1 : L.length ≤ L.length * τ := Nat.le_mul_of_pos_right _ hτ
    have h2 : own + L.length * (τ + 2) ≤ 3 * T := by
      rw [Nat.mul_add]
      omega
    have h3 : ((own + L.length * (τ + 2) : ℕ) : ℝ) ≤ 3 * (T : ℝ) := by exact_mod_cast h2
    refine h3.trans ?_
    linarith

end Printed
