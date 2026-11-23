/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Start
import Nc.Cut.Exact

/-!
# The tables of the parties at the beginning and after the moves, and the values of groups
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A A' K E U0 U1 ub c : ℕ}

section Play

variable {M : Sys F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1}

/-- All units ever held by a party are present if its table is not zero. -/
theorem partyTab_ne_none {init : (Uid A U0 M.N U1 → UW ub) → F} {a : Fin (A + A')} {y : Uid A U0 M.N U1 → UW ub}
    (hinit : init y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id → y id ≠ none)
    (h : partyTab P n o init a y ≠ 0) {id : Uid A U0 M.N U1} (hid : id ∈ Plan.seenAt n o E)
    (ha : Holds (hold0 M.np) (hold1 M.np) a id) : y id ≠ none := by
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  cases id with
  | init b c k => exact hinit h1 _ (init_mem_seen0.2 (Plan.init_mem_seenAt.1 hid)) ha
  | new ν k =>
    obtain ⟨-, hk⟩ := Plan.new_mem_seenAt.1 hid
    obtain ⟨x, ν⟩ := ν
    have h3 : ∀ p, M.part x p = a → roleAt P n o ⟨x, p⟩ y ≠ 0 := by
      intro p hp h0
      refine h2 (Finset.prod_eq_zero (Finset.mem_univ (⟨x, p⟩ : M.R)) ?_)
      have : M.rp ⟨x, p⟩ = a := hp
      rw [if_pos this]
      exact h0
    rcases ha with ha | ha
    · have : a = M.part x ((M.kind x).c ν) := ha
      exact role_new_ne_none (h3 _ this.symm) (Or.inl rfl) hk
    · have : a = M.part x ((M.kind x).d ν) := ha
      exact role_new_ne_none (h3 _ this.symm) (Or.inr rfl) hk

end Play

section Exact

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E}

/-- The tables of all parties at the beginning. -/
noncomputable def initAll (A' : ℕ) {N : Type} [Fintype N] [DecidableEq N] {U0 U1 ub : ℕ} (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (p : Fin (K + K + A')) : (Uid (K + K) U0 N U1 → UW ub) → F :=
  Fin.addCases (motive := fun _ => (Uid (K + K) U0 N U1 → UW ub) → F)
    (fun p => tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p) (fun _ _ => 1) p

variable {mu T cb}

theorem tabFinal_eq {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.N → Fin U1} (p : Fin (K + K + A')) :
    (tabFinal mu T cb P q x ρ n o p : (Uid (K + K) U0 M.N U1 → UW ub) → F) =
      partyTab P n o (initAll mu T cb A' q x ρ n p) p := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · rw [tabFinal, initAll, Fin.addCases_left, Fin.addCases_left]
  · rw [tabFinal, initAll, Fin.addCases_right, Fin.addCases_right]

theorem initAll_ne_none {N : Type} [Fintype N] [DecidableEq N] {f : N → Bool → Fin (K + K + A')}
    {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p : Fin (K + K + A')} {y : Uid (K + K) U0 N U1 → UW ub}
    (h : initAll mu T cb A' q x ρ n p y ≠ 0) :
    ∀ id ∈ seen0 (N := N) (U1 := U1) n, Holds (hold0 f) (hold1 f) p id → y id ≠ none := by
  revert h
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · intro h
    rw [initAll, Fin.addCases_left] at h
    exact tabInit_ne_none h
  · intro _ id hid hh
    cases id with
    | new ν k => exact absurd hid new_not_mem_seen0
    | init a b k =>
      exfalso
      have hne : ∀ a : Fin (K + K), Fin.natAdd (K + K) p ≠ Fin.castAdd A' a := by
        intro a h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      rcases hh with hh | hh
      · exact hne a hh
      · exact hne b hh

theorem tabFinal_ne_none {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.N → Fin U1} {p : Fin (K + K + A')} {y : Uid (K + K) U0 M.N U1 → UW ub}
    (h : tabFinal mu T cb P q x ρ n o p y ≠ 0) {id : Uid (K + K) U0 M.N U1} (hid : id ∈ Plan.seenAt n o E)
    (ha : Holds (hold0 M.np) (hold1 M.np) p id) : y id ≠ none := by
  rw [tabFinal_eq] at h
  exact partyTab_ne_none (fun h0 => initAll_ne_none h0) h hid ha

/-- The contents of shared units are present if the value of the group is not zero. -/
theorem grpVal_ne_none {G : Type} [Fintype G] [DecidableEq G] {P : Plan M U0 U1} {q : Fin (K + 1) → Q}
    {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.N → Fin U1} {grp : Fin (K + K + A') → G}
    {g : G} {b : Uid (K + K) U0 M.N U1 → UW ub} (h : grpVal mu T cb P q x ρ n o grp g b ≠ 0)
    {id : Uid (K + K) U0 M.N U1} (hid : id ∈ P.cur n o E)
    (hg : (grp (hold0 M.np id) = g ∧ grp (hold1 M.np id) ≠ g) ∨
      (grp (hold0 M.np id) ≠ g ∧ grp (hold1 M.np id) = g)) : b id ≠ none :=
  Cut.groupVal_ne_none (fun _ hi => (Plan.mem_cur.1 hi).1)
    (fun _ _ h0 _ hi ha => tabFinal_ne_none h0 hi ha) h hid hg

end Exact

end Nc.G
