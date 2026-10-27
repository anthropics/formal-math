/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
public import CountKSat.ProgC
import SparsifyWidthK.SetAlg
import SparsifyWidthK.Refine

/-! # Neither child has more clauses than its parent

This file proves `Shrink.card_light_le` and `Shrink.card_heavy_le` on finite sets, and
`Shrink.length_step_le`, the same for the lists of `stepC`.
The first child is H together with the clauses of F that do not contain H (`stLightEq`), and at
least θ(j−|H|) ≥ 1 clauses of F contain H: one clause comes, at least one goes.
The second child is the sets E ∖ H together with the clauses of F that contain none of them
(`stHeavyEq`). There are at most as many sets E ∖ H as clauses E, and every E goes, since it
contains E ∖ H.
On lists: a formula in normal form has as many clauses as its set of clauses has members, and
`stepC` computes the two children (`stRefines`). -/

public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat

namespace Shrink

variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}

/-- The first child has at most as many clauses as F. -/
theorem card_light_le (hθ : ∀ i, 1 ≤ θ i) (hF : Reduced F) (h : Heart θ F j H) : (light F H).card ≤ F.card := by
  rw [stLightEq _ θ F j H hθ hF h]
  obtain ⟨E, hE⟩ := card_pos.1 (lt_of_lt_of_le (hθ _) h.2.2)
  obtain ⟨hEF, -, hHE⟩ := mem_filter.1 hE
  have hsub : (F.filter fun C => ¬ H ⊆ C) ⊆ F.erase E := by
    intro C hC
    obtain ⟨hCF, hno⟩ := mem_filter.1 hC
    exact mem_erase.2 ⟨fun e => hno (e ▸ hHE), hCF⟩
  have h1 := card_union_le ({H} : Finset (Finset α)) (F.filter fun C => ¬ H ⊆ C)
  have h2 := card_le_card hsub
  have h3 := card_pos.2 ⟨E, hEF⟩
  rw [card_singleton] at h1
  rw [card_erase_of_mem hEF] at h2
  omega

/-- The second child has at most as many clauses as F. -/
theorem card_heavy_le (hF : Reduced F) (h : Heart θ F j H) : (heavy F j H).card ≤ F.card := by
  rw [stHeavyEq _ θ F j H hF h]
  have h1 : (petals F j H).card ≤ (Sparsify.over F j H).card := card_image_le
  have h2 : (F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C) ⊆ F \ Sparsify.over F j H := by
    intro C hC
    obtain ⟨hCF, hno⟩ := mem_filter.1 hC
    exact mem_sdiff.2 ⟨hCF, fun hO => hno (C \ H) (mem_image_of_mem _ hO) sdiff_subset⟩
  calc _ ≤ (petals F j H).card + (F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C).card := card_union_le _ _
    _ ≤ (Sparsify.over F j H).card + (F \ Sparsify.over F j H).card := Nat.add_le_add h1 (card_le_card h2)
    _ = F.card := by rw [Nat.add_comm]; exact card_sdiff_add_card_eq_card (filter_subset _ _)

/-- On lists: for thresholds at least 1, if x.1 is in normal form and none of its clauses contains
another, the formulas of both children of x have at most as many clauses as x.1. -/
theorem length_step_le {k : ℕ} (hθ : ∀ i, 1 ≤ θ i) {x l h : CNode} (hx : NF x.1) (hred : Reduced (toFin x.1)) (hst : stepC θ k x = some (l, h)) :
    l.1.length ≤ x.1.length ∧ h.1.length ≤ x.1.length := by
  obtain ⟨H, P, hp, rfl, rfl⟩ := ProgC.stepC_some hst
  obtain ⟨j, hrule, hP, hnfP, hH⟩ := (Refine.stRefines θ k hθ).some x.1 H P hx hp
  have e1 : toFin (addP [H] x.1) = light (toFin x.1) H.toFinset := by
    rw [toFin_addP, toFin_singleton, stLightEq _ θ _ j _ hθ hred hrule.heart]
    simp
  have e2 : toFin (addP P x.1) = heavy (toFin x.1) j H.toFinset := by
    rw [toFin_addP, hP, stHeavyEq _ θ _ j _ hred hrule.heart]
  constructor
  · show (addP [H] x.1).length ≤ x.1.length
    rw [nf_length_eq (nf_addP (NF_singleton hH) hx), nf_length_eq hx, e1]
    exact card_light_le hθ hred hrule.heart
  · show (addP P x.1).length ≤ x.1.length
    rw [nf_length_eq (nf_addP hnfP hx), nf_length_eq hx, e2]
    exact card_heavy_le hred hrule.heart

end Shrink

end SparsificationLemma
