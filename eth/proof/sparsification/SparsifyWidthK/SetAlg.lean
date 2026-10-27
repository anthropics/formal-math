/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces
import Mathlib.Tactic.Linarith

/-! # One step of the branching rule, as sets

This file computes the two children of a step (`light_eq`, `heavy_eq`) and shows that a formula is
satisfied exactly if one of its children is
(`sat_iff`). It uses only the definitions of SparsifyWidthK/Defs.lean and the lemmas on `red` of
StepMachines/Math/Sparsify.lean. At the end the three results are
restated as `StLightEq`, `StHeavyEq` and `StSatIff`, three of the interface statements of
SparsifyWidthK/Interfaces.lean. -/

@[expose] public section

namespace WidthK.SetAlg

open Finset Groundwork Groundwork.Sparsify

variable {α : Type*} [DecidableEq α]

/-- Let no clause of F contain another, and add a set A of proper subsets of clauses of F, none of
which contains another. Then the
inclusion-minimal clauses of F ∪ A are those of A and the clauses of F that contain no member of A. -/
theorem red_union' {F A : Finset (Finset α)} (hF : Reduced F) (hss : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C)
    (hanti : ∀ D ∈ A, ∀ E ∈ A, D ⊆ E → D = E) : red (F ∪ A) = A ∪ F.filter fun C => ∀ D ∈ A, ¬ D ⊆ C := by
  ext C
  simp only [red, mem_filter, mem_union]
  constructor
  · rintro ⟨hC, hmin⟩
    by_cases hCA : C ∈ A
    · exact Or.inl hCA
    · refine Or.inr ⟨hC.resolve_right hCA, fun D hD hDC => hCA ?_⟩
      rw [← hmin D (Or.inr hD) hDC]; exact hD
  · rintro (hCA | ⟨hCF, hno⟩)
    · refine ⟨Or.inr hCA, ?_⟩
      rintro D (hD | hD) hDC
      · obtain ⟨C', hC', hCC'⟩ := hss C hCA
        have := hF C' hC' D hD (hDC.trans hCC'.subset)
        subst this
        exact absurd hDC hCC'.2
      · exact hanti D hD C hCA hDC
    · refine ⟨Or.inl hCF, ?_⟩
      rintro D (hD | hD) hDC
      · exact hF C hCF D hD hDC
      · exact absurd hDC (hno D hD)

/-- The members of `over F i S`: the clauses of F of size i that contain S. -/
theorem mem_over {F : Finset (Finset α)} {i : ℕ} {S C : Finset α} : C ∈ over F i S ↔ C ∈ F ∧ C.card = i ∧ S ⊆ C := by
  simp [over]

/-- A petal is a clause of size j over H, without H. -/
theorem mem_petals {F : Finset (Finset α)} {j : ℕ} {H D : Finset α} : D ∈ petals F j H ↔ ∃ C ∈ over F j H, C \ H = D := by
  simp [petals]

/-- All petals have the same size, j - |H|. -/
theorem card_petal {F : Finset (Finset α)} {j : ℕ} {H D : Finset α} (hD : D ∈ petals F j H) : D.card = j - H.card := by
  obtain ⟨C, hC, rfl⟩ := mem_petals.1 hD
  obtain ⟨-, hj, hs⟩ := mem_over.1 hC
  rw [card_sdiff_of_subset hs, hj]

section step
variable {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}

/-- If all thresholds are at least 1, a heart lies in some clause of size j. -/
theorem exists_over (hθ : ∀ i, 1 ≤ θ i) (h : Heart θ F j H) : ∃ C, C ∈ over F j H := by
  have h1 : 1 ≤ θ (j - H.card) := hθ _
  exact card_pos.1 (by have := h.2.2; omega)

/-- The light child consists of the heart H and the clauses of F that do not contain H. -/
theorem light_eq (hθ : ∀ i, 1 ≤ θ i) (hF : Reduced F) (h : Heart θ F j H) :
    light F H = {H} ∪ F.filter fun C => ¬ H ⊆ C := by
  obtain ⟨C, hC⟩ := exists_over hθ h
  obtain ⟨hCF, hj, hs⟩ := mem_over.1 hC
  rw [light, red_union' hF]
  · simp
  · intro D hD
    obtain rfl := mem_singleton.1 hD
    exact ⟨C, hCF, Finset.ssubset_iff_subset_ne.2 ⟨hs, fun e => by have := h.2.1; rw [e, hj] at this; omega⟩⟩
  · intro D hD E hE _
    rw [mem_singleton.1 hD, mem_singleton.1 hE]

/-- The heavy child consists of the petals and the clauses of F that contain no petal. -/
theorem heavy_eq (hF : Reduced F) (h : Heart θ F j H) :
    heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C := by
  rw [heavy, red_union' hF]
  · intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_petals.1 hD
    obtain ⟨hCF, -, hs⟩ := mem_over.1 hC
    obtain ⟨x, hx⟩ := h.1
    refine ⟨C, hCF, Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, fun e => ?_⟩⟩
    have : x ∈ C \ H := by rw [e]; exact hs hx
    exact (mem_sdiff.1 this).2 hx
  · intro D hD E hE hDE
    exact eq_of_subset_of_card_le hDE (by rw [card_petal hD, card_petal hE])

/-- Truth values satisfy F exactly if they satisfy the light child or the heavy child. This holds
for all F, j and H. -/
theorem sat_iff (v : α → Prop) : Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H) := by
  rw [light, heavy, sat_red, sat_red]
  constructor
  · intro hsat
    by_cases hH : ∃ l ∈ H, v l
    · left
      intro C hC
      rcases mem_union.1 hC with hC | hC
      · exact hsat C hC
      · rw [mem_singleton.1 hC]; exact hH
    · right
      intro D hD
      rcases mem_union.1 hD with hD | hD
      · exact hsat D hD
      · obtain ⟨C, hC, rfl⟩ := mem_petals.1 hD
        obtain ⟨l, hl, hv⟩ := hsat C (mem_over.1 hC).1
        exact ⟨l, mem_sdiff.2 ⟨hl, fun hlH => hH ⟨l, hlH, hv⟩⟩, hv⟩
  · rintro (h | h) <;> exact fun C hC => h C (mem_union_left _ hC)

end step

end WidthK.SetAlg

namespace WidthK

/-- `SetAlg.light_eq` as an interface statement. -/
theorem stLightEq : StLightEq := fun _ _ _ _ _ _ hθ hF h => SetAlg.light_eq hθ hF h

/-- `SetAlg.heavy_eq` as an interface statement. -/
theorem stHeavyEq : StHeavyEq := fun _ _ _ _ _ _ hF h => SetAlg.heavy_eq hF h

/-- `SetAlg.sat_iff` as an interface statement. -/
theorem stSatIff : StSatIff := fun _ _ _ _ _ v => SetAlg.sat_iff v

end WidthK
