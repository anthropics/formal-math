/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Ranks
-/

namespace Nc.Tow

open Finset

variable {U κ : Type*} [DecidableEq κ] (idx : U → ℕ) (key : U → κ)

/-- The rank of an element among those with the same key. -/
def rk (F : Finset U) (u : U) : ℕ := (F.filter fun v => key v = key u ∧ idx v < idx u).card

variable {idx key}

theorem rk_congr {F F' : Finset U} {u : U} (h : ∀ v, key v = key u → (v ∈ F ↔ v ∈ F')) :
    rk idx key F u = rk idx key F' u := by
  unfold rk
  congr 1
  ext v
  rw [mem_filter, mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(h v h2).1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(h v h2).2 h1, h2, h3⟩

theorem rk_lt {F : Finset U} {u : U} (hu : u ∈ F) : rk idx key F u < (F.filter fun v => key v = key u).card := by
  refine card_lt_card ?_
  rw [ssubset_iff_of_subset]
  · exact ⟨u, mem_filter.mpr ⟨hu, rfl⟩, fun h => lt_irrefl _ (mem_filter.mp h).2.2⟩
  · intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.1⟩

theorem rk_lt_rk {F : Finset U} {u v : U} (hu : u ∈ F) (huv : key u = key v) (h : idx u < idx v) :
    rk idx key F u < rk idx key F v := by
  refine card_lt_card ?_
  rw [ssubset_iff_of_subset]
  · exact ⟨u, mem_filter.mpr ⟨hu, huv, h⟩, fun h => lt_irrefl _ (mem_filter.mp h).2.2⟩
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨h1, h2.trans huv, h3.trans h⟩

theorem rk_inj (hidx : Function.Injective idx) {F : Finset U} {u v : U} (hu : u ∈ F) (hv : v ∈ F)
    (huv : key u = key v) (h : rk idx key F u = rk idx key F v) : u = v := by
  rcases lt_trichotomy (idx u) (idx v) with h1 | h1 | h1
  · have := rk_lt_rk hu huv h1
    omega
  · exact hidx h1
  · have := rk_lt_rk hv huv.symm h1
    omega

theorem card_rk_le (hidx : Function.Injective idx) (F : Finset U) (k : κ) (a b : ℕ) :
    (F.filter fun u => key u = k ∧ a ≤ rk idx key F u ∧ rk idx key F u < b).card ≤ b - a := by
  rw [← Nat.card_Ico]
  refine card_le_card_of_injOn (rk idx key F) ?_ ?_
  · intro u hu
    have := (mem_filter.1 (mem_coe.1 hu)).2
    exact mem_coe.2 (mem_Ico.2 this.2)
  · intro u hu v hv h
    have hu' := mem_filter.1 (mem_coe.1 hu)
    have hv' := mem_filter.1 (mem_coe.1 hv)
    exact rk_inj hidx hu'.1 hv'.1 (hu'.2.1.trans hv'.2.1.symm) h

/-- Every rank occurs. -/
theorem exists_rk (hidx : Function.Injective idx) (F : Finset U) (k : κ) {w : ℕ}
    (hw : w < (F.filter fun u => key u = k).card) : ∃ u ∈ F, key u = k ∧ rk idx key F u = w := by
  have hinj : Set.InjOn (rk idx key F) (F.filter fun u => key u = k) := by
    intro u hu v hv h
    have hu' := mem_filter.1 (mem_coe.1 hu)
    have hv' := mem_filter.1 (mem_coe.1 hv)
    exact rk_inj hidx hu'.1 hv'.1 (hu'.2.trans hv'.2.symm) h
  have himg : (F.filter fun u => key u = k).image (rk idx key F) = range (F.filter fun u => key u = k).card := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro ρ hρ
      obtain ⟨u, hu, rfl⟩ := mem_image.1 hρ
      obtain ⟨h1, h2⟩ := mem_filter.1 hu
      rw [mem_range, ← h2]
      exact rk_lt h1
    · rw [card_range, card_image_of_injOn hinj]
  have : w ∈ (F.filter fun u => key u = k).image (rk idx key F) := by
    rw [himg, mem_range]; exact hw
  obtain ⟨u, hu, rfl⟩ := mem_image.1 this
  obtain ⟨h1, h2⟩ := mem_filter.1 hu
  exact ⟨u, h1, h2, rfl⟩

end Nc.Tow
