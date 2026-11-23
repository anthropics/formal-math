/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Duality.Abstract

/-!
# Gauges as infima of weights

For an abstract commutative monoid with a covering relation: a function that is defined as the infimum of the weights of
certificates is a gauge, if certificates can be multiplied and added along covers. Used for Theorem thm:duality
(`Paper/Gauges.lean`) and Proposition prop:extend (`Paper/Extension.lean`).
-/

namespace Ov.Duality

open Finset

variable {M : Type*} [CommMonoid M] {D : Cover M}

theorem le_sInf_mul_sInf {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty)
    (hS0 : ∀ a ∈ S, 0 ≤ a) (hT0 : ∀ b ∈ T, 0 ≤ b) {x : ℝ} (h : ∀ a ∈ S, ∀ b ∈ T, x ≤ a * b) :
    x ≤ sInf S * sInf T := by
  have key : ∀ {S : Set ℝ} (_ : S.Nonempty) {b : ℝ} (_ : 0 ≤ b), (∀ a ∈ S, x ≤ a * b) →
      x ≤ sInf S * b := by
    intro S hS b hb h
    rcases hb.eq_or_lt with rfl | hb
    · obtain ⟨a, ha⟩ := hS
      simpa using h a ha
    · rw [← div_le_iff₀ hb]
      exact le_csInf hS fun a ha => (div_le_iff₀ hb).2 (h a ha)
  rw [mul_comm]
  refine key hT (Real.sInf_nonneg hS0) fun b hb => ?_
  rw [mul_comm]
  exact key hS (hT0 b hb) fun a ha => h a ha b hb

/-- Let S t be sets of numbers ≥ 0, the weights of the certificates for t. Their infimum is a gauge
if certificates can be multiplied and put together along covers, 1 has a certificate of weight
1, and none of a weight below 1. -/
theorem isPre_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    (h1 : (1 : ℝ) ∈ S 1) (h1' : ∀ w ∈ S 1, 1 ≤ w)
    (hmul : ∀ s t, ∀ a ∈ S s, ∀ b ∈ S t, a * b ∈ S (s * t))
    (hsum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b → ∀ w : κ → ℝ,
      (∀ k, w k ∈ S (b k)) → ∃ w' ∈ S t, w' ≤ ∑ k, w k) :
    IsPre D (fun t => sInf (S t)) := by
  have bdd : ∀ t, BddBelow (S t) := fun t => ⟨0, fun _ hw => h0 t _ hw⟩
  refine ⟨fun t => Real.sInf_nonneg (h0 t), ?_, ?_, ?_⟩
  · exact le_antisymm (csInf_le (bdd 1) h1) (le_csInf (hne 1) h1')
  · intro s t
    exact le_sInf_mul_sInf (hne s) (hne t) (h0 s) (h0 t) fun a ha b hb =>
      csInf_le (bdd _) (hmul s t a ha b hb)
  · intro κ _ t b hb
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := δ / (Fintype.card κ + 1) with hεd
    have hε : 0 < ε := by positivity
    have hex : ∀ k, ∃ w ∈ S (b k), w < sInf (S (b k)) + ε := fun k =>
      exists_lt_of_csInf_lt (hne _) (by linarith)
    choose w hw hw' using hex
    obtain ⟨w', hw'S, hle⟩ := hsum t b hb w hw
    have h2 : ∑ k, w k ≤ ∑ k, (sInf (S (b k)) + ε) := Finset.sum_le_sum fun k _ => (hw' k).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have h3 : (Fintype.card κ : ℝ) * ε ≤ δ := by
      rw [hεd, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h4 := csInf_le (bdd t) hw'S
    linarith

theorem keeps_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    {x y : M} {c : ℝ} (hc : 0 < c) (h : ∀ t, ∀ w ∈ S (t * y), c * w ∈ S (t * x)) :
    Keeps (fun t => sInf (S t)) x y c := by
  intro t
  have h2 : sInf (S (t * x)) / c ≤ sInf (S (t * y)) := by
    refine le_csInf (hne _) fun a ha => ?_
    rw [div_le_iff₀ hc]
    exact (csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (h t a ha)).trans (mul_comm _ _).le
  rw [div_le_iff₀ hc] at h2
  exact h2.trans (mul_comm _ _).le

/-- Covers can be multiplied. -/
theorem Cover.mul_mul (D : Cover M) {κ κ' : Type} [Fintype κ] [Fintype κ'] {s t : M} {b : κ → M}
    {c : κ' → M} (h : D.cov s b) (h' : D.cov t c) :
    D.cov (s * t) (fun x : Σ _ : κ, κ' => b x.1 * c x.2) := by
  refine D.bind (b := fun k => b k * t) (c := fun k j => b k * c j) (D.mul t h) fun k => ?_
  have := D.mul (b k) h'
  simpa only [mul_comm _ (b k)] using this

end Ov.Duality
