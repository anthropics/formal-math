/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Defs.Counting

/-!
# Counting zeros that are simple or on the critical line

This file is purely combinatorial.  It defines the union count, its bad complement,
and the ordinary-ordinate collision count for an abstract `ZeroConfig`.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

/-- Zeros in the window that are simple or on the critical line, counted with multiplicity. -/
def Nu : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂,
    if ρ.re = (2 : ℝ)⁻¹ ∨ Z.mult ρ = 1 then Z.mult ρ else 0

/-- Semantic form of `Nu`: multiplicity restricted to the union of the on-line
and simple supports. -/
theorem Nu_eq_finsum_union :
    Z.Nu T₁ T₂ =
      ∑ᶠ ρ ∈ (Z.window T₁ T₂ ∩ (onLine ∪ Z.simple)), Z.mult ρ := by
  classical
  have hw := Z.window_finite T₁ T₂
  have hu : (Z.window T₁ T₂ ∩ (onLine ∪ Z.simple)).Finite :=
    hw.subset inter_subset_left
  unfold Nu
  rw [finsum_mem_eq_finite_toFinset_sum _ hw,
    finsum_mem_eq_finite_toFinset_sum _ hu, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff,
      mem_union, onLine, simple, mem_ofPred_eq]
    norm_num
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ
    simp

/-- Off-line multiple zeros in the window, counted with multiplicity. -/
def Nbad : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂,
    if ρ.re ≠ (2 : ℝ)⁻¹ ∧ 2 ≤ Z.mult ρ then Z.mult ρ else 0

/-- Total multiplicity in the window at the ordinary ordinate `γ`. -/
def ordinateMass (γ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂, if ρ.im = γ then Z.mult ρ else 0

/-- Union count in the enlarged interval used by the finite Gabor compression. -/
def NuIprime (T : ℝ) : ℕ := Z.Nu (T - D0 T) (2 * T + D0 T)

/-- Bad multiplicity mass in the enlarged interval used by the finite Gabor compression. -/
def NbadIprime (T : ℝ) : ℕ := Z.Nbad (T - D0 T) (2 * T + D0 T)

/-- The factorial second moment of ordinary-ordinate multiplicities:
`Σ_γ M(γ)(M(γ)-1)`, written as a sum over zero points. -/
def ordinateCollision : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂,
    Z.mult ρ * (Z.ordinateMass T₁ T₂ ρ.im - 1)

lemma reflect_im_eq (ρ : ℂ) : (reflect ρ).im = ρ.im := by
  simp [reflect]

lemma reflect_ne_of_re_ne_half {ρ : ℂ} (hρ : ρ.re ≠ (2 : ℝ)⁻¹) : reflect ρ ≠ ρ := by
  intro h
  have hre := congrArg Complex.re h
  simp [reflect] at hre
  apply hρ
  linarith

lemma reflect_mem_window {ρ : ℂ} (hρ : ρ ∈ Z.window T₁ T₂) :
    reflect ρ ∈ Z.window T₁ T₂ := by
  refine ⟨Z.reflect_mem ρ hρ.1, ?_⟩
  simpa [reflect_im_eq] using hρ.2

/-- The union and its bad complement partition the multiplicity count. -/
theorem N_eq_Nu_add_Nbad : Z.N T₁ T₂ = Z.Nu T₁ T₂ + Z.Nbad T₁ T₂ := by
  classical
  have hfin := Z.window_finite T₁ T₂
  unfold N Nu Nbad
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hm := Z.one_le_mult ρ (Z.window_subset_carrier T₁ T₂ (hfin.mem_toFinset.mp hρ))
  by_cases hl : ρ.re = (2 : ℝ)⁻¹
  · simp [hl]
  by_cases hs : Z.mult ρ = 1
  · simp [hl, hs]
  have hm2 : 2 ≤ Z.mult ρ := by omega
  simp [hl, hs, hm2]

/-- The direct weighted union count satisfies inclusion-exclusion. -/
theorem Nu_add_N0s_eq_N0_add_Ns :
    Z.Nu T₁ T₂ + Z.N0s T₁ T₂ = Z.N0 T₁ T₂ + Z.Ns T₁ T₂ := by
  classical
  let s : Finset ℂ := (Z.window_finite T₁ T₂).toFinset
  have hs (ρ : ℂ) : ρ ∈ s ↔ ρ ∈ Z.window T₁ T₂ := by
    simp [s]
  have hNu : Z.Nu T₁ T₂ = ∑ ρ ∈ s,
      if ρ.re = (2 : ℝ)⁻¹ ∨ Z.mult ρ = 1 then Z.mult ρ else 0 := by
    unfold Nu
    rw [finsum_mem_eq_finite_toFinset_sum _ (Z.window_finite T₁ T₂)]
  have hN0 : Z.N0 T₁ T₂ = ∑ ρ ∈ s,
      if ρ.re = (2 : ℝ)⁻¹ then Z.mult ρ else 0 := by
    unfold N0
    have hfin : (Z.window T₁ T₂ ∩ onLine).Finite :=
      (Z.window_finite T₁ T₂).subset inter_subset_left
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff, onLine,
        mem_ofPred_eq, hs]
      norm_num
    · intro ρ hρ
      rfl
  have hNs : Z.Ns T₁ T₂ = ∑ ρ ∈ s,
      if Z.mult ρ = 1 then 1 else 0 := by
    unfold Ns
    have hfin : (Z.window T₁ T₂ ∩ Z.simple).Finite :=
      (Z.window_finite T₁ T₂).subset inter_subset_left
    rw [Set.ncard_eq_toFinset_card _ hfin]
    rw [Finset.sum_boole]
    congr 1
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff, simple,
      mem_ofPred_eq, hs]
  have hN0s : Z.N0s T₁ T₂ = ∑ ρ ∈ s,
      if ρ.re = (2 : ℝ)⁻¹ ∧ Z.mult ρ = 1 then 1 else 0 := by
    unfold N0s
    have hfin : (Z.window T₁ T₂ ∩ onLine ∩ Z.simple).Finite :=
      ((Z.window_finite T₁ T₂).subset inter_subset_left).subset inter_subset_left
    rw [Set.ncard_eq_toFinset_card _ hfin]
    rw [Finset.sum_boole]
    congr 1
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff, onLine, simple,
      mem_ofPred_eq, hs]
    norm_num
    tauto
  rw [hNu, hN0s, hN0, hNs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases h0 : ρ.re = (2 : ℝ)⁻¹ <;>
    by_cases h1 : Z.mult ρ = 1 <;> simp [h0, h1]

/-- Subtractive spelling of inclusion-exclusion.  The natural subtraction is exact,
since it is obtained from the preceding additive identity. -/
theorem Nu_eq_N0_add_Ns_sub_N0s :
    Z.Nu T₁ T₂ = Z.N0 T₁ T₂ + Z.Ns T₁ T₂ - Z.N0s T₁ T₂ :=
  Nat.eq_sub_of_add_eq (Z.Nu_add_N0s_eq_N0_add_Ns T₁ T₂)

/-- A bad point sees at least its reflected mate at the same ordinary ordinate. -/
lemma two_mul_mult_le_ordinateMass {ρ : ℂ} (hwin : ρ ∈ Z.window T₁ T₂)
    (hoff : ρ.re ≠ (2 : ℝ)⁻¹) :
    2 * Z.mult ρ ≤ Z.ordinateMass T₁ T₂ ρ.im := by
  classical
  have hfin := Z.window_finite T₁ T₂
  have hmate : reflect ρ ∈ Z.window T₁ T₂ := Z.reflect_mem_window T₁ T₂ hwin
  have hne : reflect ρ ≠ ρ := reflect_ne_of_re_ne_half hoff
  have hsub : ({ρ, reflect ρ} : Finset ℂ) ⊆ hfin.toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hfin.mem_toFinset.mpr hwin
    · exact hfin.mem_toFinset.mpr hmate
  unfold ordinateMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc
    2 * Z.mult ρ = ∑ z ∈ ({ρ, reflect ρ} : Finset ℂ),
        if z.im = ρ.im then Z.mult z else 0 := by
          simp [hne.symm, reflect_im_eq, Z.mult_reflect ρ hwin.1]
          omega
    _ ≤ ∑ z ∈ hfin.toFinset, if z.im = ρ.im then Z.mult z else 0 :=
      Finset.sum_le_sum_of_subset hsub

/-- Every bad multiplicity unit contributes at least three ordinary-ordinate collisions.
A single reflected pair of double zeros is an equality case. -/
theorem three_Nbad_le_collision :
    3 * Z.Nbad T₁ T₂ ≤ Z.ordinateCollision T₁ T₂ := by
  classical
  have hfin := Z.window_finite T₁ T₂
  unfold Nbad ordinateCollision
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hwin : ρ ∈ Z.window T₁ T₂ := hfin.mem_toFinset.mp hρ
  by_cases hb : ρ.re ≠ (2 : ℝ)⁻¹ ∧ 2 ≤ Z.mult ρ
  · rw [if_pos hb]
    have hM := Z.two_mul_mult_le_ordinateMass T₁ T₂ hwin hb.1
    have hm : 2 ≤ Z.mult ρ := hb.2
    have hfour : 4 ≤ Z.ordinateMass T₁ T₂ ρ.im := by omega
    have hthree : 3 ≤ Z.ordinateMass T₁ T₂ ρ.im - 1 := by omega
    simpa [mul_comm] using Nat.mul_le_mul_left (Z.mult ρ) hthree
  · rw [if_neg hb]
    exact Nat.zero_le _


/-- A point's multiplicity is included in the mass at its own ordinate. -/
lemma mult_le_ordinateMass {ρ : ℂ} (hwin : ρ ∈ Z.window T₁ T₂) :
    Z.mult ρ ≤ Z.ordinateMass T₁ T₂ ρ.im := by
  classical
  have hfin := Z.window_finite T₁ T₂
  have hmem : ρ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hwin
  have hsub : ({ρ} : Finset ℂ) ⊆ hfin.toFinset := by
    intro z hz
    simp only [Finset.mem_singleton] at hz
    simpa [hz] using hmem
  unfold ordinateMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc
    Z.mult ρ = ∑ z ∈ ({ρ} : Finset ℂ),
        if z.im = ρ.im then Z.mult z else 0 := by simp
    _ ≤ ∑ z ∈ hfin.toFinset, if z.im = ρ.im then Z.mult z else 0 :=
      Finset.sum_le_sum_of_subset hsub

/-- The full ordinate-square mass is `N +` the factorial collision count. -/
theorem N_add_collision_eq :
    Z.N T₁ T₂ + Z.ordinateCollision T₁ T₂ =
      ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ * Z.ordinateMass T₁ T₂ ρ.im := by
  classical
  have hfin := Z.window_finite T₁ T₂
  unfold N ordinateCollision
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hwin : ρ ∈ Z.window T₁ T₂ := hfin.mem_toFinset.mp hρ
  have hM : 1 ≤ Z.ordinateMass T₁ T₂ ρ.im :=
    (Z.one_le_mult ρ hwin.1).trans (Z.mult_le_ordinateMass T₁ T₂ hwin)
  have hsub : Z.ordinateMass T₁ T₂ ρ.im - 1 + 1 = Z.ordinateMass T₁ T₂ ρ.im :=
    Nat.sub_add_cancel hM
  calc
    Z.mult ρ + Z.mult ρ * (Z.ordinateMass T₁ T₂ ρ.im - 1)
        = Z.mult ρ * (Z.ordinateMass T₁ T₂ ρ.im - 1) + Z.mult ρ := by omega
    _ = Z.mult ρ * (Z.ordinateMass T₁ T₂ ρ.im - 1 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ = Z.mult ρ * Z.ordinateMass T₁ T₂ ρ.im := by rw [hsub]

/-- A nonnegative pair energy over ordinary ordinates. -/
def ordinateEnergy (K : ℝ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂, ∑ᶠ ρ' ∈ Z.window T₁ T₂,
    (Z.mult ρ : ℝ) * Z.mult ρ' * K (ρ.im - ρ'.im)

/-- A nonnegative kernel with value one at zero dominates all equal-ordinate pairs. -/
theorem N_add_collision_le_energy (K : ℝ → ℝ) (hK : ∀ x, 0 ≤ K x)
    (hK0 : K 0 = 1) :
    (Z.N T₁ T₂ : ℝ) + (Z.ordinateCollision T₁ T₂ : ℝ)
      ≤ Z.ordinateEnergy T₁ T₂ K := by
  classical
  have hfin := Z.window_finite T₁ T₂
  rw [← Nat.cast_add, Z.N_add_collision_eq T₁ T₂,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  unfold ordinateEnergy
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [Nat.cast_mul]
  unfold ordinateMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ' hρ' => ?_
  by_cases heq : ρ'.im = ρ.im
  · rw [heq, if_pos rfl, sub_self, hK0]
    norm_num
  · rw [if_neg heq]
    simp only [Nat.cast_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg (Z.mult ρ)) (Nat.cast_nonneg (Z.mult ρ')))
      (hK (ρ.im - ρ'.im))

end Zeta23.ZeroConfig
