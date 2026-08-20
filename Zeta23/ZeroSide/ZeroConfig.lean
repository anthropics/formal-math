/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Defs.UnionCounting

/-!
# Reflection-mate multiplicity energy

This file is purely finite combinatorics for an abstract `ZeroConfig`.  It retains the
half-open ordinate window `T₁ < Im ρ ≤ T₂` and the explicit point multiplicities.

At a horizontal location `x = Re ρ - 1/2`, reflection sends `x` to `-x` without
changing the ordinate and preserves multiplicity.  The same-location energy is
`m (m - 1)`.  The reflection-mate energy uses `m (m - 1)` at `x = 0`, where a
multiplicity unit must not mate with itself, and `m(x) m(-x)` off the line.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

/-- The point with ordinate `γ` and horizontal displacement `x = Re ρ - 1/2`. -/
def horizontalPoint (γ x : ℝ) : ℂ := ⟨(2 : ℝ)⁻¹ + x, γ⟩

@[simp] lemma horizontalPoint_re (γ x : ℝ) : (horizontalPoint γ x).re = (2 : ℝ)⁻¹ + x := rfl
@[simp] lemma horizontalPoint_im (γ x : ℝ) : (horizontalPoint γ x).im = γ := rfl

/-- Reflection negates horizontal displacement and preserves the ordinate. -/
lemma reflect_horizontalPoint (γ x : ℝ) :
    reflect (horizontalPoint γ x) = horizontalPoint γ (-x) := by
  apply Complex.ext <;> simp [horizontalPoint, reflect]
  ring

/-- Window-restricted horizontal multiplicity.  It is zero away from the configured
point set or outside the half-open ordinate window. -/
def horizontalMultiplicity (γ x : ℝ) : ℕ := by
  classical
  exact if horizontalPoint γ x ∈ Z.window T₁ T₂ then Z.mult (horizontalPoint γ x) else 0

/-- The horizontal multiplicity function is even at every ordinate. -/
theorem horizontalMultiplicity_neg (γ x : ℝ) :
    Z.horizontalMultiplicity T₁ T₂ γ (-x) = Z.horizontalMultiplicity T₁ T₂ γ x := by
  classical
  rw [horizontalMultiplicity, horizontalMultiplicity, ← reflect_horizontalPoint]
  by_cases h : horizontalPoint γ x ∈ Z.window T₁ T₂
  · rw [if_pos h, if_pos (Z.reflect_mem_window T₁ T₂ h)]
    exact Z.mult_reflect _ h.1
  · have hreflect : reflect (horizontalPoint γ x) ∉ Z.window T₁ T₂ := by
      intro hr
      have hrr := Z.reflect_mem_window T₁ T₂ hr
      apply h
      simpa [reflect] using hrr
    rw [if_neg h, if_neg hreflect]

/-- Multiplicity mass away from the critical line. -/
def Noff : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂,
    if ρ.re ≠ (2 : ℝ)⁻¹ then Z.mult ρ else 0

/-- Same-location factorial multiplicity energy
`Q_loc = Σ_ρ m_ρ (m_ρ - 1)` in the half-open window. -/
def Qloc : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ * (Z.mult ρ - 1)

/-- Reflection-mate energy.  At an on-line point reflection fixes the location, so the
point contributes `m (m - 1)`.  An off-line point contributes `m_ρ m_{reflect ρ}`;
both members of a reflected pair occur in the sum. -/
def Pmate : ℕ :=
  ∑ᶠ ρ ∈ Z.window T₁ T₂,
    Z.mult ρ *
      (if ρ.re = (2 : ℝ)⁻¹ then Z.mult ρ - 1 else Z.mult (reflect ρ))

/-- The fiber of the half-open window at one ordinary ordinate. -/
def ordinateFiber (γ : ℝ) : Set ℂ :=
  Z.window T₁ T₂ ∩ {ρ | ρ.im = γ}

lemma ordinateFiber_finite (γ : ℝ) : (Z.ordinateFiber T₁ T₂ γ).Finite :=
  (Z.window_finite T₁ T₂).subset inter_subset_left

/-- Same-location energy in one ordinate fiber. -/
def QlocAt (γ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Z.ordinateFiber T₁ T₂ γ, Z.mult ρ * (Z.mult ρ - 1)

/-- Off-line multiplicity mass in one ordinate fiber. -/
def NoffAt (γ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Z.ordinateFiber T₁ T₂ γ,
    if ρ.re ≠ (2 : ℝ)⁻¹ then Z.mult ρ else 0

/-- Reflection-mate energy in one ordinate fiber. -/
def PmateAt (γ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Z.ordinateFiber T₁ T₂ γ,
    Z.mult ρ *
      (if ρ.re = (2 : ℝ)⁻¹ then Z.mult ρ - 1 else Z.mult (reflect ρ))

private lemma pmate_term_eq {ρ : ℂ} (hρ : ρ ∈ Z.window T₁ T₂) :
    Z.mult ρ *
        (if ρ.re = (2 : ℝ)⁻¹ then Z.mult ρ - 1 else Z.mult (reflect ρ)) =
      Z.mult ρ * (Z.mult ρ - 1) +
        (if ρ.re ≠ (2 : ℝ)⁻¹ then Z.mult ρ else 0) := by
  have hm : 1 ≤ Z.mult ρ := Z.one_le_mult ρ hρ.1
  by_cases hline : ρ.re = (2 : ℝ)⁻¹
  · simp [hline]
  · rw [if_neg hline, Z.mult_reflect ρ hρ.1, if_pos hline]
    calc
      Z.mult ρ * Z.mult ρ = Z.mult ρ * (Z.mult ρ - 1 + 1) := by
        rw [Nat.sub_add_cancel hm]
      _ = Z.mult ρ * (Z.mult ρ - 1) + Z.mult ρ := by
        rw [Nat.mul_add, Nat.mul_one]

/-- Fiberwise mate decomposition: `P_mate(γ) = Q_loc(γ) + N_off(γ)`. -/
theorem PmateAt_eq_QlocAt_add_NoffAt (γ : ℝ) :
    Z.PmateAt T₁ T₂ γ = Z.QlocAt T₁ T₂ γ + Z.NoffAt T₁ T₂ γ := by
  classical
  have hfin := Z.ordinateFiber_finite T₁ T₂ γ
  unfold PmateAt QlocAt NoffAt
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact Z.pmate_term_eq T₁ T₂ (inter_subset_left (hfin.mem_toFinset.mp hρ))

/-- Window mate decomposition: `P_mate = Q_loc + N_off`. -/
theorem Pmate_eq_Qloc_add_Noff :
    Z.Pmate T₁ T₂ = Z.Qloc T₁ T₂ + Z.Noff T₁ T₂ := by
  classical
  have hfin := Z.window_finite T₁ T₂
  unfold Pmate Qloc Noff
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ρ hρ =>
    Z.pmate_term_eq T₁ T₂ (hfin.mem_toFinset.mp hρ)

/-- Every multiplicity unit not represented by a simple on-line point is paid for by
reflection-mate energy.  This additive form avoids natural-subtraction side conditions. -/
theorem N_le_N0s_add_Pmate :
    Z.N T₁ T₂ ≤ Z.N0s T₁ T₂ + Z.Pmate T₁ T₂ := by
  classical
  have hfin := Z.window_finite T₁ T₂
  let s : Finset ℂ := hfin.toFinset
  have hs (ρ : ℂ) : ρ ∈ s ↔ ρ ∈ Z.window T₁ T₂ := by
    simp [s]
  have hN0s : Z.N0s T₁ T₂ = ∑ ρ ∈ s,
      if ρ.re = (2 : ℝ)⁻¹ ∧ Z.mult ρ = 1 then 1 else 0 := by
    unfold N0s
    have hgood : (Z.window T₁ T₂ ∩ onLine ∩ Z.simple).Finite :=
      (hfin.subset inter_subset_left).subset inter_subset_left
    rw [Set.ncard_eq_toFinset_card _ hgood, Finset.sum_boole]
    congr 1
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff,
      onLine, simple, mem_ofPred_eq, hs]
    norm_num
    tauto
  unfold N Pmate
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, hN0s,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hwin : ρ ∈ Z.window T₁ T₂ := hs ρ |>.mp hρ
  have hm : 1 ≤ Z.mult ρ := Z.one_le_mult ρ hwin.1
  by_cases hline : ρ.re = (2 : ℝ)⁻¹
  · by_cases hsimple : Z.mult ρ = 1
    · simp [hline, hsimple]
    · have hm2 : 2 ≤ Z.mult ρ := by omega
      rw [if_neg (fun h => hsimple h.2)]
      simp only [hline, ↓reduceIte, zero_add]
      have hsub : 1 ≤ Z.mult ρ - 1 := by omega
      calc
        Z.mult ρ = Z.mult ρ * 1 := (Nat.mul_one _).symm
        _ ≤ Z.mult ρ * (Z.mult ρ - 1) := Nat.mul_le_mul_left _ hsub
  · rw [if_neg (fun h => hline h.1), if_neg hline,
      Z.mult_reflect ρ hwin.1, zero_add]
    calc
      Z.mult ρ = Z.mult ρ * 1 := (Nat.mul_one _).symm
      _ ≤ Z.mult ρ * Z.mult ρ := Nat.mul_le_mul_left _ hm

/-- Subtractive spelling of the preceding finite combinatorial bound. -/
theorem N_sub_N0s_le_Pmate :
    Z.N T₁ T₂ - Z.N0s T₁ T₂ ≤ Z.Pmate T₁ T₂ := by
  have h := Z.N_le_N0s_add_Pmate T₁ T₂
  omega

/-- Reflection-mate energy only counts pairs already present in the full
ordinary-ordinate factorial collision count. -/
theorem Pmate_le_ordinateCollision :
    Z.Pmate T₁ T₂ ≤ Z.ordinateCollision T₁ T₂ := by
  classical
  have hfin := Z.window_finite T₁ T₂
  unfold Pmate ordinateCollision
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hwin : ρ ∈ Z.window T₁ T₂ := hfin.mem_toFinset.mp hρ
  by_cases hline : ρ.re = (2 : ℝ)⁻¹
  · rw [if_pos hline]
    exact Nat.mul_le_mul_left _
      (Nat.sub_le_sub_right (Z.mult_le_ordinateMass T₁ T₂ hwin) 1)
  · rw [if_neg hline, Z.mult_reflect ρ hwin.1]
    have htwo := Z.two_mul_mult_le_ordinateMass T₁ T₂ hwin hline
    have hm := Z.one_le_mult ρ hwin.1
    have hmate : Z.mult ρ ≤ Z.ordinateMass T₁ T₂ ρ.im - 1 := by omega
    exact Nat.mul_le_mul_left _ hmate

/-- The requested mate-energy sandwich, entirely finite and combinatorial. -/
theorem mate_energy_sandwich :
    Z.N T₁ T₂ - Z.N0s T₁ T₂ ≤ Z.Pmate T₁ T₂ ∧
      Z.Pmate T₁ T₂ ≤ Z.ordinateCollision T₁ T₂ :=
  ⟨Z.N_sub_N0s_le_Pmate T₁ T₂, Z.Pmate_le_ordinateCollision T₁ T₂⟩

end Zeta23.ZeroConfig
