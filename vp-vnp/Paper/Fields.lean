/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Rate
import Paper.HcGrid
import Paper.Transfer
import Nc.Hc.Vnp

/-!
# The paper, appendix "All fields and the Hamiltonian cycle polynomial"
-/

namespace Paper

open Finset MvPolynomial Nc

universe u

theorem map_genHC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (genHC R m) = genHC S m := by
  simp only [genHC, map_sum, map_prod, map_X]

/-- The permanent with integer coefficients. -/
noncomputable def permInt (m : ℕ) : MvPolynomial (Fin m × Fin m) ℤ :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i, X (σ i, i)

theorem map_permInt (F : Type u) [Field F] (m : ℕ) :
    MvPolynomial.map (Int.castRingHom F) (permInt m) = genPerm F m := by
  simp only [permInt, genPerm, Matrix.permanent, Matrix.of_apply, map_sum, map_prod, map_X]

/-- KK, "the algebraic closure of the prime field of characteristic p". -/
theorem exists_closed (p : ℕ) (hp : p = 0 ∨ p.Prime) : ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ CharP K p := by
  rcases hp with rfl | hp
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, inferInstance⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩

/-- 2 is not 0 in characteristic other than 2. -/
theorem two_ne_zero_of_char (K : Type) [Field K] (p : ℕ) [CharP K p] (hp : p = 0 ∨ p.Prime) (h2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h3
  rcases hp with rfl | hp
  · simp at h3
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

/-- The flat case for HC, in every characteristic. -/
theorem flat_rate_hc {K : Type} [Field K] (hK : Flat K) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Computes (genHC K m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := flat_rate_complete 40
  exact ⟨m₀, h K hK _ (gridComplete_hc K)⟩

/-- The contracting case for HC, in every characteristic. -/
theorem contracting_hc {K : Type} [Field K] (hK : Contracting K) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Computes (genHC K m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨C, M₁, h⟩ := contracting_complete hK (gridComplete_hc K)
  exact quasi_of_exponents (P := fun M s => Computes (genHC K M) s) (fun _ _ _ hst hs => Computes.mono hs hst) h

/-- "The bound of the contracting case, although its constant depends on p, exceeds that of the flat case for large m." -/
theorem thm_allfields_exceeds {P : ℕ → ℕ → Prop}
    (h : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨c, hc, m₁, h⟩ := h
  obtain ⟨m₂, hm₂⟩ := thm_main_calculation (1 / (c * 1600 ^ 2))
  refine ⟨m₁ + m₂, fun m hm s hs => lt_of_le_of_lt ?_ (h m (by omega) s hs)⟩
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (hm₂ m (by omega)) hc.le).trans_eq (mul_div_assoc _ _ _).symm)
  field_simp

/-- The bound 2^((log m)^(4/3)/1600²) in the form of the main theorems. -/
theorem beyond_of_rate {m s : ℕ} (hm : 2 ≤ m) (h : (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) :
    (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  rwa [thm_main_form hm, one_div_mul_eq_div]

/-- **Paper: Theorem thm:allfields.** "There is an absolute constant c > 0 such that for every p, zero or prime,
there is m₀: over every field of characteristic p and for every m ≥ m₀ every circuit for HC_m, and for PERM_m if p ≠ 2,
has more than m^(c(log m)^(1/3)) gates." -/
theorem thm_allfields : ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ,
    ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Computes (genHC F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Computes (genPerm F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
  refine ⟨1 / 1600 ^ 2, by norm_num, fun p hp => ?_⟩
  obtain ⟨K, _, _, _⟩ := exists_closed p hp
  obtain ⟨M₁, h1⟩ : ∃ M₁ : ℕ, ∀ m ≥ M₁, ∀ s, Computes (genHC K m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    rcases thm_alt K with hK | hK
    · exact flat_rate_hc hK
    · exact thm_allfields_exceeds (contracting_hc hK)
  obtain ⟨M₂, h2⟩ : ∃ M₂ : ℕ, p ≠ 2 → ∀ m ≥ M₂, ∀ s, Computes (genPerm K m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    by_cases hne : p = 2
    · exact ⟨0, fun h => absurd hne h⟩
    · have h2 := two_ne_zero_of_char K p hp hne
      obtain ⟨M₂, h⟩ := (thm_alt K).elim (fun hK => thm_flat_rate hK h2)
        fun hK => thm_allfields_exceeds (thm_contracting hK h2)
      exact ⟨M₂, fun _ => h⟩
  refine ⟨M₁ + M₂ + 2, fun F _ _ m hm s => ⟨fun hs => ?_, fun hne hs => ?_⟩⟩
  · rw [← map_genHC (Int.castRingHom F)] at hs
    have h := lem_transfer (KK := K) p (genHC ℤ m) hs
    rw [map_genHC] at h
    exact beyond_of_rate (by omega) (h1 m (by omega) s h)
  · rw [← map_permInt] at hs
    have h := lem_transfer (KK := K) p (permInt m) hs
    rw [map_permInt] at h
    exact beyond_of_rate (by omega) (h2 hne m (by omega) s h)

/-- A bound m^(c(log m)^(1/3)) is beyond every polynomial. -/
theorem exists_beyond_poly {c : ℝ} (hc : 0 < c) (m₀ C : ℕ) :
    ∃ m ≥ m₀, ¬ (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < ((m ^ C + C : ℕ) : ℝ) := by
  have ht : Filter.Tendsto (fun m : ℕ => c * Real.logb 2 m ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp
      ((Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  obtain ⟨m, hm1, hm2⟩ := ((Filter.eventually_ge_atTop (m₀ + C + 2)).and
    (ht.eventually_ge_atTop ((C + 1 : ℕ) : ℝ))).exists
  refine ⟨m, by omega, fun hb => ?_⟩
  have h3 : (m : ℝ) ^ ((C + 1 : ℕ) : ℝ) < ((m ^ C + C : ℕ) : ℝ) :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m)) hm2) hb
  rw [Real.rpow_natCast] at h3
  have h4 : m ^ (C + 1) < m ^ C + C := by exact_mod_cast h3
  have h5 : 1 ≤ m ^ C := Nat.one_le_pow _ _ (by omega)
  have h6 : m ^ C * (C + 1) ≤ m ^ C * m := Nat.mul_le_mul_left _ (by omega)
  rw [pow_succ] at h4
  nlinarith

/-- "(HC_m) is in VNP." -/
theorem hc_mem_VNP (F : Type u) [Field F] :
    ({ X := fun n => Fin n × Fin n, poly := genHC F } : Family F) ∈ VNP F := by
  refine ⟨fun n => n * n, Hc.hcWit F, ⟨700, fun n => ?_⟩, Hc.genHC_eq_sum_wit F⟩
  have hb := Hc.quartic_bound n (C := 700) le_rfl
  obtain ⟨h1, h2⟩ := Hc.csize_hcWit F n
  refine ⟨le_trans ?_ hb, h2.trans hb, h1.mono hb⟩
  show Fintype.card ((Fin n × Fin n) ⊕ Fin (n * n)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

/-- **Paper: Corollary cor:allclasses.** "Over every field, VP is a proper subset of VNP." -/
theorem cor_allclasses (F : Type u) [Field F] : VP F ⊂ VNP F := by
  refine ⟨vp_subset_vnp F, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h (hc_mem_VNP F)
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨c, hc, hall⟩ := thm_allfields.{u}
  obtain ⟨m₀, hlow⟩ := hall p (CharP.char_is_prime_or_zero F p).symm
  obtain ⟨m, hm1, hm2⟩ := exists_beyond_poly hc m₀ C
  exact hm2 ((hlow F m hm1 _).1 (hC m).2.2)

end Paper
