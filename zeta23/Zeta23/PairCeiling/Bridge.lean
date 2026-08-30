/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/Bridge.lean — from the GRID certificate (NumericCert: bounds on Dleft/Dright/Egrid/D1/E1 for the form factor S) to the
INTERVAL hypotheses of the stability lemma (Stability/Grid: Dfun/Efun of the atom masses s j := S j / N on [0,1]).
 §1 dictionary: Csum s m = T S m / N; Dfun s N (m/N) = Dright S N m; on the open cell (m/N,(m+1)/N), Dfun = Csum s m − t²/2 lies between
    Dleft S N (m+1) and Dright S N m (D decreases between atoms); Efun s N (m/N) = Egrid S N m.
 §2 sup bridges: grid one-sided bounds ⇒ |Dfun| ≤ B₁ on [0,1]; and |Egrid j| + |D^±_i|/N ≤ B₂ (all i, j) ⇒ |Efun| ≤ B₂ on [0,1]
    (Efun x − Efun(m/N) = ∫_{m/N}^x Dfun, |x − m/N| ≤ 1/N).
 §3 the package for a certificate: EnclOK ⇒ the four hypotheses the ceiling-stability theorem consumes.
-/
import Zeta23.PairCeiling.Grid
import Zeta23.PairCeiling.NumericCert

open scoped BigOperators
open MeasureTheory Set Finset

noncomputable section

namespace Zeta23
namespace PairCeiling

variable {S : ℕ → ℝ} {N : ℕ}

/-! ## §1. Dictionary between the atom masses s = S/N and the form factor S -/

/-- the atom masses of a configuration with form factor S. -/
def massOf (S : ℕ → ℝ) (N : ℕ) : ℕ → ℝ := fun j => S j / N

lemma Csum_massOf (m : ℕ) : Csum (massOf S N) m = T S m / N := by
  induction m with
  | zero => simp [T_zero]
  | succ m ih => rw [Csum_succ, ih, T_succ]; simp [massOf, add_div]

/-- D at a grid point is the right value. -/
lemma Dfun_grid_eq_Dright (hN : 0 < N) {m : ℕ} (hm : m ≤ N) : Dfun (massOf S N) N ((m : ℝ) / N) = Dright S N m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Dfun_grid hN hm, Csum_massOf]
  unfold Dright
  field_simp

/-- on the open cell (m/N, (m+1)/N), D lies between Dleft (m+1) and Dright m. -/
lemma Dfun_cell_bounds (hN : 0 < N) {m : ℕ} (hm : m < N) {t : ℝ} (ht : t ∈ Ioo ((m : ℝ) / N) ((m + 1 : ℝ) / N)) :
    Dleft S N (m + 1) ≤ Dfun (massOf S N) N t ∧ Dfun (massOf S N) N t ≤ Dright S N m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Dfun_eqOn_cell hN hm ht, Csum_massOf]
  unfold Dleft Dright
  simp only [Nat.add_sub_cancel]
  have h1 : (m : ℝ) / N < t := ht.1
  have h2 : t < ((m : ℝ) + 1) / N := ht.2
  have ht0 : 0 ≤ t := le_trans (by positivity) h1.le
  constructor
  · have : t ^ 2 ≤ (((m : ℝ) + 1) / N) ^ 2 := by gcongr
    have e : (((m + 1 : ℕ) : ℝ)) ^ 2 / (2 * (N : ℝ) ^ 2) = ((((m : ℝ) + 1) / N) ^ 2) / 2 := by push_cast; field_simp
    rw [e]; linarith
  · have : ((m : ℝ) / N) ^ 2 ≤ t ^ 2 := by gcongr
    have e : ((m : ℝ)) ^ 2 / (2 * (N : ℝ) ^ 2) = (((m : ℝ) / N) ^ 2) / 2 := by field_simp
    rw [e]; linarith

/-! ## §2. The sup bridges -/

/-- **sup|D| from the grid**: one-sided grid bounds give |D| ≤ B₁ on all of [0,1]. -/
theorem abs_Dfun_le_of_grid (hN : 0 < N) {B₁ : ℝ}
    (hD : ∀ j, 1 ≤ j → j ≤ N → |Dleft S N j| ≤ B₁ ∧ |Dright S N j| ≤ B₁) :
    ∀ t ∈ Icc (0 : ℝ) 1, |Dfun (massOf S N) N t| ≤ B₁ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ B₁ := le_trans (abs_nonneg _) (hD 1 le_rfl hN).1
  intro t ht
  by_cases hg : ∃ m : ℕ, m ≤ N ∧ t = (m : ℝ) / N
  · obtain ⟨m, hm, rfl⟩ := hg
    rw [Dfun_grid_eq_Dright hN hm]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [Dright, T_zero]; exact hB
    · exact (hD m hpos hm).2
  · have ht' : t ∈ Ioo (0 : ℝ) 1 \ grid N := by
      refine ⟨⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, ?_⟩
      · intro h; exact hg ⟨0, Nat.zero_le _, by rw [← h]; simp⟩
      · intro h; exact hg ⟨N, le_rfl, by rw [h, div_self hNr.ne']⟩
      · rintro ⟨m, hmt⟩
        have hmt' : (m : ℝ) / N = t := hmt
        apply hg
        refine ⟨m, ?_, hmt'.symm⟩
        have : (m : ℝ) / N ≤ 1 := hmt' ▸ ht.2
        rw [div_le_one hNr] at this
        exact_mod_cast this
    obtain ⟨m, hm, htm⟩ := exists_cell hN ht'
    obtain ⟨hlo, hhi⟩ := Dfun_cell_bounds hN hm htm
    have h1 := (hD (m + 1) (Nat.succ_pos m) (Nat.succ_le_of_lt hm)).1
    rw [abs_le] at h1 ⊢
    constructor
    · linarith [h1.1]
    · rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        have : Dright S N 0 = 0 := by simp [Dright, T_zero]
        linarith
      · have h2 := (hD m hpos hm.le).2
        rw [abs_le] at h2
        linarith [h2.2]

/-- E at a grid point is Egrid. -/
lemma Efun_grid_eq_Egrid (hN : 0 < N) {m : ℕ} (hm : m ≤ N) : Efun (massOf S N) N ((m : ℝ) / N) = Egrid S N m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Efun_grid hN hm]
  clear hm
  induction m with
  | zero => simp [Egrid, U_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Csum_massOf]
    unfold Egrid
    rw [U_succ]
    push_cast
    field_simp
    ring

/-- **sup|E| from the grid**: the combined grid bounds give |E| ≤ B₂ on all of [0,1]. -/
theorem abs_Efun_le_of_grid (hN : 0 < N) {B₂ : ℝ}
    (hE : ∀ i j, 1 ≤ i → i ≤ N → 1 ≤ j → j ≤ N →
        |Egrid S N j| + |Dleft S N i| / N ≤ B₂ ∧ |Egrid S N j| + |Dright S N i| / N ≤ B₂) :
    ∀ x ∈ Icc (0 : ℝ) 1, |Efun (massOf S N) N x| ≤ B₂ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : 1 ≤ N := hN
  -- B₂ dominates every |D^±_i|/N and every |Egrid j| (the other summand is ≥ 0)
  have hB0 : 0 ≤ B₂ := le_trans (by positivity) (hE 1 1 le_rfl hN1 le_rfl hN1).1
  intro x hx
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · -- x = 1 = N/N
    subst hx1
    rw [show (1 : ℝ) = (N : ℝ) / N from (div_self hNr.ne').symm, Efun_grid_eq_Egrid hN le_rfl]
    have h := (hE N N hN1 le_rfl hN1 le_rfl).1
    linarith [div_nonneg (abs_nonneg (Dleft S N N)) hNr.le]
  · -- x ∈ [m/N, (m+1)/N) with m < N
    set m : ℕ := ⌊(N : ℝ) * x⌋₊ with hm
    have hmx : (m : ℝ) ≤ N * x := Nat.floor_le (by have := hx.1; positivity)
    have hxm : (N : ℝ) * x < m + 1 := Nat.lt_floor_add_one _
    have hmN : m < N := by
      have : (m : ℝ) < N := lt_of_le_of_lt hmx (by nlinarith [hx.1])
      exact_mod_cast this
    have hlo : (m : ℝ) / N ≤ x := by rw [div_le_iff₀ hNr]; linarith
    have hhi : x < ((m : ℝ) + 1) / N := by rw [lt_div_iff₀ hNr]; linarith
    -- split the integral at m/N
    have hI1 : IntervalIntegrable (Dfun (massOf S N) N) volume 0 ((m : ℝ) / N) :=
      (intervalIntegrable_Dfun hN).mono_set (by
        rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by positivity)]
        exact Icc_subset_Icc le_rfl (by rw [div_le_one hNr]; exact_mod_cast hmN.le))
    have hI2 : IntervalIntegrable (Dfun (massOf S N) N) volume ((m : ℝ) / N) x :=
      (intervalIntegrable_Dfun hN).mono_set (by
        rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hlo]
        exact Icc_subset_Icc (by positivity) hx.2)
    have hsplit : Efun (massOf S N) N x = Efun (massOf S N) N ((m : ℝ) / N) + ∫ t in ((m : ℝ) / N)..x, Dfun (massOf S N) N t := by
      unfold Efun; rw [intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    -- on (m/N, x] ⊆ the open cell, |D| ≤ C := max |Dleft (m+1)| |Dright m|
    set C : ℝ := max |Dleft S N (m + 1)| |Dright S N m| with hC
    have hbound : ∀ t ∈ Set.uIoc ((m : ℝ) / N) x, ‖Dfun (massOf S N) N t‖ ≤ C := by
      intro t ht
      rw [Set.uIoc_of_le hlo] at ht
      have ht' : t ∈ Ioo ((m : ℝ) / N) ((m + 1 : ℝ) / N) := ⟨ht.1, lt_of_le_of_lt ht.2 hhi⟩
      obtain ⟨h1, h2⟩ := Dfun_cell_bounds hN hmN ht'
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs h1 h2
    have hint : |∫ t in ((m : ℝ) / N)..x, Dfun (massOf S N) N t| ≤ C / N := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
      rw [Real.norm_eq_abs] at h
      refine h.trans ?_
      have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (le_max_left _ _)
      have : |x - (m : ℝ) / N| ≤ 1 / N := by
        rw [abs_of_nonneg (by linarith)]
        have : ((m : ℝ) + 1) / N = (m : ℝ) / N + 1 / N := by ring
        linarith
      calc C * |x - (m : ℝ) / N| ≤ C * (1 / N) := mul_le_mul_of_nonneg_left this hC0
        _ = C / N := by ring
    rw [hsplit, Efun_grid_eq_Egrid hN hmN.le]
    have htri : |Egrid S N m + ∫ t in ((m : ℝ) / N)..x, Dfun (massOf S N) N t| ≤ |Egrid S N m| + C / N :=
      (abs_add_le _ _).trans (by linarith)
    refine htri.trans ?_
    -- |Egrid m| + C/N ≤ B₂ from the grid hypotheses (m = 0: Egrid 0 = 0 and use j = 1)
    have key : ∀ {Dv : ℝ}, (∀ j, 1 ≤ j → j ≤ N → |Egrid S N j| + |Dv| / N ≤ B₂) → |Egrid S N m| + |Dv| / N ≤ B₂ := by
      intro Dv h
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]; simp only [Egrid, U_zero, Nat.cast_zero, zero_div]
        have := h 1 le_rfl hN1
        norm_num
        linarith [abs_nonneg (Egrid S N 1)]
      · exact h m hpos hmN.le
    rcases le_total |Dleft S N (m + 1)| |Dright S N m| with hle | hle
    · have hCe : C = |Dright S N m| := max_eq_right hle
      rw [hCe]
      refine key fun j hj1 hj2 => ?_
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · -- Dright 0 = 0
        have : Dright S N m = 0 := by rw [h0]; simp [Dright, T_zero]
        rw [this, abs_zero, zero_div, add_zero]
        have := (hE 1 j le_rfl hN1 hj1 hj2).1
        linarith [div_nonneg (abs_nonneg (Dleft S N 1)) hNr.le]
      · exact (hE m j hpos hmN.le hj1 hj2).2
    · have hCe : C = |Dleft S N (m + 1)| := max_eq_left hle
      rw [hCe]
      exact key fun j hj1 hj2 => (hE (m + 1) j (Nat.succ_pos m) (Nat.succ_le_of_lt hmN) hj1 hj2).1

/-! ## §3. The package consumed by the ceiling-stability theorem -/

/-- **from a checked certificate to the interval hypotheses**: for every form factor S inside the enclosures, the atom masses
s := S/N satisfy |D(1)| ≤ bD1, |E(1)| ≤ bE1, |D| ≤ b1 on [0,1], |E| ≤ b2 on [0,1]. -/
theorem package_of_check (d : CertData) (hc : check d = true) (S : ℕ → ℝ) (hS : EnclOK d.K S 0 d.encl) :
    |Dfun (massOf S d.N) d.N 1| ≤ (d.bD1n : ℝ) / d.bD1d ∧ |Efun (massOf S d.N) d.N 1| ≤ (d.bE1n : ℝ) / d.bE1d ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |Dfun (massOf S d.N) d.N t| ≤ (d.b1n : ℝ) / d.b1d) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, |Efun (massOf S d.N) d.N x| ≤ (d.b2n : ℝ) / d.b2d) := by
  obtain ⟨hD1, hE1, hD, hE⟩ := cert_of_check d hc S hS
  have hN : 0 < d.N := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.1.1.1.1.1.1.1.2
  have hNr : (0 : ℝ) < d.N := by exact_mod_cast hN
  have h1 : (1 : ℝ) = (d.N : ℝ) / d.N := (div_self hNr.ne').symm
  refine ⟨?_, ?_, abs_Dfun_le_of_grid hN hD, abs_Efun_le_of_grid hN hE⟩
  · rw [h1, Dfun_grid_eq_Dright hN le_rfl]; exact hD1
  · rw [h1, Efun_grid_eq_Egrid hN le_rfl]; exact hE1

end PairCeiling
end Zeta23

end
