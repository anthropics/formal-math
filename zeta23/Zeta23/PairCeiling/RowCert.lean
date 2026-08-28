/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/RowCert.lean — an integer certificate format for NEAR-CUE grid laws (NearCUE.lean): from kernel-checkable enclosures
lo_j ≤ K·S(j) ≤ hi_j (j = 1..N, scale K) the checker verifies |N·S(j) − j| ≤ τ for 0 < j < N and |D(1)| = |T_N/N − 1/2| ≤ d₁ with
rational τ = tn/td, d₁ = dn/dd, by pure integer arithmetic; the soundness theorem turns an accepted certificate plus the displayed
hypothesis EnclOK (that the true S lies in the enclosures) into the hypotheses of ceiling_nearCUE.
-/
import Zeta23.PairCeiling.NearCUE
import Zeta23.PairCeiling.NumericCert

open scoped BigOperators
open MeasureTheory Set Finset

noncomputable section

namespace Zeta23
namespace PairCeiling

/-- certificate data: N, scale K, enclosures for j = 1..N, τ = tn/td, d₁ = dn/dd. -/
structure RowCertData where
  N : ℕ
  K : ℕ
  encl : List (ℤ × ℤ)
  tn : ℕ
  td : ℕ
  dn : ℕ
  dd : ℕ

/-- the row checks: the enclosure of row j+1 lies within τ of j+1 whenever j+1 < N. -/
def rowsOK (N K tn td : ℕ) : ℕ → List (ℤ × ℤ) → Bool
  | _, [] => true
  | j, e :: l =>
      (decide (N ≤ j + 1) ||
        (decide (|(N : ℤ) * e.1 - ((j : ℤ) + 1) * K| * td ≤ tn * K) &&
         decide (|(N : ℤ) * e.2 - ((j : ℤ) + 1) * K| * td ≤ tn * K)))
      && rowsOK N K tn td (j + 1) l

/-- sums of the lower / upper enclosure ends. -/
def sumLo : List (ℤ × ℤ) → ℤ
  | [] => 0
  | e :: l => e.1 + sumLo l

def sumHi : List (ℤ × ℤ) → ℤ
  | [] => 0
  | e :: l => e.2 + sumHi l

/-- **the checker** (pure integer arithmetic). -/
def checkRows (d : RowCertData) : Bool :=
  decide (0 < d.N) && decide (0 < d.K) && decide (0 < d.td) && decide (0 < d.dd) && decide (d.encl.length = d.N)
    && rowsOK d.N d.K d.tn d.td 0 d.encl
    && decide (|2 * sumLo d.encl - (d.K : ℤ) * d.N| * d.dd ≤ d.dn * (2 * (d.K : ℤ) * d.N))
    && decide (|2 * sumHi d.encl - (d.K : ℤ) * d.N| * d.dd ≤ d.dn * (2 * (d.K : ℤ) * d.N))

/-! ## Soundness -/

section Sound

variable {S : ℕ → ℝ}

/-- the row checks give the near-CUE hypothesis on the covered range. -/
lemma rows_sound {N K tn td : ℕ} (hK : 0 < K) (htd : 0 < td) :
    ∀ (l : List (ℤ × ℤ)) (j : ℕ), rowsOK N K tn td j l = true → EnclOK K S j l →
      ∀ j' : ℕ, j < j' → j' ≤ j + l.length → j' < N → |(N : ℝ) * S j' - j'| ≤ (tn : ℝ) / td := by
  intro l
  induction l with
  | nil => intro j _ _ j' h1 h2 _; simp at h2; omega
  | cons e l ih =>
    intro j hok hE j' h1 h2 h3
    simp only [rowsOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hhead, htail⟩ := hok
    obtain ⟨⟨he1, he2⟩, hE'⟩ := hE
    rcases Nat.lt_or_ge (j + 1) j' with hlt | hge
    · exact ih (j + 1) htail hE' j' hlt (by simp at h2 ⊢; omega) h3
    · -- j' = j + 1
      have hj' : j' = j + 1 := by omega
      subst hj'
      rcases hhead with hbad | ⟨hlo, hhi⟩
      · omega
      · have hKr : (0 : ℝ) < K := by exact_mod_cast hK
        have htdr : (0 : ℝ) < td := by exact_mod_cast htd
        -- cast the integer facts
        have hlo' : |(N : ℝ) * (e.1 : ℝ) - ((j : ℝ) + 1) * K| * td ≤ tn * K := by exact_mod_cast hlo
        have hhi' : |(N : ℝ) * (e.2 : ℝ) - ((j : ℝ) + 1) * K| * td ≤ tn * K := by exact_mod_cast hhi
        rw [abs_le]
        rw [← le_div_iff₀ htdr] at hlo' hhi'
        rw [abs_le] at hlo' hhi'
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        push_cast
        constructor
        · -- lower: N·S ≥ N·e1/K
          have : (N : ℝ) * (e.1 : ℝ) ≤ (N : ℝ) * (K * S (j + 1)) := mul_le_mul_of_nonneg_left he1 hN0
          have h2' : ((N : ℝ) * e.1 - ((j : ℝ) + 1) * K) / K ≤ (N : ℝ) * S (j + 1) - ((j : ℝ) + 1) := by
            rw [div_le_iff₀ hKr]; nlinarith
          have h3' : -((tn : ℝ) / td) ≤ ((N : ℝ) * e.1 - ((j : ℝ) + 1) * K) / K := by
            rw [le_div_iff₀ hKr]; have := hlo'.1
            have e0 : -(↑tn * ↑K / ↑td) = -(↑tn / ↑td) * (K:ℝ) := by ring
            linarith [e0]
          linarith
        · have : (N : ℝ) * (K * S (j + 1)) ≤ (N : ℝ) * (e.2 : ℝ) := mul_le_mul_of_nonneg_left he2 hN0
          have h2' : (N : ℝ) * S (j + 1) - ((j : ℝ) + 1) ≤ ((N : ℝ) * e.2 - ((j : ℝ) + 1) * K) / K := by
            rw [le_div_iff₀ hKr]; nlinarith
          have h3' : ((N : ℝ) * e.2 - ((j : ℝ) + 1) * K) / K ≤ (tn : ℝ) / td := by
            rw [div_le_iff₀ hKr]; have := hhi'.2
            have e0 : (↑tn * ↑K / ↑td) = (↑tn / ↑td) * (K:ℝ) := by ring
            linarith [e0]
          linarith

/-- the enclosure sums enclose K·(S(j+1) + … + S(j+|l|)). -/
lemma sums_sound {K : ℕ} :
    ∀ (l : List (ℤ × ℤ)) (j : ℕ), EnclOK K S j l →
      (sumLo l : ℝ) ≤ K * ∑ i ∈ Finset.range l.length, S (j + i + 1) ∧
      (K : ℝ) * ∑ i ∈ Finset.range l.length, S (j + i + 1) ≤ (sumHi l : ℝ) := by
  intro l
  induction l with
  | nil => intro j _; simp [sumLo, sumHi]
  | cons e l ih =>
    intro j hE
    obtain ⟨⟨he1, he2⟩, hE'⟩ := hE
    obtain ⟨ih1, ih2⟩ := ih (j + 1) hE'
    simp only [sumLo, sumHi, List.length_cons, Int.cast_add]
    rw [Finset.sum_range_succ', Finset.mul_sum] at *
    simp only [add_zero] at *
    have e : ∀ i, j + (i + 1) + 1 = j + 1 + i + 1 := fun i => by ring
    simp only [e]
    rw [← Finset.mul_sum] at ih1 ih2
    rw [mul_add]
    constructor <;> linarith

/-- **soundness of the row checker.** -/
theorem cert_of_checkRows (d : RowCertData) (hc : checkRows d = true) (S : ℕ → ℝ) (hS : EnclOK d.K S 0 d.encl) :
    0 < d.N ∧ NearCUE S d.N ((d.tn : ℝ) / d.td) ∧ |Dfun (massOf S d.N) d.N 1| ≤ (d.dn : ℝ) / d.dd := by
  simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hN, hK⟩, htd⟩, hdd⟩, hlen⟩, hrows⟩, hD1lo⟩, hD1hi⟩ := hc
  refine ⟨hN, ?_, ?_⟩
  · intro j hj1 hjN
    exact rows_sound hK htd d.encl 0 hrows hS j (by omega) (by rw [hlen]; omega) hjN
  · have hNr : (0 : ℝ) < d.N := by exact_mod_cast hN
    have hKr : (0 : ℝ) < d.K := by exact_mod_cast hK
    have hddr : (0 : ℝ) < d.dd := by exact_mod_cast hdd
    obtain ⟨hlo, hhi⟩ := sums_sound d.encl 0 hS
    rw [hlen] at hlo hhi
    have eT : ∑ i ∈ Finset.range d.N, S (0 + i + 1) = T S d.N := by simp [T]
    rw [eT] at hlo hhi
    rw [Dfun_one hN, Csum_massOf]
    have hD1lo' : |2 * (sumLo d.encl : ℝ) - (d.K : ℝ) * d.N| * d.dd ≤ d.dn * (2 * (d.K : ℝ) * d.N) := by exact_mod_cast hD1lo
    have hD1hi' : |2 * (sumHi d.encl : ℝ) - (d.K : ℝ) * d.N| * d.dd ≤ d.dn * (2 * (d.K : ℝ) * d.N) := by exact_mod_cast hD1hi
    have e1 : T S d.N / d.N - 1 / 2 = (2 * (d.K : ℝ) * T S d.N - d.K * d.N) / (2 * (d.K : ℝ) * d.N) := by
      field_simp
    rw [e1, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * (d.K : ℝ) * d.N), div_le_div_iff₀ (by positivity) hddr]
    have hm : |2 * (d.K : ℝ) * T S d.N - d.K * d.N|
        ≤ max |2 * (sumLo d.encl : ℝ) - (d.K : ℝ) * d.N| |2 * (sumHi d.encl : ℝ) - (d.K : ℝ) * d.N| :=
      abs_le_max_abs_abs (by linarith) (by linarith)
    calc |2 * (d.K : ℝ) * T S d.N - d.K * d.N| * d.dd
        ≤ max |2 * (sumLo d.encl : ℝ) - (d.K : ℝ) * d.N| |2 * (sumHi d.encl : ℝ) - (d.K : ℝ) * d.N| * d.dd := by gcongr
      _ ≤ d.dn * (2 * (d.K : ℝ) * d.N) := by
          rw [max_mul_of_nonneg _ _ hddr.le]; exact max_le hD1lo' hD1hi'

end Sound

end PairCeiling
end Zeta23

end
