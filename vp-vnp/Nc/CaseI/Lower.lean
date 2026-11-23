/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.CaseI.Fkl
import Nc.CaseI.Geo
import Nc.Price.Network
import Nc.Price.Basic

/-!
# The complete network: ends, sums over the ends, and the numbers of the lower bound
-/

namespace Nc.CaseI

open Finset Nc.Price Ov

variable {k : ℕ}

/-- The ends of all pairs. -/
abbrev End (k : ℕ) := Σ _ : Pr k, Fin 2

/-- The parties: the ends, and two hubs for every set. -/
abbrev RPt (k : ℕ) := End k ⊕ (Finset (Fin k) × Bool)

/-- The node of an end. -/
def endNode (e : Pr k) (i : Fin 2) : Fin k := if i = 0 then e.1.1 else e.1.2

/-- Sums over ends and over pairs. -/
theorem sum_pairs (G : Fin k → Fin k → ℝ) :
    ∑ e : Pr k, (G e.1.1 e.1.2 + G e.1.2 e.1.1) = ∑ a, ∑ b, if a = b then 0 else G a b := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if a = b then (0 : ℝ) else G a b),
    Finset.sum_add_distrib,
    ← Finset.sum_subtype (univ.filter fun e : Fin k × Fin k => e.1 < e.2) (by simp)
      (fun e : Fin k × Fin k => G e.1 e.2),
    ← Finset.sum_subtype (univ.filter fun e : Fin k × Fin k => e.1 < e.2) (by simp)
      (fun e : Fin k × Fin k => G e.2 e.1), Finset.sum_filter, Finset.sum_filter]
  have h2 : ∑ e : Fin k × Fin k, (if e.1 < e.2 then G e.2 e.1 else 0) =
      ∑ e : Fin k × Fin k, if e.2 < e.1 then G e.1 e.2 else 0 :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun e => rfl
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases lt_trichotomy e.1 e.2 with h | h | h
  · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne, add_zero]
  · rw [if_neg (not_lt.2 h.ge), if_neg (not_lt.2 h.le), if_pos h, add_zero]
  · rw [if_neg (not_lt.2 h.le), if_pos h, if_neg h.ne', zero_add]

theorem sum_pairs_one : ∑ _e : Pr k, (1 : ℝ) = k * (k - 1) / 2 := by
  have h := sum_pairs (k := k) fun _ _ => 1 / 2
  have h1 : ∀ e : Pr k, ((1 : ℝ) / 2 + 1 / 2) = 1 := fun _ => by norm_num
  rw [Finset.sum_congr rfl fun e _ => h1 e] at h
  rw [h]
  have h2 : ∀ a : Fin k, ∑ b : Fin k, (if a = b then (0 : ℝ) else 1 / 2) = (k - 1) / 2 := by
    intro a
    have h3 : ∀ b : Fin k, (if a = b then (0 : ℝ) else 1 / 2) = 1 / 2 - if a = b then 1 / 2 else 0 := by
      intro b
      split_ifs <;> ring
    simp only [h3]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h2]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The numbers of the lower bound. -/
theorem lower_numbers {k ℓ c N δ S1 S2 S3 lg : ℝ} (hk1 : 1 ≤ k) (hℓ0 : 0 ≤ ℓ) (hc : 0 ≤ c)
    (hN : N = k * (k - 1) / 2) (hδ : δ = 1 / (150 * k)) (hlog : 0 ≤ lg) (hℓc : 100 * c ≤ ℓ)
    (hw : N * (1 - δ) ≤ c * S1) (hh : c * S2 ≤ N - k / 12 + 2 * N * δ)
    (hm : c * S3 ≤ 1 / (3 * √k) + δ) (h1 : ℓ * S1 ≤ k + ℓ * S2 + S3 * lg) :
    ℓ * (k * √k) / 6 ≤ lg := by
  have hk0 : 0 < k := by linarith
  have hN0 : 0 ≤ N := by
    have : (0 : ℝ) ≤ k - 1 := by linarith
    rw [hN]
    positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have h3 : ℓ * (N * (1 - δ)) ≤ c * k + ℓ * (N - k / 12 + 2 * N * δ) + (1 / (3 * √k) + δ) * lg := by
    have h2 := mul_le_mul_of_nonneg_left h1 hc
    have a1 := mul_le_mul_of_nonneg_left hw hℓ0
    have a2 := mul_le_mul_of_nonneg_left hh hℓ0
    have a3 := mul_le_mul_of_nonneg_right hm hlog
    have e1 : c * (ℓ * S1) = ℓ * (c * S1) := by ring
    have e2 : c * (k + ℓ * S2 + S3 * lg) = c * k + ℓ * (c * S2) + c * S3 * lg := by ring
    rw [e1, e2] at h2
    linarith
  have hNδ : 3 * N * δ ≤ k / 100 := by
    have : N ≤ k * k / 2 := by rw [hN]; nlinarith
    have h4 : 3 * N * δ ≤ 3 * (k * k / 2) * δ := by gcongr
    refine h4.trans (le_of_eq ?_)
    rw [hδ]
    field_simp
    norm_num
  have hck : c * k ≤ ℓ * (k / 100) := by nlinarith
  have h5 : ℓ * (k * (19 / 300)) ≤ (1 / (3 * √k) + δ) * lg := by
    have h6 : ℓ * (3 * N * δ) ≤ ℓ * (k / 100) := mul_le_mul_of_nonneg_left hNδ hℓ0
    have e3 : ℓ * (N * (1 - δ)) = ℓ * N - ℓ * (N * δ) := by ring
    have e4 : ℓ * (N - k / 12 + 2 * N * δ) = ℓ * N - ℓ * k / 12 + 2 * (ℓ * (N * δ)) := by ring
    have e5 : ℓ * (3 * N * δ) = 3 * (ℓ * (N * δ)) := by ring
    rw [e3, e4] at h3
    rw [e5] at h6
    linarith
  have hsq : √k * √k = k := Real.mul_self_sqrt hk0.le
  have hsq1 : 1 ≤ √k := by
    rw [Real.one_le_sqrt]
    exact hk1
  have hsq0 : 0 < √k := by linarith
  have h7 : 1 / (3 * √k) + δ ≤ (17 / 50) / √k := by
    have h8 : δ ≤ 1 / (150 * √k) := by
      rw [hδ]
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith
    have h9 : (1 : ℝ) / (3 * √k) + 1 / (150 * √k) = (17 / 50) / √k := by
      field_simp
      norm_num
    linarith
  have h10 : ℓ * (k * (19 / 300)) ≤ (17 / 50) / √k * lg :=
    h5.trans (mul_le_mul_of_nonneg_right h7 hlog)
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq0] at h10
  have h11 : (0 : ℝ) ≤ ℓ * (k * √k) := by positivity
  have e6 : ℓ * (k * (19 / 300)) * √k = 19 / 300 * (ℓ * (k * √k)) := by ring
  rw [e6] at h10
  linarith

/-- Sums over ends, with an error. -/
theorem sum_pairs_add (G : Fin k → Fin k → ℝ) (δ : ℝ) :
    ∑ e : Pr k, ((G e.1.1 e.1.2 + δ) + (G e.1.2 e.1.1 + δ)) =
      (∑ a, ∑ b, if a = b then 0 else G a b) + 2 * ((k : ℝ) * (k - 1) / 2) * δ := by
  have h1 : ∀ e : Pr k, ((G e.1.1 e.1.2 + δ) + (G e.1.2 e.1.1 + δ)) =
      (G e.1.1 e.1.2 + G e.1.2 e.1.1) + 1 * (2 * δ) := fun e => by ring
  rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_add_distrib, sum_pairs, ← Finset.sum_mul,
    sum_pairs_one]
  ring

end Nc.CaseI
