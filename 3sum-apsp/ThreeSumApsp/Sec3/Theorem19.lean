/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem17.Witnesses
public import ThreeSumApsp.Sec3.Theorem19.Choice

/-!
# Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3)

Theorem 19 applies the reduction of Theorem 17 with `D` about `n^{1/18}` and `g = ⌈D^η⌉`, and solves
each instance by a corollary of Section 3.1: by Corollary 15 with `η = 1/36`, where `D` is the
largest power of four with `D ≤ n^{1/18}`, and by Corollary 16 with `η = 0.0315`, where
`D = ⌊n^{1/18}⌋`.  This file has the arithmetic of the proof.  The deduction of the running time
from Theorem 17 that uses it is `Theorem19.explicit_of_theorem_17_corollary_15` and
`Theorem19.explicit_of_theorem_17_corollary_16`, and the theorem about programs is
`wordRam_theorem_19`.

1. Both choices of the parameters, `paramD₅` with `paramG₅` and `paramD₂₆` with `paramG₂₆`, are a
   `Theorem19.Choice` (`Theorem19.choice_theorem_5`, `Theorem19.choice_corollary_26`).  So they
   satisfy the hypotheses of Theorem 17 and of the two corollaries (`Choice.sixteen_le`,
   `Choice.le_n`, `Choice.one_le_ceil`, `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. By the cost analysis for a general choice (`Theorem19.exists_total_le`), the number of instances
   times the cost of one instance, plus the additional time of Theorem 17, is
   `O(n^{3-1/648} log² n)`, respectively `O(n^{3-0.00175} log n)` (`Theorem19.total_theorem_5`,
   `Theorem19.total_corollary_26`).  The step "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})" of the
   statement is the general fact that a larger exponent absorbs logarithms
   (`IsPowPolylog.isBigOPow`); it is applied in `Theorem19.second_of_explicit`.

NOTE.  "Assume n is larger than a constant depending on ν": the two choices of `D` below are stated
for `n ≥ 16^18`, which makes `D ≥ 16`.

Remark 20 explains the values of `η`: the exponents `η - γ` of the instances and `-η` of the scans
balance at `η = γ/2` (`remark_20_balance`, `remark_20_numbers`), and the straightforward algorithm
for the instances gives back the bound `n³` (`remark_20_brute_force`).
-/

public section

namespace ThreeSumApsp

/-! ### The two choices of the parameters -/

/-- `paramD₅ n` is what the proof of Theorem 19 asks for: "the largest power of four with
D ≤ n^{1/18}". -/
theorem paramD₅_largest_pow_four (n : ℕ) (hn : 1 ≤ n) :
    (∃ k : ℕ, paramD₅ n = 4 ^ k) ∧ (paramD₅ n : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) ∧
    ∀ k : ℕ, ((4 : ℝ) ^ k) ≤ (n : ℝ) ^ (1 / 18 : ℝ) → 4 ^ k ≤ paramD₅ n := by
  have hroot : 1 ≤ (n : ℝ) ^ (1 / 18 : ℝ) := Real.one_le_rpow (Nat.one_le_cast.2 hn) (by norm_num)
  have hfloor : ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊ ≠ 0 :=
    Nat.one_le_iff_ne_zero.1 (Nat.le_floor (by simpa only [Nat.cast_one] using hroot))
  refine ⟨⟨_, rfl⟩, ?_, fun k hk => ?_⟩
  · exact (Nat.cast_le.2 (Nat.pow_log_le_self 4 hfloor)).trans
      (Nat.floor_le (zero_le_one.trans hroot))
  · exact Nat.pow_le_pow_right (by norm_num)
      (Nat.le_log_of_pow_le (by norm_num) (Nat.le_floor (by push_cast; exact hk)))

/-- The largest power of four with `D ≤ n^{1/18}` is at least 16 and at least `n^{1/18}/4`. -/
theorem Theorem19.Choice.of_largest_pow_four {n D : ℕ} (hn : 16 ^ 18 ≤ n) (hD4 : ∃ k : ℕ, D = 4 ^ k)
    (hDle : (D : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ))
    (hDmax : ∀ k : ℕ, ((4 : ℝ) ^ k) ≤ (n : ℝ) ^ (1 / 18 : ℝ) → 4 ^ k ≤ D) :
    Theorem19.Choice n D (1 / 36) 4 where
  -- `16 = 4²` is a power of four that is at most `n^{1/18}`.
  sixteen_le := hDmax 2 (by norm_num; exact Theorem19.sixteen_le_root hn)
  le_root := hDle
  root_div_le := by
    -- Otherwise `4D` would be a larger power of four that is at most `n^{1/18}`.
    obtain ⟨k, rfl⟩ := hD4
    by_contra hlt
    have hquarter : (4 : ℝ) ^ k < (n : ℝ) ^ (1 / 18 : ℝ) / 4 := by exact_mod_cast not_le.mp hlt
    have hnext : (4 : ℝ) ^ (k + 1) ≤ (n : ℝ) ^ (1 / 18 : ℝ) := by
      rw [pow_succ]
      linarith [hquarter]
    exact absurd (hDmax (k + 1) hnext) (Nat.pow_lt_pow_right (by norm_num) k.lt_succ_self).not_ge
  c_pos := by norm_num
  η_nonneg := by norm_num
  η_le := by norm_num

/-- Proof of Theorem 19, by Theorem 5: "Let D be the largest power of four with D ≤
n^{1/18}, so that D ≥ n^{1/18}/4, and let g := ⌈D^{1/36}⌉." -/
theorem Theorem19.choice_theorem_5 {n : ℕ} (hn : 16 ^ 18 ≤ n) :
    Theorem19.Choice n (paramD₅ n) (1 / 36) 4 :=
  have ⟨hD4, hDle, hDmax⟩ := paramD₅_largest_pow_four n (le_trans (by norm_num) hn)
  Theorem19.Choice.of_largest_pow_four hn hD4 hDle hDmax

/-- Proof of Theorem 19, by Corollary 26: "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉", and
"D ≥ n^{1/18}/2". -/
theorem Theorem19.choice_corollary_26 {n : ℕ} (hn : 16 ^ 18 ≤ n) :
    Theorem19.Choice n (paramD₂₆ n) 0.0315 2 where
  sixteen_le := Nat.le_floor (by exact_mod_cast Theorem19.sixteen_le_root hn)
  le_root := Nat.floor_le (by positivity)
  root_div_le := by
    -- With `r = n^{1/18} ≥ 16`: `D > r - 1 ≥ r/2`.
    have hlt : (n : ℝ) ^ (1 / 18 : ℝ) < (paramD₂₆ n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith [Theorem19.sixteen_le_root hn, hlt]
  c_pos := by norm_num
  η_nonneg := by norm_num
  η_le := by norm_num

/-! ### The costs added up -/

/-- **Theorem 19, first bound**, the costs added up: "so the time is
O(n^{3−1/648} log² n)".  The left side is the bound of Theorem 17 at `D = paramD₅ n` and
`g = paramG₅ n`: the number of instances times the bound of Corollary 15 for one instance, plus the
three terms of the additional time (with Strassen's exponent).  `a` and `b` stand for the constants
hidden in the two `O(·)`, and `κ` is the exponent in the bound on the weights, the paper's ν. -/
theorem Theorem19.total_theorem_5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 16 ^ 18 ≤ n → ∀ {a b κ : ℝ}, 0 ≤ a → 0 ≤ b → 1 ≤ κ →
      4 * (n : ℝ) * (paramG₅ n : ℝ)
          * (a * ((n : ℝ) ^ 2 * Real.log (paramD₅ n) ^ 2 / (paramD₅ n : ℝ) ^ (1 / 18 : ℝ)))
        + b * (termScans n (paramG₅ n) κ + termPrime strassen n (paramD₅ n)
          + termBuild n (paramD₅ n) (paramG₅ n))
        ≤ C * ((a + b) * (κ * ((n : ℝ) ^ (3 - 1 / 648 : ℝ) * Real.log n ^ 2))) := by
  obtain ⟨C, hC, htotal⟩ := Theorem19.exists_total_le (c := 4) (by norm_num) (1 / 36)
  refine ⟨C, hC, fun {n} hn {a b κ} ha hb hκ => ?_⟩
  have P := Theorem19.choice_theorem_5 hn
  -- The logarithmic factors `log² D` and `log n` are at most `log² n`.
  have h := htotal P ha hb hκ (sq_nonneg (Real.log (paramD₅ n)))
    (pow_le_pow_left₀ (Real.log_natCast_nonneg _) P.log_le_log 2)
    (le_self_pow₀ P.one_le_log two_ne_zero)
  rwa [show (2 * (1 / 36) : ℝ) = 1 / 18 by norm_num,
    show (3 - 1 / 36 / 18 : ℝ) = 3 - 1 / 648 by norm_num] at h

/-- **Theorem 19, second bound**, the costs added up: "so the time is O(n^{3−ε'} log n)",
`ε' = 0.00175`.  The letters are as in `Theorem19.total_theorem_5`, with Corollary 16 in place of
Corollary 15. -/
theorem Theorem19.total_corollary_26 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 16 ^ 18 ≤ n → ∀ {a b κ : ℝ}, 0 ≤ a → 0 ≤ b → 1 ≤ κ →
      4 * (n : ℝ) * (paramG₂₆ n : ℝ) * (a * ((n : ℝ) ^ 2 / (paramD₂₆ n : ℝ) ^ (0.063 : ℝ)))
        + b * (termScans n (paramG₂₆ n) κ + termPrime strassen n (paramD₂₆ n)
          + termBuild n (paramD₂₆ n) (paramG₂₆ n))
        ≤ C * ((a + b) * (κ * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n))) := by
  obtain ⟨C, hC, htotal⟩ := Theorem19.exists_total_le (c := 2) (by norm_num) 0.0315
  refine ⟨C, hC, fun {n} hn {a b κ} ha hb hκ => ?_⟩
  have P := Theorem19.choice_corollary_26 hn
  -- The cost of one instance has no logarithmic factor: `X = 1 ≤ log n`.
  have h := htotal P ha hb hκ zero_le_one P.one_le_log le_rfl
  rwa [mul_one, show (2 * 0.0315 : ℝ) = 0.063 by norm_num,
    show (3 - 0.0315 / 18 : ℝ) = 3 - 0.00175 by norm_num] at h

/-! ### Remark 20 -/

/-- **Remark 20**: "With g = D^η and a saving D^γ per instance, the instances cost n³
D^{η−γ} and the scans n³ D^{−η} [...].  They balance at η = γ/2": the larger of the two exponents
`η − γ` and `−η` is smallest, namely `−γ/2`, exactly at `η = γ/2`. -/
theorem remark_20_balance (γ η : ℝ) :
    -(γ / 2) ≤ max (η - γ) (-η) ∧ (max (η - γ) (-η) = -(γ / 2) ↔ η = γ / 2) := by
  have hinstances : η - γ ≤ max (η - γ) (-η) := le_max_left _ _
  have hscans : -η ≤ max (η - γ) (-η) := le_max_right _ _
  -- The maximum is at least the mean `-γ/2` of the two exponents, with equality only if both are
  -- equal to it.
  refine ⟨by linarith [hinstances, hscans], ⟨fun h => by linarith [hinstances, hscans, h], ?_⟩⟩
  rintro rfl
  rw [max_eq_right (by linarith)]

/-- **Remark 20**: "that is, at η = 1/36 for the saving D^{1/18} of Theorem 5 and at η =
0.0315 for the saving D^{0.063} of Corollary 26 [...] the final exponent η/18". -/
theorem remark_20_numbers :
    ((1 / 18 : ℝ) / 2 = 1 / 36) ∧ ((0.063 : ℝ) / 2 = 0.0315) ∧ ((1 / 36 : ℝ) / 18 = 1 / 648) ∧
    ((0.0315 : ℝ) / 18 = 0.00175) := by
  norm_num

/-- **Remark 20**: "With the straightforward algorithm (O(n²/g) per instance, since every
vertex of A has O(√D/g) neighbors in the middle part) the reduction recovers the brute-force bound
n³": `n²/√D` query pairs times `⌈s/g⌉` neighbors is at most `2n²/g`, and `4ng` instances at `2n²/g`
each come to `8n³`.  (That a vertex of `A` has at most `⌈s/g⌉` neighbors in the middle part is the
library's lemma `TriangleInstance.ncard_nbr_lopInstance_le`.)  The paper adds "up to a logarithmic
factor".  The cost of the instances has no such factor; the term ν n³ log n/g of Theorem 17, for the
scans, has one.  Only the cost of the instances is treated here. -/
theorem remark_20_brute_force {n D g : ℕ} (hD : 16 ≤ D) (hg1 : 1 ≤ g)
    (hg : (g : ℝ) ≤ Real.sqrt D) :
    (n : ℝ) ^ 2 / Real.sqrt D * (pieceSize D g : ℝ) ≤ 2 * (n : ℝ) ^ 2 / (g : ℝ) ∧
    4 * (n : ℝ) * (g : ℝ) * (2 * (n : ℝ) ^ 2 / (g : ℝ)) = 8 * (n : ℝ) ^ 3 := by
  have hsqrt : 0 < Real.sqrt D := by linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
  refine ⟨?_, by field_simp; ring⟩
  calc (n : ℝ) ^ 2 / Real.sqrt D * (pieceSize D g : ℝ)
      ≤ (n : ℝ) ^ 2 / Real.sqrt D * (2 * Real.sqrt D / g) := by
        gcongr
        exact pieceSize_le_two_mul_sqrt_div hg1 hg
    _ = 2 * (n : ℝ) ^ 2 / (g : ℝ) := by field_simp

end ThreeSumApsp
