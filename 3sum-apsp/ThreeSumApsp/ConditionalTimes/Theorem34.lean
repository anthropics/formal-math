/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.ConditionalTimes.SmallFacts

/-!
# Theorem 34 from Theorems 22 and 33

Write `m = ⌈n^μ⌉`. The (min,+)-product of an `n × m` matrix by an `m × n` matrix is cut into
`⌈n/m⌉²` products of `m × m` matrices, at a cost of `O(m² (1 + log u))` each for the copying (the
claim `hcut`), and Theorem 22 computes each of them.

1. The entries are at most `n^{1-μ} (log n + 1)^e ≤ n ≤ m²` (`eventually_entries_le`,
   `natCast_le_thinDim_rpow_two`; the second is where `μ ≥ 1/2` is used). Theorem 22 is stated for
   the bound `m^κ` on the entries (`κ` is the paper's ν); we take `κ = 2`, and `hrelax` lets the
   algorithm run on smaller entries.
2. There are at most `(2n/m)²` products (`natCeil_div_le_two_mul`), and `1 + log u ≤ 2 log n`
   (`one_add_logU_le`).
3. The total is `Õ(n^{2-2μ} m^{3-δ}) = Õ(n^{2+μ-μδ})`, where `3 - δ` is the exponent of Theorem 22
   (`isPowPolylog_total`).

This gives `rectMinPlus_of_minPlusInPolylog`. With `δ = ε'/3` the bound is `O(n^{2+μ-ε₁})` for
`ε₁ = με'/6`, so Theorem 33 applies (`conditional_theorem_34`).
-/

public section

open ThreeSumApsp.ConditionalTimes

namespace ThreeSumApsp

namespace ConditionalTimes

open Filter

/-- `1 ≤ ⌈n^μ⌉` for `n ≥ 1`. -/
private theorem one_le_thinDim (μ : ℝ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ thinDim μ n :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) μ)

/-- `⌈n^μ⌉ ≤ n` for `μ ≤ 1` and `n ≥ 1`. -/
private theorem thinDim_le_self {μ : ℝ} (hμ1 : μ ≤ 1) {n : ℕ} (hn : 1 ≤ n) : thinDim μ n ≤ n :=
  Nat.ceil_le.2 (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hμ1)

/-- `n ≤ m²` for `m = ⌈n^μ⌉` and `μ ≥ 1/2`. -/
private theorem natCast_le_thinDim_rpow_two {μ : ℝ} (hμ : 1 / 2 ≤ μ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ (thinDim μ n : ℝ) ^ (2 : ℝ) := by
  have hroot : (n : ℝ) ^ (1 / 2 : ℝ) ≤ thinDim μ n :=
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hμ).trans (Nat.le_ceil _)
  calc (n : ℝ) = ((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul n.cast_nonneg]
        norm_num
    _ ≤ (thinDim μ n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg n.cast_nonneg _) hroot (by norm_num)

/-- The bound `n^{1-μ} (log n + 1)^e` on the entries is at most `n` for large `n`, for `μ > 0`. -/
private theorem eventually_entries_le {μ : ℝ} (hμ0 : 0 < μ) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - μ) * (Real.log n + 1) ^ e ≤ n := by
  filter_upwards [(isPowPolylog_rpow_mul_log_add_one_pow (1 - μ) e).eventually_abs_le
    (sub_lt_self 1 hμ0)] with n hn
  simpa only [Real.rpow_one] using (le_abs_self _).trans hn

/-- `1 + logU u ≤ 2 log n` for `u ≤ n` and `n ≥ 3`. -/
private theorem one_add_logU_le {n : ℕ} (hn : 3 ≤ n) {u : ℝ} (hu : u ≤ n) :
    1 + logU u ≤ 2 * Real.log n := by
  linarith [Real.one_le_log_natCast_of_three_le hn, logU_le_log (by omega : 2 ≤ n) hu]

/-- `⌈n/m⌉ ≤ 2 n/m` for `1 ≤ m ≤ n`. -/
private theorem natCeil_div_le_two_mul {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (⌈(n : ℝ) / (m : ℝ)⌉₊ : ℝ) ≤ 2 * ((n : ℝ) * (m : ℝ)⁻¹) := by
  have hquot : 1 ≤ (n : ℝ) / m := (one_le_div (Nat.cast_pos.2 hm)).2 (Nat.cast_le.2 hmn)
  rw [← div_eq_mul_inv]
  -- `⌈x⌉ < x + 1 ≤ 2x` for `x ≥ 1`
  linarith [Nat.ceil_lt_add_one (zero_le_one.trans hquot)]

/-- Step 3: `(2n/m)² (G(m) + c m² · 2 log n) = Õ(n^{2+μ-μδ})` if `G(s) = Õ(s^{3-δ})`, where
`m = ⌈n^μ⌉`, `μ > 0` and `δ ≤ 1`. -/
private theorem isPowPolylog_total {G : ℕ → ℝ} {μ δ : ℝ} (hμ0 : 0 < μ) (hδ : δ ≤ 1)
    (hG : IsPowPolylog G (3 - δ)) (c : ℝ) :
    IsPowPolylog (fun n : ℕ => (2 * ((n : ℝ) * (thinDim μ n : ℝ)⁻¹)) ^ 2 *
      (G (thinDim μ n) + c * ((thinDim μ n : ℝ) ^ 2 * (2 * Real.log n)))) (2 + μ - μ * δ) := by
  have hm : IsBigOPow (fun n : ℕ => (thinDim μ n : ℝ)) μ := isBigOPow_ceil_rpow hμ0.le
  have hblocks : IsPowPolylog (fun n : ℕ => (2 * ((n : ℝ) * (thinDim μ n : ℝ)⁻¹)) ^ 2)
      (2 - 2 * μ) :=
    ((((isBigOPow_natCast.mul (isBigOPow_inv_ceil_rpow μ)).const_mul 2).pow 2).mono
      (le_of_eq (by push_cast; ring))).isPowPolylog
  have hproduct : IsPowPolylog (fun n : ℕ => G (thinDim μ n)) ((3 - δ) * μ) :=
    hG.comp hm (show 0 ≤ 3 - δ by linarith) hμ0.le
  -- Copying is cheaper than multiplying: `2μ ≤ (3 - δ)μ`.
  have hcheaper : μ * (2 : ℕ) + 0 ≤ (3 - δ) * μ := by
    push_cast
    linarith [mul_nonneg hμ0.le (sub_nonneg.2 hδ)]
  have hcopy : IsPowPolylog (fun n : ℕ => c * ((thinDim μ n : ℝ) ^ 2 * (2 * Real.log n)))
      ((3 - δ) * μ) :=
    ((((hm.pow 2).isPowPolylog).mul (isPowPolylog_log.const_mul 2)).const_mul c).mono hcheaper
  -- `(2 - 2μ) + (3 - δ)μ = 2 + μ - μδ`
  exact (hblocks.mul (hproduct.add hcopy)).mono (le_of_eq (by ring))

/-- The first half of the proof of Theorem 34: if the (min,+)-product of square
matrices is computed in `Õ(n^{3-δ})` time (`h22`; Theorem 22 has `δ = ε'/3`), then the product of an
`n × n^μ` matrix by an `n^μ × n` matrix with entries up to `n^{1-μ} (log n + 1)^e` is computed in
`Õ(n^{2+μ-μδ})` time: "Theorem 22 computes each of them in Õ((n^μ)^{3-ε'/3}) time, and all of them
in Õ(n^{2+μ-με'/3}) time". `μ ≤ 1` is used for the number of blocks. -/
theorem rectMinPlus_of_minPlusInPolylog (M : TimeModel) {μ δ : ℝ} (hμ : 1 / 2 ≤ μ) (hμ1 : μ ≤ 1)
    (hδ : δ ≤ 1) (h22 : Claim.MinPlusInPolylog M (3 - δ)) (hcut : Claim.RectMinPlusFromSquare M)
    (hrelax : Closure.RelaxMinPlusBound M) (e : ℕ) :
    ∃ T : ℕ → ℕ → ℝ → ℝ, M.rectMinPlus T ∧
      UpperPowPolylog (fun n => T n (thinDim μ n) ((n : ℝ) ^ (1 - μ) * (Real.log n + 1) ^ e))
        (2 + μ - μ * δ) := by
  have hμ0 : 0 < μ := by linarith
  -- Theorem 22 for entries up to `m²`, run on entries up to `u ≤ m²`.
  obtain ⟨T, hT, hTclass⟩ := h22 2 (by norm_num)
  obtain ⟨C₀, hblocks⟩ := hcut
  obtain ⟨G, hG0, hG, hTG⟩ := hTclass.exists_isPowPolylog
  refine ⟨_, hblocks _ (hrelax T (fun m u => max u ((m : ℝ) ^ (2 : ℝ)))
    (fun _ _ => le_max_left _ _) hT),
    (isPowPolylog_total hμ0 hδ hG |C₀|).upperPowPolylog.mono_left ?_⟩
  filter_upwards [(tendsto_ceil_rpow_atTop hμ0).eventually hTG, eventually_entries_le hμ0 e,
    eventually_ge_atTop 3] with n hTGm hentries hn
  have hn1 : 1 ≤ n := by omega
  set u : ℝ := (n : ℝ) ^ (1 - μ) * (Real.log n + 1) ^ e
  set m : ℕ := thinDim μ n
  have hsquare : T m (max u ((m : ℝ) ^ (2 : ℝ))) ≤ G m := by
    rw [max_eq_right (hentries.trans (natCast_le_thinDim_rpow_two hμ hn1))]
    exact hTGm
  have hcopy : C₀ * ((m : ℝ) ^ 2 * (1 + logU u)) ≤ |C₀| * ((m : ℝ) ^ 2 * (2 * Real.log n)) :=
    (le_abs_mul_of_le_mul le_rfl
      (mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (logU_nonneg u)))).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (one_add_logU_le hn hentries) (sq_nonneg _)) (abs_nonneg C₀))
  have hcost0 : 0 ≤ G m + |C₀| * ((m : ℝ) ^ 2 * (2 * Real.log n)) :=
    add_nonneg (hG0 m) (by positivity)
  calc (⌈(n : ℝ) / (m : ℝ)⌉₊ : ℝ) ^ 2
        * (T m (max u ((m : ℝ) ^ (2 : ℝ))) + C₀ * ((m : ℝ) ^ 2 * (1 + logU u)))
      ≤ (⌈(n : ℝ) / (m : ℝ)⌉₊ : ℝ) ^ 2 * (G m + |C₀| * ((m : ℝ) ^ 2 * (2 * Real.log n))) :=
        mul_le_mul_of_nonneg_left (add_le_add hsquare hcopy) (sq_nonneg _)
    _ ≤ (2 * ((n : ℝ) * (m : ℝ)⁻¹)) ^ 2 * (G m + |C₀| * ((m : ℝ) ^ 2 * (2 * Real.log n))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (natCeil_div_le_two_mul
          (one_le_thinDim μ hn1) (thinDim_le_self hμ1 hn1)) 2) hcost0

end ConditionalTimes

/-- The deduction of **Theorem 34** from Theorems 22 and 33: "Theorem 22 computes each of them in
Õ((n^μ)^{3-ε'/3}) time, and all of them in Õ(n^{2+μ-με'/3}) time. This is O(n^{2+μ-ε₁}) for any
constant ε₁ < με'/3, so [CVX21, Theorem 3.1] applies, in the deterministic form of Theorem 33, since
the algorithm of Theorem 22 is deterministic." Here `ε' = 0.00175` (Theorem 19). `μ` is a real
parameter; 1/2 ≤ μ ≤ 1 holds for the paper's μ (Section 5.1). The conclusion `Claim.Theorem_34 M μ`
is literally the conclusion of `h33`. So what this theorem checks is that the premise of Theorem 33
holds for some ε₁ > 0.

The entries: the paper's proof bounds them by "Õ(n^{1-μ}) ≤ Õ(n^μ), because μ ≥ 1/2", and Theorem
22, applied to matrices of size n^μ, allows entries up to (n^μ)^ν for every constant ν. Here
n^{1-μ}(log n + 1)^e ≤ n ≤ (n^μ)² for large n, which is the case `κ = 2` of `h22` (`κ` is the
paper's ν), used through `hrelax`. So μ ≥ 1/2 is used only for n ≤ (n^μ)²; with a larger exponent,
any μ > 0 would do. -/
theorem conditional_theorem_34 (M : TimeModel) (μ : ℝ) (hμ : 1 / 2 ≤ μ) (hμ1 : μ ≤ 1)
    (h22 : Claim.MinPlusInPolylog M (3 - 0.00175 / 3)) (hcut : Claim.RectMinPlusFromSquare M)
    (hrelax : Closure.RelaxMinPlusBound M) (h33 : Claim.Theorem_33 M μ) :
    Claim.Theorem_34 M μ := by
  have hμ0 : 0 < μ := by linarith
  -- `ε₁ = με'/6 < με'/3`
  refine h33 (μ * 0.00175 / 6) (by positivity) fun e => ?_
  obtain ⟨T, hT, hTclass⟩ :=
    rectMinPlus_of_minPlusInPolylog M hμ hμ1 (by norm_num) h22 hcut hrelax e
  exact ⟨T, hT, hTclass.upperBigOPow (by linarith)⟩

end ThreeSumApsp
