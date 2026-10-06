/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ParameterSteps
public import ThreeSumApsp.Sec5.Lemma37
public import ThreeSumApsp.Util.Asymptotics.Logarithms
public import ThreeSumApsp.Util.Asymptotics.Powers

/-!
# Corollary 38

For `d ≤ n^{1/40}` and large `n`, comparison counts are computed in
`O(|P| n^{0.0229} + n²/d^{0.126} + n^{2-1/440} log n)` time.  The algorithm applies Lemma 37 with
`s := ⌈n^{1-1/440}/d⌉` (`blockLen`), pads the product to the inner dimension
`D* := ⌈3d²n^{1/440}⌉` (`Dstar`), and applies Corollary 26 with `N := n` and `D := D*`.

Running times are not defined here.  This file proves that the algorithm is correct and that
Corollary 26 applies (`corollary_38_correct`), and that the times of Corollary 26 and Lemma 37 add
up to the bound (`corollary_38_bound`).  Both rest on the inequalities of the paper's proof.  Each
of them is a lemma, in the paper's order:
* `D'' ≤ 3d²n^{1/440}`, so the product can be padded (`D''_le`, `D''_le_Dstar`);
* `D* ≤ 4n^{23/440}`, so `(D*)^18 ≤ n` (`Dstar_le`, `Dstar_pow_le`);
* `(D*)^{0.437} = O(n^{0.0229})` and `(D*)^{0.063} ≥ d^{0.126}` (`Dstar_rpow_le`,
  `rpow_le_Dstar_rpow`);
* `nD* = O(n^{1.06})`, `nds ≤ 2n^{2-1/440}`, `ds² ≤ 4n^{2-1/440}` (`mul_Dstar_le`,
  `mul_mul_blockLen_le`, `mul_blockLen_sq_le`).
-/

@[expose] public section

namespace ThreeSumApsp

open Finset Asymptotics Filter
open ComparisonCounts

namespace Corollary38

/-- The hypotheses of Corollary 38: "Let d ≤ n^{1/40}, and let n be larger than a suitable
constant."  The first four fields are what the proof needs of the size of `n`; they make the
constant large, more than `2^610`. -/
structure Regime (n d : ℕ) : Prop where
  /-- There is at least one list. -/
  one_le_n : 1 ≤ n
  /-- The step `2d²n^{1/440} + d + 1 ≤ 3d²n^{1/440}` needs this at `d = 1`. -/
  two_le_rpow : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 440 : ℝ)
  /-- This is equivalent to the step `4^18 n^{0.941} ≤ n`. -/
  four_pow_le_rpow : (4 : ℝ) ^ 18 ≤ (n : ℝ) ^ (0.059 : ℝ)
  /-- This gives `n^{1.06} = O(n^{2-1/440} log n)`. -/
  one_le_log : 1 ≤ Real.log n
  /-- The standing assumption of Section 5.2: "Throughout, d ∈ [n] is a parameter". -/
  one_le_d : 1 ≤ d
  /-- The hypothesis of the corollary: "Let d ≤ n^{1/40}". -/
  d_le : (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ)

/-- There is a suitable constant. -/
theorem exists_regime :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) → Regime n d := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((eventually_ge_atTop 3).and
    ((eventually_le_rpow 2 (η := 1 / 440) (by norm_num)).and
      (eventually_le_rpow (4 ^ 18) (η := 0.059) (by norm_num))))
  refine ⟨n₀, fun n d hn hd hdn => ?_⟩
  obtain ⟨hthree, htwo, hpow⟩ := hn₀ n hn
  exact ⟨by omega, htwo, hpow, Real.one_le_log_natCast_of_three_le hthree, hd, hdn⟩

variable {n d : ℕ}

namespace Regime

theorem one_le_cast_n (h : Regime n d) : (1 : ℝ) ≤ n := Nat.one_le_cast.2 h.one_le_n

theorem cast_n_pos (h : Regime n d) : (0 : ℝ) < n := Nat.cast_pos.2 h.one_le_n

theorem one_le_cast_d (h : Regime n d) : (1 : ℝ) ≤ d := Nat.one_le_cast.2 h.one_le_d

theorem cast_d_pos (h : Regime n d) : (0 : ℝ) < d := Nat.cast_pos.2 h.one_le_d

theorem d_le_n (h : Regime n d) : d ≤ n :=
  Nat.cast_le (α := ℝ).1 (h.d_le.trans (Real.rpow_le_self_of_one_le h.one_le_cast_n (by norm_num)))

end Regime

/-- `s = ⌈n^{1-1/440}/d⌉ ≥ 1`, the hypothesis of Lemma 37. -/
theorem one_le_blockLen (h : Regime n d) : 1 ≤ blockLen n d :=
  Nat.ceil_pos.2 (div_pos (Real.rpow_pos_of_pos h.cast_n_pos _) h.cast_d_pos)

/-- `ds ≥ n^{1-1/440}`, since `s = ⌈n^{1-1/440}/d⌉`. -/
theorem le_mul_blockLen (h : Regime n d) : (n : ℝ) ^ (1 - 1 / 440 : ℝ) ≤ d * blockLen n d :=
  (div_le_iff₀' h.cast_d_pos).1 (Nat.le_ceil _)

/-- `ds ≤ n^{1-1/440} + d ≤ 2n^{1-1/440}`, since `s = ⌈n^{1-1/440}/d⌉`. -/
theorem mul_blockLen_le (h : Regime n d) :
    (d : ℝ) * blockLen n d ≤ 2 * (n : ℝ) ^ (1 - 1 / 440 : ℝ) := by
  have hd0 := h.cast_d_pos
  have hceil : (blockLen n d : ℝ) < (n : ℝ) ^ (1 - 1 / 440 : ℝ) / d + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsmall : (d : ℝ) ≤ (n : ℝ) ^ (1 - 1 / 440 : ℝ) :=
    h.d_le.trans (Real.rpow_le_rpow_of_exponent_le h.one_le_cast_n (by norm_num))
  calc (d : ℝ) * blockLen n d ≤ d * ((n : ℝ) ^ (1 - 1 / 440 : ℝ) / d + 1) := by gcongr
    _ = (n : ℝ) ^ (1 - 1 / 440 : ℝ) + d := by field_simp
    _ ≤ 2 * (n : ℝ) ^ (1 - 1 / 440 : ℝ) := by linarith [hsmall]

/-- "so that D'' ≤ 2d²n^{1/440} + d + 1 ≤ 3d²n^{1/440}". -/
theorem D''_le (h : Regime n d) :
    (D'' n d (blockLen n d) : ℝ) ≤ 3 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) := by
  have hd := h.one_le_cast_d
  have hs : (0 : ℝ) < blockLen n d := Nat.cast_pos.2 (one_le_blockLen h)
  have hceil : ((⌈(2 * n * d : ℚ) / blockLen n d⌉₊ : ℕ) : ℝ) < 2 * n * d / blockLen n d + 1 := by
    have hrat := (Rat.cast_lt (K := ℝ)).2
      (Nat.ceil_lt_add_one (a := (2 * n * d : ℚ) / blockLen n d) (by positivity))
    push_cast at hrat
    exact hrat
  -- `2nd/s ≤ 2d²n^{1/440}` because `n = n^{1-1/440} n^{1/440}` and `n^{1-1/440} ≤ ds`
  have hquot : 2 * n * d / blockLen n d ≤ 2 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) := by
    rw [div_le_iff₀ hs]
    calc 2 * (n : ℝ) * d = 2 * d * (n : ℝ) ^ (1 / 440 : ℝ) * (n : ℝ) ^ (1 - 1 / 440 : ℝ) := by
          rw [mul_assoc (2 * (d : ℝ)), ← Real.rpow_add h.cast_n_pos, add_sub_cancel, Real.rpow_one]
          ring
      _ ≤ 2 * d * (n : ℝ) ^ (1 / 440 : ℝ) * (d * blockLen n d) := by
          gcongr
          exact le_mul_blockLen h
      _ = 2 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) * blockLen n d := by ring
  -- `d + 1 ≤ 2d² ≤ d²n^{1/440}`
  have hrest : (d : ℝ) + 1 ≤ (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) :=
    calc (d : ℝ) + 1 ≤ (d : ℝ) ^ 2 * 2 := by linarith [le_self_pow₀ hd two_ne_zero]
      _ ≤ (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) := by
          gcongr
          exact h.two_le_rpow
  calc (D'' n d (blockLen n d) : ℝ) = (⌈(2 * n * d : ℚ) / blockLen n d⌉₊ : ℕ) + d := by
        rw [D'', Nat.cast_add]
    _ ≤ 2 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) + d + 1 := by linarith [hceil, hquot]
    _ ≤ 3 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) := by linarith [hrest]

/-- `D'' ≤ D*`: the product of Lemma 37 can be padded to the inner dimension `D*`. -/
theorem D''_le_Dstar (h : Regime n d) : D'' n d (blockLen n d) ≤ Dstar n d :=
  Nat.cast_le (α := ℝ).1 ((D''_le h).trans (Nat.le_ceil _))

/-- "Since d ≤ n^{1/40}, we have D* ≤ 4n^{23/440}". -/
theorem Dstar_le (h : Regime n d) : (Dstar n d : ℝ) ≤ 4 * (n : ℝ) ^ (23 / 440 : ℝ) := by
  have hn := h.cast_n_pos
  have hceil : (Dstar n d : ℝ) < 3 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hone : 1 ≤ (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ h.one_le_cast_d) (by linarith [h.two_le_rpow])
  calc (Dstar n d : ℝ) ≤ 4 * ((d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ)) := by linarith [hceil, hone]
    _ ≤ 4 * (((n : ℝ) ^ (1 / 40 : ℝ)) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ)) := by
        gcongr
        exact h.d_le
    _ = 4 * (n : ℝ) ^ (23 / 440 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
        norm_num

/-- "so (D*)^18 ≤ 4^18 n^{0.941} ≤ n", the hypothesis `N ≥ D^18` of Corollary 26. -/
theorem Dstar_pow_le (h : Regime n d) : Dstar n d ^ 18 ≤ n := by
  have hn := h.cast_n_pos
  have hreal : (Dstar n d : ℝ) ^ 18 ≤ n :=
    calc (Dstar n d : ℝ) ^ 18 ≤ (4 * (n : ℝ) ^ (23 / 440 : ℝ)) ^ 18 := by
          gcongr
          exact Dstar_le h
      _ = 4 ^ 18 * (n : ℝ) ^ (23 / 440 * (18 : ℕ) : ℝ) := by
          rw [mul_pow, Real.rpow_mul hn.le, Real.rpow_natCast]
      _ ≤ 4 ^ 18 * (n : ℝ) ^ (0.941 : ℝ) := by
          gcongr
          · exact h.one_le_cast_n
          · norm_num
      _ ≤ (n : ℝ) ^ (0.059 : ℝ) * (n : ℝ) ^ (0.941 : ℝ) := by
          gcongr
          exact h.four_pow_le_rpow
      _ = n := by
          rw [← Real.rpow_add hn]
          norm_num
  exact_mod_cast hreal

/-- "Here (D*)^{0.437} ≤ 4^{0.437} n^{0.437·23/440} = O(n^{0.0229})", with the constant 4. -/
theorem Dstar_rpow_le (h : Regime n d) :
    (Dstar n d : ℝ) ^ (0.437 : ℝ) ≤ 4 * (n : ℝ) ^ (0.0229 : ℝ) :=
  calc (Dstar n d : ℝ) ^ (0.437 : ℝ) ≤ (4 * (n : ℝ) ^ (23 / 440 : ℝ)) ^ (0.437 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (Dstar_le h) (by norm_num)
    _ = 4 ^ (0.437 : ℝ) * (n : ℝ) ^ (23 / 440 * 0.437 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul h.cast_n_pos.le]
    _ ≤ 4 ^ (1 : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) := by
        gcongr
        · norm_num
        · norm_num
        · exact h.one_le_cast_n
        · norm_num
    _ = 4 * (n : ℝ) ^ (0.0229 : ℝ) := by rw [Real.rpow_one]

/-- "and (D*)^{0.063} ≥ (3d²)^{0.063} ≥ d^{0.126}". -/
theorem rpow_le_Dstar_rpow (h : Regime n d) :
    (d : ℝ) ^ (0.126 : ℝ) ≤ (Dstar n d : ℝ) ^ (0.063 : ℝ) := by
  have hle : 3 * (d : ℝ) ^ 2 ≤ Dstar n d :=
    (le_mul_of_one_le_right (by positivity) (by linarith [h.two_le_rpow])).trans (Nat.le_ceil _)
  calc (d : ℝ) ^ (0.126 : ℝ) = ((d : ℝ) ^ 2) ^ (0.063 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h.cast_d_pos.le]
        norm_num
    _ ≤ (3 * (d : ℝ) ^ 2) ^ (0.063 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith [sq_nonneg (d : ℝ)]) (by norm_num)
    _ ≤ (Dstar n d : ℝ) ^ (0.063 : ℝ) := Real.rpow_le_rpow (by positivity) hle (by norm_num)

/-- "nD* = O(n^{1.06})". -/
theorem mul_Dstar_le (h : Regime n d) : (n : ℝ) * Dstar n d ≤ 4 * (n : ℝ) ^ (1.06 : ℝ) :=
  calc (n : ℝ) * Dstar n d ≤ n * (4 * (n : ℝ) ^ (23 / 440 : ℝ)) := by
        gcongr
        exact Dstar_le h
    _ = 4 * (n : ℝ) ^ (1 + 23 / 440 : ℝ) := by
        rw [Real.rpow_add h.cast_n_pos, Real.rpow_one]
        ring
    _ ≤ 4 * (n : ℝ) ^ (1.06 : ℝ) := by
        gcongr
        · exact h.one_le_cast_n
        · norm_num

/-- `n · n^{1-1/440} = n^{2-1/440}`. -/
private theorem self_mul_rpow (h : Regime n d) :
    (n : ℝ) * (n : ℝ) ^ (1 - 1 / 440 : ℝ) = (n : ℝ) ^ (2 - 1 / 440 : ℝ) := by
  rw [show (2 - 1 / 440 : ℝ) = 1 + (1 - 1 / 440) by ring, Real.rpow_add h.cast_n_pos, Real.rpow_one]

/-- "nds ≤ 2n^{2-1/440}". -/
theorem mul_mul_blockLen_le (h : Regime n d) :
    (n : ℝ) * d * blockLen n d ≤ 2 * (n : ℝ) ^ (2 - 1 / 440 : ℝ) :=
  calc (n : ℝ) * d * blockLen n d = n * (d * blockLen n d) := by ring
    _ ≤ n * (2 * (n : ℝ) ^ (1 - 1 / 440 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_blockLen_le h) h.cast_n_pos.le
    _ = 2 * (n : ℝ) ^ (2 - 1 / 440 : ℝ) := by
        rw [← self_mul_rpow h]
        ring

/-- "ds² ≤ 4n^{2-1/440}": `s ≤ ds ≤ 2n^{1-1/440}`, and `n^{1-1/440} ≤ n`. -/
theorem mul_blockLen_sq_le (h : Regime n d) :
    (d : ℝ) * (blockLen n d : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ (2 - 1 / 440 : ℝ) := by
  have hs : (blockLen n d : ℝ) ≤ 2 * (n : ℝ) ^ (1 - 1 / 440 : ℝ) :=
    (le_mul_of_one_le_left (Nat.cast_nonneg _) h.one_le_cast_d).trans (mul_blockLen_le h)
  have hle : (n : ℝ) ^ (1 - 1 / 440 : ℝ) ≤ n :=
    Real.rpow_le_self_of_one_le h.one_le_cast_n (by norm_num)
  calc (d : ℝ) * (blockLen n d : ℝ) ^ 2 = d * blockLen n d * blockLen n d := by ring
    _ ≤ 2 * (n : ℝ) ^ (1 - 1 / 440 : ℝ) * (2 * (n : ℝ) ^ (1 - 1 / 440 : ℝ)) :=
        mul_le_mul (mul_blockLen_le h) hs (Nat.cast_nonneg _) (by positivity)
    _ = 4 * ((n : ℝ) ^ (1 - 1 / 440 : ℝ) * (n : ℝ) ^ (1 - 1 / 440 : ℝ)) := by ring
    _ ≤ 4 * (n * (n : ℝ) ^ (1 - 1 / 440 : ℝ)) := by gcongr
    _ = 4 * (n : ℝ) ^ (2 - 1 / 440 : ℝ) := by rw [self_mul_rpow h]

end Corollary38

/-- Proof of Corollary 38: "Corollary 26 ... computes (XY)[r,c] for all (r,c) ∈ P
deterministically in O(|P|(D*)^{0.437} + n²/(D*)^{0.063}) time" and "the time of Lemma 37 itself is
O(nD* + (|P| + nds + ds²) log n) = O(|P| n^{0.0229} + n^{2-1/440} log n)"; together these are at
most a constant times the bound |P| n^{0.0229} + n²/d^{0.126} + n^{2-1/440} log n of the corollary.
`p` is |P|.  The hypothesis 1 ≤ d is the standing assumption of Section 5.2: "Throughout, d ∈ [n] is
a parameter".

NOTE. The time of Lemma 37 is taken as in the library's `Claim.Lemma_37`, so that this is the
arithmetic of `conditional_corollary_38`: it has `log n + 1` in place of `log n`, which makes the
statement stronger. -/
theorem corollary_38_bound :
    ∃ (K : ℝ) (n₀ : ℕ), ∀ n d p : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) →
      ((p : ℝ) * (Dstar n d : ℝ) ^ (0.437 : ℝ) + (n : ℝ) ^ 2 / (Dstar n d : ℝ) ^ (0.063 : ℝ)) +
          ((n : ℝ) * Dstar n d +
            ((n : ℝ) * d * blockLen n d + (d : ℝ) * (blockLen n d : ℝ) ^ 2 + (p : ℝ)) *
              (Real.log n + 1))
        ≤ K * ((p : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (d : ℝ) ^ (0.126 : ℝ) +
          (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n) := by
  obtain ⟨n₀, hn₀⟩ := Corollary38.exists_regime
  obtain ⟨c, hc, hlogx⟩ := dominated_log_add_one_rpow (η := 0.0229) (by norm_num)
  refine ⟨16 + c, n₀, fun n d p hn hd hdn => ?_⟩
  have h := hn₀ n d hn hd hdn
  have hd0 := h.cast_d_pos
  have hlog := h.one_le_log
  -- Corollary 26: the `|P|` queries and the preprocessing
  have hquery : (p : ℝ) * (Dstar n d : ℝ) ^ (0.437 : ℝ) ≤ p * (4 * (n : ℝ) ^ (0.0229 : ℝ)) :=
    mul_le_mul_of_nonneg_left (Corollary38.Dstar_rpow_le h) p.cast_nonneg
  have hprep : (n : ℝ) ^ 2 / (Dstar n d : ℝ) ^ (0.063 : ℝ) ≤ (n : ℝ) ^ 2 / (d : ℝ) ^ (0.126 : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (Corollary38.rpow_le_Dstar_rpow h)
  -- Lemma 37: filling in `X` and `Y`, the pairs in the same block, and the `|P|` answers
  have hfill : (n : ℝ) * Dstar n d ≤ 4 * ((n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n) :=
    calc (n : ℝ) * Dstar n d ≤ 4 * (n : ℝ) ^ (1.06 : ℝ) := Corollary38.mul_Dstar_le h
      _ ≤ 4 * ((n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n) := by
          gcongr
          exact (Real.rpow_le_rpow_of_exponent_le h.one_le_cast_n (by norm_num)).trans
            (le_mul_of_one_le_right (by positivity) hlog)
  have hsame : ((n : ℝ) * d * blockLen n d + (d : ℝ) * (blockLen n d : ℝ) ^ 2) * (Real.log n + 1)
      ≤ 6 * (n : ℝ) ^ (2 - 1 / 440 : ℝ) * (2 * Real.log n) :=
    mul_le_mul (by linarith [Corollary38.mul_mul_blockLen_le h, Corollary38.mul_blockLen_sq_le h])
      (by linarith) (by linarith) (by positivity)
  have hanswers : (p : ℝ) * (Real.log n + 1) ≤ p * (c * (n : ℝ) ^ (0.0229 : ℝ)) :=
    mul_le_mul_of_nonneg_left (hlogx n h.one_le_cast_n) p.cast_nonneg
  -- the sum is at most `(4 + c) |P| n^{0.0229} + n²/d^{0.126} + (4 + 12) n^{2-1/440} log n`
  have hP : (0 : ℝ) ≤ (p : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) := by positivity
  have hQ : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (d : ℝ) ^ (0.126 : ℝ) := by positivity
  have hR : (0 : ℝ) ≤ (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n := by positivity
  linarith [hquery, hprep, hfill, hsame, hanswers, hP, hQ, mul_nonneg hc hQ, mul_nonneg hc hR]

/-- Corollary 38, the part that is not a running time: the counts γ(r,c), (r,c) ∈ P, "with < or with
≤", are the wanted entries of a product with inner dimension D*, which satisfies the hypotheses of
Corollary 26 with N = n (second to fourth conjunct: (D*)^18 ≤ n, and entries of absolute value at
most n), plus the integers γ₂(r,c) of Lemma 37. The first conjunct, D'' ≤ D* (proof of Corollary 38:
"D'' ≤ 2d²n^{1/440} + d + 1 ≤ 3d²n^{1/440}"), says that "pad the product to the inner dimension D*"
only adds zero columns and zero rows: `padInnerCols` and `padInnerRows` would cut off a larger
matrix. `n₀` is the "suitable constant" of the corollary.  The hypothesis 1 ≤ d is the standing
assumption of Section 5.2: "Throughout, d ∈ [n] is a parameter". -/
theorem corollary_38_correct :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) →
      ∀ (cmp : Cmp) (Ls : Lists n d), Ls.Valid →
      ∀ (P : Finset (Fin n × Fin n)) (o : SortedOrder cmp Ls)
        (idx : Fin d × ℕ → Fin (D'' n d (blockLen n d))),
      Set.InjOn idx (blockPairs o (blockLen n d)) →
        D'' n d (blockLen n d) ≤ Dstar n d ∧
        (Dstar n d) ^ 18 ≤ n ∧
        (∀ r j, |(padInnerCols (Dstar n d) (matX o (blockLen n d) idx)) r j| ≤ n) ∧
        (∀ j c, |(padInnerRows (Dstar n d) (matY o (blockLen n d) idx)) j c| ≤ n) ∧
        ∀ r c, (r, c) ∈ P →
          (comparisonCount cmp Ls r c : ℤ) =
            ((padInnerCols (Dstar n d) (matX o (blockLen n d) idx)) *
              (padInnerRows (Dstar n d) (matY o (blockLen n d) idx))) r c
            + sameBlockCount o (blockLen n d) P r c := by
  obtain ⟨n₀, hn₀⟩ := Corollary38.exists_regime
  refine ⟨n₀, fun n d hn hd hdn cmp Ls hLs P o idx hidx => ?_⟩
  have h := hn₀ n d hn hd hdn
  obtain ⟨hX, hY, hcount⟩ :=
    lemma_37 cmp Ls hLs (blockLen n d) (Corollary38.one_le_blockLen h) P o idx hidx
  -- the entries of `X` and `Y` lie between 0 and `d ≤ n`, and the padding adds zeros
  have hdn' : (d : ℤ) ≤ n := Nat.cast_le.2 h.d_le_n
  refine ⟨Corollary38.D''_le_Dstar h, Corollary38.Dstar_pow_le h, fun r j => ?_, fun j c => ?_,
    fun r c hrc => ?_⟩
  · rw [padInnerCols]
    split_ifs
    · exact (abs_of_nonneg (hX r _).1).trans_le ((hX r _).2.trans hdn')
    · simp
  · rw [padInnerRows]
    split_ifs
    · exact (abs_of_nonneg (hY _ c).1).trans_le ((hY _ c).2.trans hdn')
    · simp
  · rw [Corollary26.padding _ (Corollary38.D''_le_Dstar h)]
    exact hcount r c hrc

end ThreeSumApsp
