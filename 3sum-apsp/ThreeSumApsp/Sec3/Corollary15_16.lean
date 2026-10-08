/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Chunks
public import ThreeSumApsp.Sec3.Parameters
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Corollaries 15 and 16: the number of pieces, and the bound for few query pairs

The theorems about programs are `wordRam_corollary_15` and `wordRam_corollary_16`.  This file has
two computations from the text around the corollaries.

* **Corollary 15.**  Its pieces are the chunks of `W` with `cap = ⌊n²/√D⌋`.  There are at most
  `⌈|W|√D/n²⌉ + 1` of them (`Corollary15.split`).  The program cuts `W` into pieces of
  `splitCap n D = max(1, ⌊n²/√D⌋)` pairs, and there are at most `2(n² + |W|√D)/n²` of these
  (`ceil_div_splitCap_le`, which the running-time claim uses).  So `n²` operations for each piece
  are `O(n² + |W|√D)` in all (`Corollary15.pieces_cost`).  Nothing else rests on
  `Corollary15.split` and `Corollary15.pieces_cost`.
* **After Corollary 16.**  For `|W| = O(n²/√D)` its bound is `O(n²/D^{0.063})`
  (`Corollary16.bound_le_of_card_le`; nothing else rests on it).
-/

public section

namespace ThreeSumApsp

/-! ### Corollary 15 -/

/-- `D ≤ D^18 ≤ n`. -/
private theorem le_of_pow_eighteen_le {n D : ℕ} (hn : D ^ 18 ≤ n) : D ≤ n :=
  (Nat.le_self_pow (by norm_num) D).trans hn

/-- Under the hypotheses of Corollary 15, `√D + 1 ≤ n²/√D`, because `(√D + 1)√D ≤ 2D ≤ D² ≤ n²`. -/
private theorem sqrt_add_one_le_div {n D : ℕ} (hD : 4 ≤ D) (hn : D ^ 18 ≤ n) :
    Real.sqrt D + 1 ≤ (n : ℝ) ^ 2 / Real.sqrt D := by
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast hD
  have hsqrt : 1 ≤ Real.sqrt D := Real.one_le_sqrt.mpr (by linarith)
  have hDn : (D : ℝ) ≤ n := by exact_mod_cast le_of_pow_eighteen_le hn
  rw [le_div_iff₀ (by linarith)]
  calc (Real.sqrt D + 1) * Real.sqrt D ≤ (Real.sqrt D + Real.sqrt D) * Real.sqrt D := by gcongr
    _ = 2 * D := by rw [← two_mul, mul_assoc, Real.mul_self_sqrt (by linarith)]
    _ ≤ D * D := by gcongr; linarith
    _ ≤ (n : ℝ) ^ 2 := by rw [sq]; gcongr

/-- The inequality behind the number of pieces in Corollary 15: `|W|/⌊r⌋ ≤ |W|/r + 1` for
`r = n²/√D`.  It holds because `y = |W|/r` is at most `√D ≤ r − 1`, so that
`|W| = y r ≤ (y + 1)(r − 1) ≤ (y + 1)⌊r⌋`. -/
private theorem card_div_queryCap_le {n D : ℕ} (hD : 4 ≤ D) (hn : D ^ 18 ≤ n)
    (W : Finset (Fin n × Fin n)) :
    (W.card : ℝ) / (queryCap n D : ℝ) ≤ (W.card : ℝ) * Real.sqrt D / (n : ℝ) ^ 2 + 1 := by
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < D))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by positivity) hn
  have hcap : (0 : ℝ) < queryCap n D := by
    exact_mod_cast one_le_queryCap (by omega) (le_of_pow_eighteen_le hn)
  have hW : (W.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (Finset.card_le_univ W).trans_eq (by simp [sq])
  set y := (W.card : ℝ) * Real.sqrt D / (n : ℝ) ^ 2 with hy
  set r := (n : ℝ) ^ 2 / Real.sqrt D with hr
  have hyr : y * r = W.card := by rw [hy, hr]; field_simp
  have hy0 : 0 ≤ y := by positivity
  have hysqrt : y ≤ Real.sqrt D := by
    rw [hy, div_le_iff₀ (by positivity), mul_comm]
    gcongr
  have hsqrtr : Real.sqrt D + 1 ≤ r := sqrt_add_one_le_div hD hn
  have hfloor : r < (queryCap n D : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [div_le_iff₀ hcap]
  calc (W.card : ℝ) ≤ y * r + (r - 1 - y) := by linarith [hyr, hysqrt, hsqrtr]
    _ = (y + 1) * (r - 1) := by ring
    _ ≤ (y + 1) * (queryCap n D : ℝ) := by gcongr; linarith [hfloor]

/-- **Corollary 15**, proof: "apply the theorem to each of at most ⌈|W|√D/n²⌉ + 1 pieces".  (That
`D` is a power of four is needed to apply Theorem 5, not to count the pieces.) -/
theorem Corollary15.split {n D : ℕ} (hD : 4 ≤ D) (hn : D ^ 18 ≤ n) (W : Finset (Fin n × Fin n)) :
    numChunks W (queryCap n D) ≤ ⌈(W.card : ℝ) * Real.sqrt D / (n : ℝ) ^ 2⌉₊ + 1 := by
  refine Nat.ceil_le.mpr ((card_div_queryCap_le hD hn W).trans ?_)
  push_cast
  gcongr
  exact Nat.le_ceil _

/-- A piece has at least half of `n² / √D` query pairs. -/
theorem sq_div_sqrt_le_two_mul_splitCap (n D : ℕ) :
    (n : ℝ) ^ 2 / Real.sqrt D ≤ 2 * (splitCap n D : ℝ) := by
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) ^ 2 / Real.sqrt D)
  have hone : (1 : ℝ) ≤ splitCap n D := by exact_mod_cast le_max_left 1 (queryCap n D)
  have hcap : (⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊ : ℝ) ≤ splitCap n D :=
    Nat.cast_le.2 (le_max_right 1 (queryCap n D))
  linarith [hfloor, hone, hcap]

/-- The number of pieces: `⌈w / cap⌉ ≤ 2 (n² + w √D) / n²`. -/
theorem ceil_div_splitCap_le {n D : ℕ} (w : ℕ) (hD : 1 ≤ D) (hn : 1 ≤ n) :
    (⌈(w : ℝ) / (splitCap n D : ℝ)⌉₊ : ℝ)
      ≤ 2 * (((n : ℝ) ^ 2 + (w : ℝ) * Real.sqrt D) / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.2 (Nat.cast_pos.2 hD)
  have hcap : (0 : ℝ) < splitCap n D := by exact_mod_cast lt_max_of_lt_left one_pos
  have hhalf : (n : ℝ) ^ 2 ≤ 2 * (splitCap n D : ℝ) * Real.sqrt D :=
    (div_le_iff₀ hsqrt).1 (sq_div_sqrt_le_two_mul_splitCap n D)
  have hquot : (w : ℝ) / (splitCap n D : ℝ) ≤ 2 * ((w : ℝ) * Real.sqrt D) / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hcap hn0]
    calc (w : ℝ) * (n : ℝ) ^ 2 ≤ (w : ℝ) * (2 * (splitCap n D : ℝ) * Real.sqrt D) :=
          mul_le_mul_of_nonneg_left hhalf w.cast_nonneg
      _ = 2 * ((w : ℝ) * Real.sqrt D) * (splitCap n D : ℝ) := by ring
  have hceil := Nat.ceil_lt_add_one (div_nonneg w.cast_nonneg hcap.le)
  rw [add_div, div_self hn0.ne']
  linarith [hceil, hquot, mul_div_assoc 2 ((w : ℝ) * Real.sqrt D) ((n : ℝ) ^ 2)]

/-- **Corollary 15**, the arithmetic behind "solves it deterministically in time O((n² + |W|√D) log²
D / D^{1/18})": the number of pieces times `n²` is at most `2(n² + |W|√D)`. -/
theorem Corollary15.pieces_cost {n D : ℕ} (hD : 4 ≤ D) (hn : D ^ 18 ≤ n)
    (W : Finset (Fin n × Fin n)) :
    (numChunks W (queryCap n D) : ℝ) * (n : ℝ) ^ 2
      ≤ 2 * ((n : ℝ) ^ 2 + (W.card : ℝ) * Real.sqrt D) := by
  have hDn := le_of_pow_eighteen_le hn
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  -- Under the hypotheses of Corollary 15 a piece has `⌊n²/√D⌋ ≥ 1` pairs.
  have hcap : splitCap n D = queryCap n D := max_eq_right (one_le_queryCap (by omega) hDn)
  have hcount := ceil_div_splitCap_le (n := n) (D := D) W.card (by omega) (by omega)
  rw [hcap] at hcount
  calc (numChunks W (queryCap n D) : ℝ) * (n : ℝ) ^ 2
      ≤ 2 * (((n : ℝ) ^ 2 + (W.card : ℝ) * Real.sqrt D) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcount hn0.le
    _ = 2 * ((n : ℝ) ^ 2 + (W.card : ℝ) * Real.sqrt D) := by
        rw [mul_assoc, div_mul_cancel₀ _ hn0.ne']

/-! ### After Corollary 16 -/

/-- After **Corollary 16**: "For |W| = O(n²/√D), which is what the reductions below produce, the
running time in Corollary 16 is O(n²/D^{0.063})."

NOTE.  Corollary 16 states no lower bound on `D`; this computation is stated for `D ≥ 1`. -/
theorem Corollary16.bound_le_of_card_le {n D : ℕ} (hD : 1 ≤ D) (C : ℝ) (Wcard : ℕ)
    (hW : (Wcard : ℝ) ≤ C * ((n : ℝ) ^ 2 / Real.sqrt D)) :
    (Wcard : ℝ) * (D : ℝ) ^ (0.437 : ℝ) + (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)
      ≤ (C + 1) * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hsqrt : Real.sqrt D = (D : ℝ) ^ (0.437 : ℝ) * (D : ℝ) ^ (0.063 : ℝ) := by
    rw [← Real.rpow_add hD0, Real.sqrt_eq_rpow]
    norm_num
  have hpow437 : 0 < (D : ℝ) ^ (0.437 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hpow063 : 0 < (D : ℝ) ^ (0.063 : ℝ) := Real.rpow_pos_of_pos hD0 _
  -- `|W| D^{0.437} ≤ C n² D^{0.437}/√D = C n²/D^{0.063}`.
  have hfirst : (Wcard : ℝ) * (D : ℝ) ^ (0.437 : ℝ) ≤ C * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) :=
    calc (Wcard : ℝ) * (D : ℝ) ^ (0.437 : ℝ)
        ≤ C * ((n : ℝ) ^ 2 / Real.sqrt D) * (D : ℝ) ^ (0.437 : ℝ) := by gcongr
      _ = C * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) := by rw [hsqrt]; field_simp
  linarith [hfirst]

end ThreeSumApsp
