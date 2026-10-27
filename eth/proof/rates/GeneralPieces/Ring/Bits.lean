/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Sizes
public import ClauseBound.Part.Bounds

/-! # The numbers in the proof of the theorem on the pieces with ρ = 1/√2: numbers of bits

The paragraph "Numbers of bits" of that proof in Appendix B, and the sentence on log Δ of the next
paragraph, sentence by sentence. Here h is the least integer ≥ 2 with p(h) ≥ 2^λ, and κ = π√(2/3)/ln 2.
Display (46) of the appendix is the hypothesis `Partitions.Bounds B C`: κ√E − B·log E − C ≤ log p(E)
for E ≥ 1 and log p(E) ≤ κ√E + C. The appendix has B = 1, from the formula of Hardy and Ramanujan;
So where the appendix has log h, there is B·log h here; at B = 1 the statements are those of the
appendix. One may take B ≥ 0 (`bounds_abs`).
Every statement is proved from those before it, in the order of the appendix: p(h−1) < 2^λ
(`p_pred_lt`); κ√(h−1) < λ + B·log h + C for B ≥ 0 (`kappa_sqrt_pred_lt`); h = O(λ²)
(`exists_hOf_le`); κ√h ≤ κ√(h−1) + κ (`kappa_sqrt_le_pred`) ≤ λ + O(log 2λ)
(`exists_kappa_sqrt_le`);
R^row_s ≤ (2h+1)·p(2h+s) and R^col_s ≤ (2h+1)·p(2h−s) (`Rrow_le`, `Rcol_le`); √(2h+s) + √(2h−s) ≤
2√(2h) (`sqrt_add_sqrt_le`); the display
c^row_s + c^col_s ≤ 2√2·κ√h + 2·log(2h+1) + 2C + 2 (`bits_le`) ≤ 2√2·λ + O(log 2λ)
(`exists_bits_le`); log Δ ≤ 2κ√h + log(4h+1) + C (`logb_Delta_le`) = O(λ) (`exists_Delta_le`). -/

public section

namespace GeneralPieces.Bits

open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes

variable {B C : ℝ}

/-- p(h−1) < 2^λ: by the choice of h if h > 2, and because p(1) = 1 if h = 2. -/
theorem p_pred_lt {lam : ℕ} (hl : 1 ≤ lam) : p (AppHalfPieces.hOf lam - 1) < 2 ^ lam := by
  rw [hOf_eq]
  exact ClauseBound.Part.Bits.p_pred_lt hl

/-- Display (46) with B holds with |B| as well, because log E ≥ 0 for E ≥ 1. -/
theorem bounds_abs (hB : Bounds B C) : Bounds |B| C := by
  refine ⟨fun E hE => ?_, hB.2⟩
  have h1 := hB.1 E hE
  have h2 : 0 ≤ logb 2 E := Real.logb_nonneg (by norm_num) (by exact_mod_cast hE)
  have h3 : B * logb 2 E ≤ |B| * logb 2 E := mul_le_mul_of_nonneg_right (le_abs_self B) h2
  linarith

/-- By display (46), for B ≥ 0: κ√(h−1) < λ + B·log h + C. -/
theorem kappa_sqrt_pred_lt (hB : Bounds B C) (hB0 : 0 ≤ B) {lam : ℕ} (hl : 1 ≤ lam) :
    kappa * √((AppHalfPieces.hOf lam : ℝ) - 1) < lam + B * logb 2 (AppHalfPieces.hOf lam) + C := by
  have h2 := (hOfSpec lam).1
  have h1 := hB.1 (AppHalfPieces.hOf lam - 1) (by omega)
  have h3 : logb 2 (p (AppHalfPieces.hOf lam - 1)) < lam := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast ClauseBound.Part.p_pos _), Real.rpow_natCast]
    exact_mod_cast p_pred_lt hl
  have h7 : ((AppHalfPieces.hOf lam - 1 : ℕ) : ℝ) = (AppHalfPieces.hOf lam : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hh0 : (2 : ℝ) ≤ AppHalfPieces.hOf lam := by exact_mod_cast h2
  rw [h7] at h1
  have h8 : logb 2 ((AppHalfPieces.hOf lam : ℝ) - 1) ≤ logb 2 (AppHalfPieces.hOf lam) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have h9 := mul_le_mul_of_nonneg_left h8 hB0
  linarith

/-- Hence h = O(λ²): log h grows more slowly than √(h−1). -/
theorem exists_hOf_le (hB : Bounds B C) : ∃ c₀ : ℕ, ∀ lam : ℕ, 1 ≤ lam → AppHalfPieces.hOf lam ≤ c₀ * lam ^ 2 := by
  have hκ := ClauseBound.Part.Bits.kappa_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 * |B| / Real.log 2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = D ^ 2 / (2 * kappa) + |B| + |C| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (1 + G) / kappa := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨⌈M ^ 2⌉₊ + 1, fun lam hl => ?_⟩
  have h2 := (hOfSpec lam).1
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = AppHalfPieces.hOf lam - 1 := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by omega
  have hE0 : (1 : ℝ) ≤ E := by exact_mod_cast hE1
  have h14 : ((AppHalfPieces.hOf lam : ℕ) : ℝ) = E + 1 := by
    rw [hE, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h1 := kappa_sqrt_pred_lt (bounds_abs hB) (abs_nonneg B) hl
  rw [h14, add_sub_cancel_right] at h1
  have h0 : logb 2 ((E : ℝ) + 1) ≤ 1 + logb 2 E := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) (show (E : ℝ) + 1 ≤ 2 * E by linarith)
    rwa [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at this
  have h0' := mul_le_mul_of_nonneg_left h0 (abs_nonneg B)
  have h3 := ClauseBound.Part.Bits.logb_le_sqrt_sqrt hE1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = √√(E : ℝ) := ⟨_, rfl⟩
  have hy2 : y ^ 2 = √(E : ℝ) := by rw [hy, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [← hy] at h3
  have h4 : |B| * Real.logb 2 E ≤ D * y := by
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg B)
    rw [hD]
    calc |B| * Real.logb 2 E ≤ |B| * (4 * y / Real.log 2) := this
      _ = 4 * |B| / Real.log 2 * y := by ring
  have h5 : D * y ≤ kappa * y ^ 2 / 2 + D ^ 2 / (2 * kappa) := by
    have h6 : kappa * y ^ 2 / 2 + D ^ 2 / (2 * kappa) - D * y = (kappa * y - D) ^ 2 / (2 * kappa) := by
      field_simp
      ring
    have h7 : 0 ≤ (kappa * y - D) ^ 2 / (2 * kappa) := by positivity
    linarith
  have h8 : kappa * √(E : ℝ) < 2 * (lam + G) := by
    rw [← hy2] at h1 ⊢
    rw [hG]
    linarith [le_abs_self C]
  have h9 : √(E : ℝ) < M * lam := by
    have h10 : 2 * (lam + G) ≤ 2 * (1 + G) * lam := by nlinarith
    have h11 : M * lam = 2 * (1 + G) * lam / kappa := by rw [hM]; ring
    rw [h11, lt_div_iff₀ hκ, mul_comm]
    linarith
  have h12 : (E : ℝ) < M ^ 2 * lam ^ 2 := by
    have h13 : (√(E : ℝ)) ^ 2 < (M * lam) ^ 2 := pow_lt_pow_left₀ h9 (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow] at h13
  have h15 : ((AppHalfPieces.hOf lam : ℕ) : ℝ) ≤ (((⌈M ^ 2⌉₊ + 1) * lam ^ 2 : ℕ) : ℝ) := by
    have h16 := Nat.le_ceil (M ^ 2)
    have h17 : (1 : ℝ) ≤ (lam : ℝ) ^ 2 := one_le_pow₀ hl0
    have h18 : M ^ 2 * (lam : ℝ) ^ 2 ≤ (⌈M ^ 2⌉₊ : ℝ) * (lam : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
    push_cast
    rw [h14]
    linarith
  exact_mod_cast h15

/-- κ√h ≤ κ√(h−1) + κ, for h ≥ 1. -/
theorem kappa_sqrt_le_pred {h : ℕ} (hh : 1 ≤ h) : kappa * √(h : ℝ) ≤ kappa * √((h : ℝ) - 1) + kappa := by
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h9 : √(h : ℝ) ≤ √((h : ℝ) - 1) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h10 := Real.sq_sqrt (show 0 ≤ (h : ℝ) - 1 by linarith)
    have h11 := Real.sqrt_nonneg ((h : ℝ) - 1)
    nlinarith
  have := mul_le_mul_of_nonneg_left h9 ClauseBound.Part.Bits.kappa_pos.le
  linarith

/-- And then κ√h ≤ κ√(h−1) + κ ≤ λ + O(log 2λ); on the way, log h = O(log 2λ). -/
theorem exists_kappa_sqrt_le (hB : Bounds B C) : ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ lam : ℕ, 1 ≤ lam →
    kappa * √(AppHalfPieces.hOf lam : ℝ) ≤ lam + c₁ * logb 2 (2 * lam) ∧ logb 2 (AppHalfPieces.hOf lam) ≤ c₂ * logb 2 (2 * lam) := by
  have hκ := ClauseBound.Part.Bits.kappa_pos
  obtain ⟨c₀, h0⟩ := exists_hOf_le hB
  have hc0 : 1 ≤ c₀ := by
    have h1 := h0 1 le_rfl
    have h2 := (hOfSpec 1).1
    omega
  have hc0' : (1 : ℝ) ≤ c₀ := by exact_mod_cast hc0
  have ha : 0 ≤ logb 2 c₀ := Real.logb_nonneg (by norm_num) hc0'
  refine ⟨|B| * (logb 2 c₀ + 2) + |C| + kappa, logb 2 c₀ + 2, by positivity, by positivity, fun lam hl => ?_⟩
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hx : 0 ≤ logb 2 lam := Real.logb_nonneg (by norm_num) hl0
  have hℓ : logb 2 (2 * lam) = 1 + logb 2 lam := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have h2 := (hOfSpec lam).1
  have h3 : logb 2 (AppHalfPieces.hOf lam) ≤ (logb 2 c₀ + 2) * logb 2 (2 * lam) := by
    have h4 : ((AppHalfPieces.hOf lam : ℕ) : ℝ) ≤ c₀ * (lam : ℝ) ^ 2 := by exact_mod_cast h0 lam hl
    have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h4
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow] at h5
    rw [hℓ]
    push_cast at h5
    nlinarith [mul_nonneg ha hx]
  refine ⟨?_, h3⟩
  have h6 := kappa_sqrt_pred_lt (bounds_abs hB) (abs_nonneg B) hl
  have h12 := kappa_sqrt_le_pred (h := AppHalfPieces.hOf lam) (by omega)
  have h13 : |B| * logb 2 (AppHalfPieces.hOf lam) ≤ |B| * ((logb 2 c₀ + 2) * logb 2 (2 * lam)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg B)
  have h14 : (1 : ℝ) ≤ logb 2 (2 * lam) := by rw [hℓ]; linarith
  have h15 : (|C| + kappa) * 1 ≤ (|C| + kappa) * logb 2 (2 * lam) := mul_le_mul_of_nonneg_left h14 (by positivity)
  nlinarith [le_abs_self C]

/-- p is nondecreasing, also on the integers. -/
theorem pZ_mono {E E' : ℤ} (h : E ≤ E') : pZ E ≤ pZ E' := by
  unfold pZ
  split_ifs
  · exact p_mono (by omega)
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

/-- As p is nondecreasing, R^row_s ≤ (2h+1)·p(2h+s). -/
theorem Rrow_le (h : ℕ) (s : ℤ) : Rrow h s ≤ (2 * h + 1) * pZ (2 * h + s) := by
  unfold Rrow
  refine (sum_le_card_nsmul _ _ (pZ (2 * h + s)) fun i hi => pZ_mono (by have := mem_range.1 hi; omega)).trans ?_
  rw [card_range, smul_eq_mul]

/-- As p is nondecreasing, R^col_s ≤ (2h+1)·p(2h−s). -/
theorem Rcol_le (h : ℕ) (s : ℤ) : Rcol h s ≤ (2 * h + 1) * pZ (2 * h - s) := by
  unfold Rcol
  refine (sum_le_card_nsmul _ _ (pZ (2 * h - s)) fun i _ => pZ_mono (by omega)).trans ?_
  rw [card_range, smul_eq_mul]

/-- √(2h+s) + √(2h−s) ≤ 2√(2h), for |s| ≤ 2h. -/
theorem sqrt_add_sqrt_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : √(2 * (h : ℝ) + s) + √(2 * (h : ℝ) - s) ≤ 2 * √(2 * (h : ℝ)) := by
  obtain ⟨a1, a2⟩ := abs_le.1 hs
  have b1 : -(2 * (h : ℝ)) ≤ s := by exact_mod_cast a1
  have b2 : (s : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast a2
  have e1 := Real.sq_sqrt (show 0 ≤ 2 * (h : ℝ) + s by linarith)
  have e2 := Real.sq_sqrt (show 0 ≤ 2 * (h : ℝ) - s by linarith)
  have e3 := Real.sq_sqrt (show 0 ≤ 2 * (h : ℝ) by positivity)
  have n1 := Real.sqrt_nonneg (2 * (h : ℝ) + s)
  have n2 := Real.sqrt_nonneg (2 * (h : ℝ) - s)
  have n3 := Real.sqrt_nonneg (2 * (h : ℝ))
  by_contra hc
  nlinarith [sq_nonneg (√(2 * (h : ℝ) + s) - √(2 * (h : ℝ) - s))]

/-- By display (46): if 1 ≤ r ≤ k·p(a), then log r ≤ log k + κ√a + C. -/
theorem logb_le_of_le_mul_p (hB : Bounds B C) {r k a : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (h : r ≤ k * p a) :
    logb 2 r ≤ logb 2 k + kappa * √(a : ℝ) + C := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < p a := by exact_mod_cast ClauseBound.Part.p_pos a
  have h1 : (r : ℝ) ≤ k * p a := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hr0 h1
  rw [Real.logb_mul hk0.ne' hp0.ne'] at h2
  linarith [hB.2 a]

/-- The display, first inequality: c^row_s + c^col_s ≤ 2√2·κ√h + 2·log(2h+1) + 2C + 2, for |s| ≤ 2h. -/
theorem bits_le (hB : Bounds B C) {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    ((Nat.clog 2 (Rrow h s) + Nat.clog 2 (Rcol h s) : ℕ) : ℝ) ≤ 2 * √2 * (kappa * √(h : ℝ)) + 2 * logb 2 (2 * (h : ℝ) + 1) + 2 * C + 2 := by
  obtain ⟨a1, a2⟩ := abs_le.1 hs
  have r1 : 1 ≤ Rrow h s := ClauseBound.Part.one_le_Rrow hs
  have r2 : 1 ≤ Rcol h s := ClauseBound.Part.one_le_Rcol hs
  have q1 : pZ (2 * h + s) = p (2 * (h : ℤ) + s).toNat := if_pos (by omega)
  have q2 : pZ (2 * h - s) = p (2 * (h : ℤ) - s).toNat := if_pos (by omega)
  have c1 : (((2 * (h : ℤ) + s).toNat : ℕ) : ℝ) = 2 * (h : ℝ) + s := by
    have : (((2 * (h : ℤ) + s).toNat : ℕ) : ℤ) = 2 * (h : ℤ) + s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have c2 : (((2 * (h : ℤ) - s).toNat : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
    have : (((2 * (h : ℤ) - s).toNat : ℕ) : ℤ) = 2 * (h : ℤ) - s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have h3 := ClauseBound.Part.Bits.clog_le r1 (logb_le_of_le_mul_p hB r1 (Nat.succ_pos _) (q1 ▸ Rrow_le h s))
  have h4 := ClauseBound.Part.Bits.clog_le r2 (logb_le_of_le_mul_p hB r2 (Nat.succ_pos _) (q2 ▸ Rcol_le h s))
  rw [c1] at h3
  rw [c2] at h4
  have h5 := mul_le_mul_of_nonneg_left (sqrt_add_sqrt_le hs) ClauseBound.Part.Bits.kappa_pos.le
  have h6 : √(2 * (h : ℝ)) = √2 * √(h : ℝ) := Real.sqrt_mul (by norm_num) _
  rw [h6] at h5
  push_cast at h3 h4 ⊢
  linarith

/-- The display, second inequality: 2√2·κ√h + 2·log(2h+1) + 2C + 2 ≤ 2√2·λ + O(log 2λ). -/
theorem exists_display_le (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    2 * √2 * (kappa * √(AppHalfPieces.hOf lam : ℝ)) + 2 * logb 2 (2 * (AppHalfPieces.hOf lam : ℝ) + 1) + 2 * C + 2 ≤ 2 * √2 * lam + c * logb 2 (2 * lam) := by
  obtain ⟨c₁, c₂, hc1, hc2, hcore⟩ := exists_kappa_sqrt_le hB
  refine ⟨⌈8 + 2 * c₂ + 2 * |C| + 2 * √2 * c₁⌉₊, fun lam hl => ?_⟩
  obtain ⟨h1, h2⟩ := hcore lam hl
  have hh := (hOfSpec lam).1
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hℓ : (1 : ℝ) ≤ logb 2 (2 * lam) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
    linarith [Real.logb_nonneg (b := 2) (by norm_num) hl0]
  have h6 := ClauseBound.Part.Bits.logb_succ_le (k := 2) (h := AppHalfPieces.hOf lam) (by norm_num) (by omega)
  have h8 : 2 * √2 * (kappa * √(AppHalfPieces.hOf lam : ℝ)) ≤ 2 * √2 * (lam + c₁ * logb 2 (2 * lam)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h9 := Nat.le_ceil (8 + 2 * c₂ + 2 * |C| + 2 * √2 * c₁)
  have h10 := mul_le_mul_of_nonneg_right h9 (zero_le_one.trans hℓ)
  have h11 : (8 + 2 * |C|) * 1 ≤ (8 + 2 * |C|) * logb 2 (2 * lam) := mul_le_mul_of_nonneg_left hℓ (by positivity)
  have h12 := le_abs_self C
  push_cast at h6
  nlinarith

/-- 4ρ = 2√2 for ρ = 1/√2. -/
theorem four_mul_rho : 4 * (1 / √(2 : ℝ)) = 2 * √2 := by
  rw [← Real.sqrt_div_self']
  ring

/-- The display as a whole, in the form of the definition of pieces with ρ = 1/√2: c^row_s + c^col_s
≤ 4ρλ + c·log 2λ. -/
theorem exists_bits_le (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∀ s : ℤ, |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ) →
    ((Nat.clog 2 (Rrow (AppHalfPieces.hOf lam) s) + Nat.clog 2 (Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam) := by
  obtain ⟨c, hc⟩ := exists_display_le hB
  exact ⟨c, fun lam hl s hs => by rw [four_mul_rho]; exact (bits_le hB hs).trans (hc lam hl)⟩

/-- By display (46): log Δ ≤ 2κ√h + log(4h+1) + C. -/
theorem logb_Delta_le (hB : Bounds B C) (h : ℕ) : logb 2 (Delta h) ≤ 2 * (kappa * √(h : ℝ)) + logb 2 (4 * (h : ℝ) + 1) + C := by
  have h4 : 1 ≤ Delta h :=
    (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have h5 := logb_le_of_le_mul_p hB h4 (Nat.succ_pos _) (Delta_le h)
  have h6 : √((4 * h : ℕ) : ℝ) = 2 * √(h : ℝ) := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h6] at h5
  push_cast at h5
  linarith

/-- log(2λ) ≤ λ. -/
theorem logb_two_mul_le {lam : ℕ} (hl : 1 ≤ lam) : logb 2 (2 * lam) ≤ lam := by
  have h0 : 2 * lam ≤ 2 ^ lam := by
    obtain ⟨k, rfl⟩ : ∃ k, lam = k + 1 := ⟨lam - 1, by omega⟩
    have := Nat.lt_two_pow_self (n := k)
    rw [pow_succ]
    omega
  have h1 : (0 : ℝ) < 2 * lam := by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith
  have h2 : logb 2 (2 * lam) ≤ logb 2 ((2 : ℝ) ^ lam) := Real.logb_le_logb_of_le (by norm_num) h1 (by exact_mod_cast h0)
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2

/-- So log Δ ≤ 2κ√h + O(log 2λ) = O(λ): Δ ≤ 2^{cλ} for a constant c. -/
theorem exists_Delta_le (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → Delta (AppHalfPieces.hOf lam) ≤ 2 ^ (c * lam) := by
  obtain ⟨c₁, c₂, hc1, hc2, hcore⟩ := exists_kappa_sqrt_le hB
  refine ⟨⌈5 + 2 * c₁ + c₂ + |C|⌉₊, fun lam hl => ?_⟩
  obtain ⟨h1, h2⟩ := hcore lam hl
  have hh := (hOfSpec lam).1
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hL := logb_two_mul_le hl
  have h3 := logb_Delta_le hB (AppHalfPieces.hOf lam)
  have h4 := ClauseBound.Part.Bits.logb_succ_le (k := 4) (h := AppHalfPieces.hOf lam) le_rfl (by omega)
  push_cast at h4
  have h5 : 1 ≤ Delta (AppHalfPieces.hOf lam) :=
    (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have h6 := Nat.le_ceil (5 + 2 * c₁ + c₂ + |C|)
  have h7 := mul_le_mul_of_nonneg_right h6 (zero_le_one.trans hl0)
  have h8 := mul_le_mul_of_nonneg_left hL hc1
  have h9 := mul_le_mul_of_nonneg_left hL hc2
  have h10 : (3 + |C|) * 1 ≤ (3 + |C|) * lam := mul_le_mul_of_nonneg_left hl0 (by positivity)
  refine ClauseBound.Part.Bits.le_two_pow_of_logb_le h5 h3 ?_
  push_cast
  nlinarith [le_abs_self C]

end GeneralPieces.Bits
