/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Num.PartA
public import ClauseBound.Alg.TopArith

/-! # What the proofs of parts (b) and (c) of Theorem A take from part (a)

After its proof, Appendix A uses the bounds of part (a) on K_ℓ and e_ℓ in these sentences: in the
proof of part (b), «by the induction hypothesis and e ≤ 1»; in the proof of part (c), «by (a), K ≥
m^{1/90} and e = O((log m)^{−α'})» at the largest ℓ with
K_ℓ ≤ m^{1/9}; and, at the end of that proof, «e_ℓ ≥ ρ^ℓ/2 ≥ 2^{−ℓ−1} ≥ 1/log K_ℓ». Each is a named
theorem here, with the small consequences that the programs of this development need besides. All
are drawn from the four assertions of part (a): a hypothesis
`hA : TheoremAa ρ x₀`, or `PartA.thmRunningTime_a` itself in `e_le_rPow` and `e_mul_le`; only
`one_le_e_mul_K` also uses a sentence of the proof of part (a), K_ℓ ≥ 2^{18(ℓ+1)}. (The formula for
log K_{ℓ+1} is also used where case (ii) of Lemma 8
is shown to apply.) `e_le_rPow` is «e = O((log m)^{−α'})» in the form that the proof of the bound in
m uses, with log(m + 2) for log m; the last section has what the proof of the bound in n (Theorem D)
uses. -/

public section

namespace GeneralPieces.PartAUse

open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA

variable {ρ : ℝ} {x₀ : ℕ}

/-! ## The numbers K_ℓ -/

/-- K_ℓ ≥ 2, because K_ℓ < K_ℓ^10. -/
theorem two_le_K (hA : TheoremAa ρ x₀) (l : ℕ) : 2 ≤ K x₀ l := by
  have h := lt_of_lt_of_le (hA.K_lt_le l).1 (hA.K_lt_le l).2
  by_contra hc
  have h3 : K x₀ l = 0 ∨ K x₀ l = 1 := by omega
  rcases h3 with h3 | h3 <;> rw [h3] at h <;> norm_num at h

/-- log K_ℓ ≥ 2^{ℓ+1} for x₀ ≥ 2, by the formula for log K_ℓ. -/
theorem two_pow_le_logK (hA : TheoremAa ρ x₀) (hx : 2 ≤ x₀) (l : ℕ) : (2 : ℝ) ^ (l + 1) ≤ Real.logb 2 (K x₀ l) := by
  have h1 : ((l + 1 : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := Nat.cast_le.2 Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx
  have h3 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  push_cast at h1
  have h4 : 0 ≤ (3 * (x₀ : ℝ) - 2) * ((2 : ℝ) ^ l - 1) := mul_nonneg (by linarith) (by linarith)
  rw [hA.logK, pow_succ]
  nlinarith

/-! ## The numbers e_ℓ -/

/-- e_ℓ ≥ 0, by e_ℓ ≥ ρ^ℓ/2. -/
theorem e_nonneg (hA : TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (l : ℕ) : 0 ≤ e ρ x₀ l :=
  le_trans (by positivity) (hA.e_bounds l).1

/-- Proof of part (b), «by the induction hypothesis and e ≤ 1»: e_ℓ ≤ 0.85·ρ^ℓ ≤ 1. -/
theorem e_le_one (hA : TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (l : ℕ) : e ρ x₀ l ≤ 1 := by
  have h1 := (hA.e_bounds l).2
  have h2 : ρ ^ l ≤ 1 := pow_le_one₀ hρ hρ1
  linarith

/-- End of the proof of part (c), «e_ℓ ≥ ρ^ℓ/2 ≥ 2^{−ℓ−1}». -/
theorem inv_two_pow_le_e (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (l : ℕ) : 1 / (2 : ℝ) ^ (l + 1) ≤ e ρ x₀ l := by
  have h1 : (1 / 2 : ℝ) ^ l ≤ ρ ^ l := pow_le_pow_left₀ (by norm_num) hρ l
  have h2 : 1 / (2 : ℝ) ^ (l + 1) = 1 / 2 * (1 / 2) ^ l := by rw [pow_succ, one_div_pow]; field_simp
  rw [h2]
  linarith [(hA.e_bounds l).1]

/-- e_ℓ·K_ℓ ≥ 1, by e_ℓ ≥ 2^{−ℓ−1} and the sentence «K_ℓ ≥ 2^{18(ℓ+1)}» of the proof of part (a). -/
theorem one_le_e_mul_K (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (l : ℕ) : 1 ≤ e ρ x₀ l * K x₀ l := by
  have h1 : 2 ^ (l + 1) ≤ 2 ^ (18 * (l + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (l + 1) ≤ K x₀ l := by exact_mod_cast h1.trans (K_ge_pow x₀ l hx)
  calc (1 : ℝ) = 1 / 2 ^ (l + 1) * 2 ^ (l + 1) := by field_simp
    _ ≤ e ρ x₀ l * K x₀ l := mul_le_mul (inv_two_pow_le_e hA hρ l) h2 (by positivity) (e_nonneg hA (by linarith) l)

/-- «… 2^{−ℓ−1} ≥ 1/log K_ℓ», so e_ℓ ≥ 1/log K_ℓ. -/
theorem inv_logK_le_e (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 2 ≤ x₀) (l : ℕ) : 1 / Real.logb 2 (K x₀ l) ≤ e ρ x₀ l :=
  le_trans (one_div_le_one_div_of_le (by positivity) (two_pow_le_logK hA hx l)) (inv_two_pow_le_e hA hρ l)

/-- The same with a power of the logarithm, the form in which a sequence of levels asks for it: e_ℓ
≥ 1/(log K_ℓ)^C for C ≥ 1. -/
theorem inv_logK_pow_le_e (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 2 ≤ x₀) (l C : ℕ) (hC : 1 ≤ C) :
    1 / Real.logb 2 (K x₀ l) ^ C ≤ e ρ x₀ l := by
  have h1 : (1 : ℝ) ≤ Real.logb 2 (K x₀ l) := le_trans (one_le_pow₀ (by norm_num)) (two_pow_le_logK hA hx l)
  exact le_trans (one_div_le_one_div_of_le (by linarith) (le_self_pow₀ h1 (by omega))) (inv_logK_le_e hA hρ hx l)

/-! ## The level picked for m -/

/-- Proof of part (c), «by (a), K ≥ m^{1/90}»: if K_{ℓ+1} > m^{1/9} then m < K_ℓ^90, by K_{ℓ+1} ≤
K_ℓ^10. -/
theorem lt_pow_ninety (hA : TheoremAa ρ x₀) {l m : ℕ} (h : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 90 :=
  calc m < K x₀ (l + 1) ^ 9 := h
    _ ≤ (K x₀ l ^ 10) ^ 9 := Nat.pow_le_pow_left (hA.K_lt_le l).2 9
    _ = K x₀ l ^ 90 := by rw [← pow_mul]

/-- «… and e = O((log m)^{−α'})»: if 0 < y ≤ d·log K_ℓ then e_ℓ ≤ 0.85·ρ^ℓ ≤ 0.85·(d·(3x₀+6)/y)^{α'}.
The text has y = log m and d = 90. -/
theorem e_le_of_log_le (hA : TheoremAa ρ x₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d)
    (h : y ≤ d * Real.logb 2 (K x₀ l)) : e ρ x₀ l ≤ 0.85 * (d * (3 * x₀ + 6) / y) ^ Real.logb 2 (1 / ρ) := by
  have hα : 0 ≤ Real.logb 2 (1 / ρ) := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hρ]; linarith)
  have hlK : 0 < Real.logb 2 (K x₀ l) := by
    by_contra hc
    have := mul_nonneg hd (neg_nonneg.2 (not_lt.1 hc))
    linarith
  have h3 : (3 * (x₀ : ℝ) + 6) / Real.logb 2 (K x₀ l) ≤ d * (3 * x₀ + 6) / y := by
    rw [div_le_div_iff₀ hlK hy]
    have : (0 : ℝ) ≤ 3 * x₀ + 6 := by positivity
    nlinarith
  have h4 := Real.rpow_le_rpow (div_nonneg (by positivity) hlK.le) h3 hα
  linarith [(hA.e_bounds l).2, hA.rho_pow l]

/-- The same without the power on the constant: if 1 ≤ y ≤ d·log K_ℓ for an integer d ≥ 1, then e_ℓ
≤ d·(3x₀+6)/y^{α'}, because α' ≤ 1. -/
theorem e_le_div_rpow (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {l d : ℕ} {y : ℝ} (hd : 1 ≤ d) (hy : 1 ≤ y)
    (h : y ≤ d * Real.logb 2 (K x₀ l)) : e ρ x₀ l ≤ ((d * (3 * x₀ + 6) : ℕ) : ℝ) / y ^ Real.logb 2 (1 / ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have ha1 : Real.logb 2 (1 / ρ) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]
    linarith
  have h3 := e_le_of_log_le hA hρ0 hρ1.le (by linarith) (Nat.cast_nonneg d) h
  generalize Real.logb 2 (1 / ρ) = α at *
  have hc : (1 : ℝ) ≤ ((d * (3 * x₀ + 6) : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd (by omega)
  have hcc : (d : ℝ) * (3 * x₀ + 6) = ((d * (3 * x₀ + 6) : ℕ) : ℝ) := by push_cast; ring
  rw [hcc] at h3
  generalize ((d * (3 * x₀ + 6) : ℕ) : ℝ) = a at *
  have h6 : (a / y) ^ α = a ^ α / y ^ α := Real.div_rpow (by linarith) (by linarith) α
  have h7 : a ^ α ≤ a := by
    calc a ^ α ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc ha1
      _ = a := Real.rpow_one _
  have hyα : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
  have h8 : a ^ α / y ^ α ≤ a / y ^ α := div_le_div_of_nonneg_right h7 hyα.le
  have h9 : 0 ≤ a ^ α / y ^ α := div_nonneg (Real.rpow_nonneg (by linarith) _) hyα.le
  rw [h6] at h3
  linarith

/-- If M ≤ K_ℓ^d then log M ≤ d·log K_ℓ. -/
theorem log_le_of_le_pow {l d : ℕ} {M : ℝ} (hM : 0 < M) (h : M ≤ (K x₀ l : ℝ) ^ d) : Real.logb 2 M ≤ d * Real.logb 2 (K x₀ l) := by
  have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hM h
  rwa [Real.logb_pow] at this

/-- If ⌊m^{1/9}⌋ < K_{ℓ+1} then m + 2 ≤ K_ℓ^91. -/
theorem add_two_le_pow (hA : TheoremAa ρ x₀) {l m : ℕ} (h : (root9 m).length < K x₀ (l + 1)) : m + 2 ≤ K x₀ l ^ 91 := by
  have h1 : m < K x₀ l ^ 90 := lt_pow_ninety hA (lt_of_lt_of_le (root9_spec m).2 (Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 9))
  have h2 : K x₀ l ^ 91 = K x₀ l ^ 90 * K x₀ l := pow_succ _ _
  have h3 : K x₀ l ^ 90 * 2 ≤ K x₀ l ^ 90 * K x₀ l := Nat.mul_le_mul_left _ (two_le_K hA l)
  omega

/-- «e = O((log m)^{−α'})» in the form that the proof of the bound in m uses: if ⌊m^{1/9}⌋ < K_{ℓ+1}
then e_ℓ ≤ 91·(3x₀+6)/(log(m+2))^{α'}. The proof is from part (a) as proved
in `Num/PartA.lean`. -/
theorem e_le_rPow {l m : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (h : (root9 m).length < K x₀ (l + 1)) :
    e ρ x₀ l ≤ ((91 * (3 * x₀ + 6) : ℕ) : ℝ) * SatM.rPow (Real.logb 2 (1 / ρ)) m := by
  have hA := thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hy : (1 : ℝ) ≤ Real.logb 2 ((m : ℝ) + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num
  have h1 : (m : ℝ) + 2 ≤ (K x₀ l : ℝ) ^ 91 := by exact_mod_cast add_two_le_pow hA h
  have h2 := e_le_div_rpow hA hρ hρ1 (by norm_num : 1 ≤ 91) hy (log_le_of_le_pow (by positivity) h1)
  unfold SatM.rPow
  rwa [mul_one_div]

/-! ## The level picked for n

The second sentence of part (c) of Theorem A rests on Theorem D, whose «hypothesis holds by (a) and
(b)». The proof of the bound in n in this development asks for integers s(ℓ) with 2^{−s(ℓ)} ≤ e_ℓ
and 2^{s(ℓ)} ≤ (2/e_ℓ)^{O(1)}, in place of the text's number
between 0.85·ρ^ℓ and ρ^ℓ; s(ℓ) = ℓ + 1 will do, by `inv_two_pow_le_e` and `two_pow_le_div`. -/

/-- 2^{ℓ+1} ≤ (2/e_ℓ)^{C+1} if ρ^C ≤ 1/2, by e_ℓ ≤ 0.85·ρ^ℓ ≤ ρ^ℓ. -/
theorem two_pow_le_div (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {C : ℕ} (hC : ρ ^ C ≤ 1 / 2) (l : ℕ) :
    (2 : ℝ) ^ (l + 1) ≤ (2 / e ρ x₀ l) ^ (C + 1) := by
  have hρ0 : 0 < ρ := by linarith
  have hpl : 0 < ρ ^ l := by positivity
  have he0 : 0 < e ρ x₀ l := lt_of_lt_of_le (by positivity) (hA.e_bounds l).1
  have he1 : e ρ x₀ l ≤ ρ ^ l := by linarith [(hA.e_bounds l).2]
  have h2 : 2 / ρ ^ l ≤ 2 / e ρ x₀ l := div_le_div_of_nonneg_left (by norm_num) he0 he1
  have hC1 : ρ ^ (C + 1) ≤ 1 / 2 := by
    calc ρ ^ (C + 1) = ρ ^ C * ρ := pow_succ _ _
      _ ≤ ρ ^ C * 1 := mul_le_mul_of_nonneg_left hρ1.le (by positivity)
      _ ≤ 1 / 2 := by rw [mul_one]; exact hC
  have h3 : (2 : ℝ) ^ l * (ρ ^ (C + 1)) ^ l ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by nlinarith)
  have h4 : (2 : ℝ) ≤ 2 ^ (C + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
      _ ≤ 2 ^ (C + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : 0 < (ρ ^ (C + 1)) ^ l := by positivity
  calc (2 : ℝ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    _ ≤ 2 ^ (C + 1) * (1 / (ρ ^ (C + 1)) ^ l) := by
        refine mul_le_mul h4 ?_ (by positivity) (by positivity)
        rw [le_div_iff₀ hq]
        exact h3
    _ = (2 / ρ ^ l) ^ (C + 1) := by
        rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (C + 1) l]
        ring
    _ ≤ (2 / e ρ x₀ l) ^ (C + 1) := pow_le_pow_left₀ (by positivity) h2 _

/-- If n < K_{ℓ+1}^17 then n + 4 ≤ K_ℓ^171, by K_{ℓ+1} ≤ K_ℓ^10. -/
theorem add_four_le_pow (hA : TheoremAa ρ x₀) {l n : ℕ} (hlt : n < K x₀ (l + 1) ^ 17) : n + 4 ≤ K x₀ l ^ 171 := by
  have h1 : K x₀ (l + 1) ^ 17 ≤ (K x₀ l ^ 10) ^ 17 := Nat.pow_le_pow_left (hA.K_lt_le l).2 17
  have h2 : (K x₀ l ^ 10) ^ 17 = K x₀ l ^ 170 := by rw [← pow_mul]
  have h3 : K x₀ l ^ 171 = K x₀ l ^ 170 * K x₀ l := pow_succ _ _
  have h4 : 2 ^ 170 ≤ K x₀ l ^ 170 := Nat.pow_le_pow_left (two_le_K hA l) 170
  have h5 : K x₀ l ^ 170 * 2 ≤ K x₀ l ^ 170 * K x₀ l := Nat.mul_le_mul_left _ (two_le_K hA l)
  have h6 : 4 ≤ 2 ^ 170 := by norm_num
  omega

/-- At the level picked for n, that is K_ℓ^17 ≤ n < K_{ℓ+1}^17: e_ℓ·(ℓ + 2) ≤ 3·171·(3x₀+6)·log
log(n+4)/(log(n+4))^{α'}. Here log(n+4) ≤ 171·log K_ℓ bounds e_ℓ, and 2^ℓ ≤ log K_ℓ ≤ log(n+4)
bounds ℓ. -/
theorem e_mul_le {l n : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (hle : K x₀ l ^ 17 ≤ n) (hlt : n < K x₀ (l + 1) ^ 17) :
    e ρ x₀ l * (((l + 1 : ℕ) : ℝ) + 1) ≤
      ((3 * (171 * (3 * x₀ + 6)) : ℕ) : ℝ) * (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) / Real.logb 2 ((n : ℝ) + 4) ^ Real.logb 2 (1 / ρ)) := by
  have hA := thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy : (2 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 4) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_two]
    linarith
  have h1 : (n : ℝ) + 4 ≤ (K x₀ l : ℝ) ^ 171 := by exact_mod_cast add_four_le_pow hA hlt
  have hyx := log_le_of_le_pow (by positivity) h1
  have hK : (0 : ℝ) < K x₀ l := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_K hA l)
  have hxy : Real.logb 2 (K x₀ l) ≤ Real.logb 2 ((n : ℝ) + 4) := by
    have h2 : K x₀ l ≤ n + 4 := ((Nat.le_self_pow (by norm_num) _).trans hle).trans (Nat.le_add_right _ _)
    exact Real.logb_le_logb_of_le (by norm_num) hK (by exact_mod_cast h2)
  have he := e_le_div_rpow hA hρ hρ1 (by norm_num : 1 ≤ 171) (by linarith) hyx
  have h2l : (2 : ℝ) ^ l ≤ Real.logb 2 ((n : ℝ) + 4) := by
    have h3 : (2 : ℝ) ^ l ≤ 2 ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ l)
    exact (h3.trans (two_pow_le_logK hA (by omega) l)).trans hxy
  generalize Real.logb 2 ((n : ℝ) + 4) = y at *
  have hlz : (l : ℝ) ≤ Real.logb 2 y := by
    rwa [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
  have hz : (1 : ℝ) ≤ Real.logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
    exact hy
  generalize Real.logb 2 y = z at *
  generalize Real.logb 2 (1 / ρ) = α at *
  have hyα : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
  have hl2 : ((l + 1 : ℕ) : ℝ) + 1 ≤ 3 * z := by push_cast; linarith
  calc e ρ x₀ l * (((l + 1 : ℕ) : ℝ) + 1) ≤ (((171 * (3 * x₀ + 6) : ℕ) : ℝ) / y ^ α) * (3 * z) :=
        mul_le_mul he hl2 (by positivity) (by positivity)
    _ = ((3 * (171 * (3 * x₀ + 6)) : ℕ) : ℝ) * (z / y ^ α) := by push_cast; ring

end GeneralPieces.PartAUse
