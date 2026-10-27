/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Num.PartAUse
public import ClauseBound.Alg.TopArith
public import ClauseBound.Gen.Seq
public import StepMachines.Prog.CountNet
public import StepMachines.Math.SatNet

/-! # The top level of part (c) of the theorem on the general recursion: the level and the display

The proof of part (c) in Appendix A, sentence by sentence, as far as it is arithmetic: K ≥ m^{1/90}
at the largest ℓ with K_ℓ ≤ m^{1/9};
the display «… ≤ 2ekm + O(km/K + K⁸ log K + K² log(km))»; and «every term after 2ekm is
O(k·m^{1−1/90})».
`top_level` collects the sentences for the schedule of the theorem, and `top_arith` draws from it
the inequality that the top level of this development asks for (the exponent is O(k·m·e_ℓ));
`stTopArith2` is that inequality for a general sequence of levels.

What differs from the text. The cost of the algorithm of this development is the exponent `needTop`
of a pad: the maximum of four budgets (g·(number of bits of K) for the search through the groupings,
P·(2g/K + 1) for a table entry, (K−1)·L for the arguments, and the exponent of the clique
algorithm), not the logarithm of a sum of products. The display is proved for
`needTop` (`needTop_le_display`), and `solver_terms_le` bounds its first two terms. The term
O(log(km)) of the text, which stands for factors polynomial in km, has no counterpart: such factors
are in the
polynomial running time in the length of the pad. L is `lamTopK` = ⌊1 + (2km + gP/K)/K²⌋, the text's
L with the bound 2km in place of U, where the text has U < 2km. The values have
absolute value at most 1 = 2⁰, whereas the text takes B = 1 (values below 2^B), so B' is P·(2g/K). -/

@[expose] public section

namespace GeneralPieces.TopDisplay

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA

/-! ## The level -/

/-- «By (a), K ≥ m^{1/90}»: if K_{ℓ+1} > m^{1/9} then m < K_ℓ^90. -/
theorem m_lt_pow (x₀ l m : ℕ) (hx : 1 ≤ x₀) (h : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 90 :=
  calc m < K x₀ (l + 1) ^ 9 := h
    _ ≤ (K x₀ l ^ 10) ^ 9 := Nat.pow_le_pow_left (K_lt_le x₀ l hx).2 9
    _ = K x₀ l ^ 90 := by rw [← pow_mul]

/-- m^{1/90} ≤ K if m ≤ K^90. -/
theorem root90_le (K m : ℕ) (h : m ≤ K ^ 90) : (m : ℝ) ^ (1 / 90 : ℝ) ≤ K := by
  have h1 : (m : ℝ) ≤ (K : ℝ) ^ 90 := by exact_mod_cast h
  calc (m : ℝ) ^ (1 / 90 : ℝ) ≤ ((K : ℝ) ^ 90) ^ (1 / 90 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = K := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

/-- «By (a), K ≥ m^{1/90}», for the largest ℓ with K_ℓ ≤ m^{1/9}. -/
theorem K_ge_root90 (x₀ l m : ℕ) (hx : 1 ≤ x₀) (h : m < K x₀ (l + 1) ^ 9) : (m : ℝ) ^ (1 / 90 : ℝ) ≤ K x₀ l :=
  root90_le _ _ (m_lt_pow x₀ l m hx h).le

/-! ## The display -/

section
variable {K k m : ℕ}

/-- K²·L ≤ K² + 2km + g·P/K: the text's K²·L ≤ U + 2ζgP + K² with ζ = 1/(2K) and U ≤ 2km. -/
theorem sq_L_le (hK : 2 ≤ K) : (K : ℝ) ^ 2 * lamTopK K (3 * K ^ 8) k m ≤
    (K : ℝ) ^ 2 + 2 * k * m + ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K := by
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hd : lamTopK K (3 * K ^ 8) k m * K ^ 3 ≤ K ^ 3 + K * (2 * k * m) + 3 * K ^ 8 * PtopK (3 * K ^ 8) k m := Nat.div_mul_le_self _ _
  have hd' : (lamTopK K (3 * K ^ 8) k m : ℝ) * (K : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 + K * (2 * k * m) + ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) := by
    exact_mod_cast hd
  generalize ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) = G at hd' ⊢
  refine le_of_mul_le_mul_right ?_ hκ
  have h1 : ((K : ℝ) ^ 2 + 2 * k * m + G / K) * K = (K : ℝ) ^ 3 + K * (2 * k * m) + G := by field_simp
  rw [h1]
  linarith

/-- K·(L + B') ≤ 32·km. -/
theorem arg_le_km (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    K * (lamTopK K (3 * K ^ 8) k m + PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) ≤ 32 * (k * m) := by
  have h1 : K * lamTopK K (3 * K ^ 8) k m ≤ 8 * (k * m) :=
    (Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) K)).trans (sq_mul_lam_le hK hk hm)
  have h2 : K * (PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) ≤ 15 * (k * m) :=
    calc K * (PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) = PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) * K := by ring
      _ ≤ PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) * K :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
      _ ≤ 15 * (k * m) := P_mul_le hK hk hm
  rw [Nat.mul_add]; omega

/-- log(km) ≥ 9. -/
theorem nine_le_log (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : (9 : ℝ) ≤ Real.logb 2 ((k : ℝ) * m) := by
  have h1 : 2 ^ 9 ≤ k * m :=
    calc 2 ^ 9 ≤ K ^ 9 := Nat.pow_le_pow_left hK 9
      _ ≤ m := hm
      _ ≤ k * m := Nat.le_mul_of_pos_left _ hk
  have := le_logb_of_pow_le (k * m) 9 h1
  push_cast at this
  exact this

/-- The first two terms of the display: e·K²·L + C₀·K²·log(K(L+B')) ≤ 2ekm + 5·km/K +
(2C₀+1)·K²·log(km), for 0 ≤ e ≤ 1. -/
theorem solver_terms_le (e : ℝ) (C₀ : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    e * (K : ℝ) ^ 2 * lamTopK K (3 * K ^ 8) k m +
      C₀ * (K : ℝ) ^ 2 * Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) ≤
    2 * e * k * m + 5 * ((k : ℝ) * m / K) + (2 * C₀ + 1) * ((K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) := by
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h9 := nine_le_log hK hk hm
  have hL := sq_L_le (k := k) (m := m) hK
  have hG : ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) ≤ 5 * ((k : ℝ) * m) := by exact_mod_cast g_mul_P_le hK hk hm
  have hG' : ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K ≤ 5 * ((k : ℝ) * m / K) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hG hκ.le
  have hkm : (0 : ℝ) < (k : ℝ) * m := by
    have : 0 < k * m := Nat.mul_pos hk (lt_of_lt_of_le (by positivity) hm)
    exact_mod_cast this
  -- the argument of the logarithm
  have harg : (K : ℝ) * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ)) ≤ 2 ^ 5 * ((k : ℝ) * m) := by
    have := arg_le_km hK hk hm
    exact_mod_cast this
  have hpos : 0 < (K : ℝ) * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ lamTopK K (3 * K ^ 8) k m := by exact_mod_cast one_le_lam (k := k) (m := m) hK
    positivity
  have hlog : Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) ≤
      2 * Real.logb 2 ((k : ℝ) * m) := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos harg
    have e5 : Real.logb 2 (2 ^ 5 * ((k : ℝ) * m)) = 5 + Real.logb 2 ((k : ℝ) * m) := by
      rw [Real.logb_mul (by positivity) hkm.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
    rw [e5] at h1
    linarith
  generalize Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) = X at hlog ⊢
  generalize ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K = G at hL hG'
  generalize (lamTopK K (3 * K ^ 8) k m : ℝ) = L at hL ⊢
  generalize Real.logb 2 ((k : ℝ) * m) = Y at h9 hlog ⊢
  have hq : 0 ≤ (k : ℝ) * m / K := by positivity
  generalize (k : ℝ) * m / K = q at hG' hq ⊢
  have hκ2 : 0 < (K : ℝ) ^ 2 := by positivity
  generalize (K : ℝ) ^ 2 = κ2 at hL hκ2 ⊢
  have hG0 : κ2 * L - 2 * k * m ≤ κ2 + 5 * q := by linarith
  have a1 : e * κ2 * L ≤ 2 * e * k * m + (κ2 + 5 * q) := by
    have h0 : 0 ≤ κ2 + 5 * q := by positivity
    have : e * (κ2 * L - 2 * k * m) ≤ 1 * (κ2 + 5 * q) := by
      rcases le_total 0 (κ2 * L - 2 * k * m) with hs | hs
      · exact mul_le_mul he1 hG0 hs (by norm_num)
      · have : e * (κ2 * L - 2 * k * m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0 hs
        linarith
    linarith
  have a2 : (C₀ : ℝ) * κ2 * X ≤ C₀ * κ2 * (2 * Y) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have a3 : κ2 * 1 ≤ κ2 * Y := mul_le_mul_of_nonneg_left (by linarith) hκ2.le
  nlinarith

end

/-- The display for the exponent of the algorithm of this development: at an index i with K⁹ ≤ m, 0
≤ e ≤ 1 and the bound of part (b),
`needTop` ≤ 2ekm + A·(km/K + K⁸·log K + K²·log(km)) with A = 2C₀ + 15. -/
theorem needTop_le_display {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hm : S.K i ^ 9 ≤ m)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + (2 * C₀ + 15 : ℕ) *
      ((k : ℝ) * m / S.K i + (S.K i : ℝ) ^ 8 * Real.logb 2 (S.K i) + (S.K i : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) := by
  unfold needTop
  have hr := hrate _ _ (one_le_lam (k := k) (m := m) hK) (one_le_B (k := k) (m := m) hK)
  generalize S.need (i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
    List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ()) = N at hr ⊢
  clear hrate
  generalize S.K i = K at *
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h9 := nine_le_log hK hk hm
  have h1 := solver_terms_le e C₀ he0 he1 hK hk hm
  have p0 : 0 ≤ 2 * e * k * m := by positivity
  have p1 : 0 ≤ (k : ℝ) * m / K := by positivity
  have p2 : 0 ≤ (K : ℝ) ^ 8 * Real.logb 2 K :=
    mul_nonneg (by positivity) (Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ K)))
  have p3 : 0 ≤ (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) := mul_nonneg (by positivity) (by linarith)
  have hC : (0 : ℝ) ≤ C₀ := by positivity
  have T1 : ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 6 * ((K : ℝ) ^ 8 * Real.logb 2 K) := by
    push_cast
    have := size_le_two_logb K hK
    have h8 : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 8 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have T2 : ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ 15 * ((k : ℝ) * m / K) := by
    rw [← mul_div_assoc, le_div_iff₀ hκ]
    exact_mod_cast P_mul_le hK hk hm
  have T3 : (((K - 1) * lamTopK K (3 * K ^ 8) k m : ℕ) : ℝ) ≤ 8 * ((k : ℝ) * m / K) := by
    rw [← mul_div_assoc, le_div_iff₀ hκ]
    have : (K - 1) * lamTopK K (3 * K ^ 8) k m * K ≤ 8 * (k * m) :=
      calc (K - 1) * lamTopK K (3 * K ^ 8) k m * K ≤ K * lamTopK K (3 * K ^ 8) k m * K :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        _ = K ^ 2 * lamTopK K (3 * K ^ 8) k m := by ring
        _ ≤ 8 * (k * m) := sq_mul_lam_le hK hk hm
    exact_mod_cast this
  have T4 := le_trans hr h1
  have q1 := mul_nonneg hC p1
  have q2 := mul_nonneg hC p2
  have q3 := mul_nonneg hC p3
  have hA : ((2 * C₀ + 15 : ℕ) : ℝ) = 2 * C₀ + 15 := by push_cast; ring
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_max, hA]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith

/-! ## Every term after 2ekm is O(k·m^{1−1/90}) -/

/-- log y ≤ 2y for y ≥ 1. -/
theorem logb_le_two_mul (y : ℝ) (hy : 1 ≤ y) : Real.logb 2 y ≤ 2 * y := by
  have h1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h3 : 0 < Real.log 2 := by linarith
  rw [Real.logb, div_le_iff₀ h3]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y) (sub_nonneg.mpr h2)]

/-- (m^{1/(9d)})^{9d} = m. -/
theorem root_pow (m d : ℕ) (hd : 1 ≤ d) : ((m : ℝ) ^ (1 / (9 * d : ℝ))) ^ (9 * d) = m := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have : 1 / (9 * (d : ℝ)) * ((9 * d : ℕ) : ℝ) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]

/-- m^{1−1/(9d)} = (m^{1/(9d)})^{9d−1}. -/
theorem root_pow_pred (m d : ℕ) (hd : 1 ≤ d) : (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)) = ((m : ℝ) ^ (1 / (9 * d : ℝ))) ^ (9 * d - 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  have : ((9 * d - 1 : ℕ) : ℝ) = 9 * d - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]; field_simp

/-- m^{1/(9d)} ≤ K if m ≤ K^{9d}. -/
theorem root_le (K m d : ℕ) (hd : 1 ≤ d) (h : m ≤ K ^ (9 * d)) : (m : ℝ) ^ (1 / (9 * d : ℝ)) ≤ K := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have h1 : (m : ℝ) ≤ (K : ℝ) ^ (9 * d) := by exact_mod_cast h
  calc (m : ℝ) ^ (1 / (9 * d : ℝ)) ≤ ((K : ℝ) ^ (9 * d)) ^ (1 / (9 * d : ℝ)) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = K := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have : ((9 * d : ℕ) : ℝ) * (1 / (9 * (d : ℝ))) = 1 := by push_cast; field_simp
        rw [this, Real.rpow_one]

/-- «… and every term after 2ekm is O(k·m^{1−1/90})», with any d ≥ 2 in place of 10: if m^{1/(9d)} ≤
K ≤ m^{1/9}, then with t = m^{1/(9d)} one has t ≤ K ≤ t^d, log K ≤ 2dt and
log(km) ≤ 2k + 18dt, so the three terms are at most 1, 2d and 2 + 18d times k·m^{1−1/(9d)}. -/
theorem terms_le_gen (K k m d : ℕ) (hK : 2 ≤ K) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : K ^ 9 ≤ m) (hm' : m ≤ K ^ (9 * d)) :
    (k : ℝ) * m / K ≤ k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)) ∧
    (K : ℝ) ^ 8 * Real.logb 2 K ≤ 2 * d * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) ∧
    (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) ≤ (2 + 18 * d) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) := by
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_pow _ _ (by omega)) hm
  have ht1 : 1 ≤ (m : ℝ) ^ (1 / (9 * d : ℝ)) := Real.one_le_rpow (by exact_mod_cast hm1) (by positivity)
  have htK := root_le K m d (by omega) hm'
  have h90 := root_pow m d (by omega)
  rw [root_pow_pred m d (by omega)]
  have hK9 : (K : ℝ) ^ 9 ≤ m := by exact_mod_cast hm
  generalize (m : ℝ) ^ (1 / (9 * d : ℝ)) = t at *
  rw [← h90] at hK9 ⊢
  have hκ1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd0 : (0 : ℝ) ≤ d := by positivity
  generalize (K : ℝ) = κ at *
  generalize (k : ℝ) = q at *
  have ht0 : 0 < t := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ10 : κ ≤ t ^ d := by
    have : κ ^ 9 ≤ (t ^ d) ^ 9 := by rw [← pow_mul, mul_comm d 9]; exact hK9
    exact (pow_le_pow_iff_left₀ hκ0.le (by positivity) (by norm_num)).mp this
  have hlt : Real.logb 2 t ≤ 2 * t := logb_le_two_mul t ht1
  have hlt0 : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) ht1
  have p81 : t ^ (d * 8 + 1) ≤ t ^ (9 * d - 1) := pow_le_pow_right₀ ht1 (by omega)
  have p20 : t ^ (d * 2) ≤ t ^ (9 * d - 1) := pow_le_pow_right₀ ht1 (by omega)
  have p21 : t ^ (d * 2 + 1) ≤ t ^ (9 * d - 1) := pow_le_pow_right₀ ht1 (by omega)
  have p89 : 0 < t ^ (9 * d - 1) := by positivity
  have e90 : t ^ (9 * d) = t ^ (9 * d - 1) * t := by rw [← pow_succ]; congr 1; omega
  have a2 : 1 * t ^ (9 * d - 1) ≤ q * t ^ (9 * d - 1) := mul_le_mul_of_nonneg_right hk1 p89.le
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hκ0, e90]
    have : t ^ (9 * d - 1) * t ≤ t ^ (9 * d - 1) * κ := mul_le_mul_of_nonneg_left htK p89.le
    have h2 : q * (t ^ (9 * d - 1) * t) ≤ q * (t ^ (9 * d - 1) * κ) := mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  · have h1 : Real.logb 2 κ ≤ 2 * d * t := by
      have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hκ0 hκ10
      rw [Real.logb_pow] at this
      have h3 : (d : ℝ) * Real.logb 2 t ≤ d * (2 * t) := mul_le_mul_of_nonneg_left hlt hd0
      linarith
    have h2 : κ ^ 8 ≤ t ^ (d * 8) := by
      calc κ ^ 8 ≤ (t ^ d) ^ 8 := pow_le_pow_left₀ hκ0.le hκ10 8
        _ = t ^ (d * 8) := by rw [← pow_mul]
    calc κ ^ 8 * Real.logb 2 κ ≤ t ^ (d * 8) * (2 * d * t) :=
          mul_le_mul h2 h1 (Real.logb_nonneg (by norm_num) hκ1) (by positivity)
      _ = 2 * d * t ^ (d * 8 + 1) := by ring
      _ ≤ 2 * d * (q * t ^ (9 * d - 1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have h1 : Real.logb 2 (q * t ^ (9 * d)) ≤ 2 * q + 18 * d * t := by
      rw [Real.logb_mul (by linarith) (by positivity), Real.logb_pow]
      push_cast
      have h3 : 9 * (d : ℝ) * Real.logb 2 t ≤ 9 * d * (2 * t) := mul_le_mul_of_nonneg_left hlt (by positivity)
      linarith [logb_le_two_mul q hk1]
    have h0 : 0 ≤ Real.logb 2 (q * t ^ (9 * d)) :=
      Real.logb_nonneg (by norm_num) (one_le_mul_of_one_le_of_one_le hk1 (one_le_pow₀ ht1))
    have h2 : κ ^ 2 ≤ t ^ (d * 2) := by
      calc κ ^ 2 ≤ (t ^ d) ^ 2 := pow_le_pow_left₀ hκ0.le hκ10 2
        _ = t ^ (d * 2) := by rw [← pow_mul]
    have a1 : q * t ^ (d * 2) ≤ q * t ^ (9 * d - 1) := mul_le_mul_of_nonneg_left p20 (by linarith)
    have a3 : (d : ℝ) * t ^ (d * 2 + 1) ≤ d * (q * t ^ (9 * d - 1)) := mul_le_mul_of_nonneg_left (by linarith) hd0
    calc κ ^ 2 * Real.logb 2 (q * t ^ (9 * d)) ≤ t ^ (d * 2) * (2 * q + 18 * d * t) := mul_le_mul h2 h1 h0 (by positivity)
      _ = 2 * (q * t ^ (d * 2)) + 18 * (d * t ^ (d * 2 + 1)) := by ring
      _ ≤ (2 + 18 * d) * (q * t ^ (9 * d - 1)) := by linarith

/-- «… and every term after 2ekm is O(k·m^{1−1/90})», for m^{1/90} ≤ K ≤ m^{1/9}. -/
theorem terms_le (K k m : ℕ) (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) (hm' : m ≤ K ^ 90) :
    (k : ℝ) * m / K ≤ k * (m : ℝ) ^ (1 - 1 / 90 : ℝ) ∧
    (K : ℝ) ^ 8 * Real.logb 2 K ≤ 20 * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) ∧
    (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) ≤ 182 * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by
  have h := terms_le_gen K k m 10 hK hk (by norm_num) hm hm'
  have e1 : (1 - 1 / (9 * ((10 : ℕ) : ℝ))) = (1 - 1 / 90 : ℝ) := by norm_num
  have e2 : (2 * ((10 : ℕ) : ℝ)) = 20 := by norm_num
  have e3 : (2 + 18 * ((10 : ℕ) : ℝ)) = 182 := by norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The exponent of the algorithm of this development is at most 2ekm + A'·k·m^{1−1/(9d)} with A' =
(3 + 20d)·(2C₀ + 15), at an index with m^{1/(9d)} ≤ K ≤ m^{1/9}. -/
theorem needTop_le_main_gen {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m d : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ (9 * d))
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + ((3 + 20 * d) * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) := by
  have h := needTop_le_display S i e C₀ k m he0 he1 hK hk hm hrate
  obtain ⟨t1, t2, t3⟩ := terms_le_gen (S.K i) k m d hK hk hd hm hm'
  have hA : (0 : ℝ) ≤ ((2 * C₀ + 15 : ℕ) : ℝ) := by positivity
  have h2 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3) hA
  have h3 : (((3 + 20 * d) * (2 * C₀ + 15) : ℕ) : ℝ) = (3 + 20 * d) * ((2 * C₀ + 15 : ℕ) : ℝ) := by push_cast; ring
  rw [h3]
  linarith

/-- The exponent of the algorithm of this development is at most 2ekm + A'·k·m^{1−1/90} with A' =
203·(2C₀ + 15), at an index with m^{1/90} ≤ K ≤ m^{1/9}. -/
theorem needTop_le_main {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ 90)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + (203 * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by
  have h := needTop_le_display S i e C₀ k m he0 he1 hK hk hm hrate
  obtain ⟨t1, t2, t3⟩ := terms_le (S.K i) k m hK hk hm hm'
  have hA : (0 : ℝ) ≤ ((2 * C₀ + 15 : ℕ) : ℝ) := by positivity
  have h2 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3) hA
  have h3 : ((203 * (2 * C₀ + 15) : ℕ) : ℝ) = 203 * ((2 * C₀ + 15 : ℕ) : ℝ) := by push_cast; ring
  rw [h3]
  linarith

/-! ## The exponent is O(k·m·e) -/

/-- (log t)ⁿ ≤ n!·2ⁿ·t for real t ≥ 1. -/
theorem logb_pow_le_real (t : ℝ) (ht : 1 ≤ t) (n : ℕ) : Real.logb 2 t ^ n ≤ (n.factorial * 2 ^ n : ℕ) * t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 := Real.pow_div_factorial_le_exp (Real.log t) hlog n
  rw [Real.exp_log ht0] at h1
  have h2 : Real.log t ^ n ≤ n.factorial * t := by rwa [div_le_iff₀' (by positivity)] at h1
  have h3 : Real.logb 2 t ≤ 2 * Real.log t := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h2' : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have h4 : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) ht
  calc Real.logb 2 t ^ n ≤ (2 * Real.log t) ^ n := pow_le_pow_left₀ h4 h3 n
    _ = 2 ^ n * Real.log t ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (n.factorial * t) := by gcongr
    _ = (n.factorial * 2 ^ n : ℕ) * t := by push_cast; ring

/-- m^{−1/(9d)} is small against e: if K ≤ t^d and e ≥ (log K)^{−C₀}, then 1 ≤
d^{C₀}·C₀!·2^{C₀}·e·t. -/
theorem one_le_mul_root (K C₀ d : ℕ) (t e : ℝ) (ht : 1 ≤ t) (hK : 2 ≤ K) (hKt : (K : ℝ) ≤ t ^ d) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) :
    1 ≤ ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) * e * t := by
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hL : 0 < Real.logb 2 K ^ C₀ := by positivity
  have he1 : 1 ≤ e * Real.logb 2 K ^ C₀ := (div_le_iff₀ hL).1 he
  have he0 : 0 ≤ e := le_trans (by positivity) he
  have h2 : Real.logb 2 K ≤ d * Real.logb 2 t := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hκ hKt
    rwa [Real.logb_pow] at this
  have h3 : Real.logb 2 K ^ C₀ ≤ (d : ℝ) ^ C₀ * ((C₀.factorial * 2 ^ C₀ : ℕ) * t) :=
    calc Real.logb 2 K ^ C₀ ≤ (d * Real.logb 2 t) ^ C₀ := pow_le_pow_left₀ (by linarith) h2 C₀
      _ = (d : ℝ) ^ C₀ * Real.logb 2 t ^ C₀ := mul_pow _ _ _
      _ ≤ (d : ℝ) ^ C₀ * ((C₀.factorial * 2 ^ C₀ : ℕ) * t) := mul_le_mul_of_nonneg_left (logb_pow_le_real t ht C₀) (by positivity)
  calc (1 : ℝ) ≤ e * Real.logb 2 K ^ C₀ := he1
    _ ≤ e * ((d : ℝ) ^ C₀ * ((C₀.factorial * 2 ^ C₀ : ℕ) * t)) := mul_le_mul_of_nonneg_left h3 he0
    _ = ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) * e * t := by push_cast; ring

/-- The constant of `needTop_le_kme` and of `top_arith`. -/
def Atop (C₀ d : ℕ) : ℕ := 2 + (3 + 20 * d) * (2 * C₀ + 15) * (d ^ C₀ * (C₀.factorial * 2 ^ C₀))

/-- The end of the proof of the first sentence of part (c): an exponent X ≤ 2ekm + A'·k·m^{1−1/(9d)}
is O(k·m·e), because e ≥ (log K)^{−C₀}, K ≤ m^{1/9}, and m^{−1/(9d)} is smaller than any power of
1/log m, up to a
constant. (The text compares both terms with km/(log m)^{α'}; the top level of this development asks
for a multiple of k·m·e.) -/
theorem kme_of_main (K C₀ k m d A' : ℕ) (e X : ℝ) (hK : 2 ≤ K) (hd : 1 ≤ d) (hm : K ^ 9 ≤ m) (he : 1 / Real.logb 2 K ^ C₀ ≤ e)
    (h : X ≤ 2 * e * k * m + (A' : ℝ) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)))) :
    X ≤ ((2 + A' * (d ^ C₀ * (C₀.factorial * 2 ^ C₀)) : ℕ) : ℝ) * k * m * e := by
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_pow _ _ (by omega)) hm
  have ht1 : 1 ≤ (m : ℝ) ^ (1 / (9 * d : ℝ)) := Real.one_le_rpow (by exact_mod_cast hm1) (by positivity)
  have h90 := root_pow m d hd
  have hK9 : (K : ℝ) ^ 9 ≤ m := by exact_mod_cast hm
  rw [root_pow_pred m d hd] at h
  generalize (m : ℝ) ^ (1 / (9 * d : ℝ)) = t at *
  have hκ0 : (0 : ℝ) ≤ K := by positivity
  have hKt : (K : ℝ) ≤ t ^ d := by
    have : (K : ℝ) ^ 9 ≤ (t ^ d) ^ 9 := by rw [← pow_mul, mul_comm d 9, h90]; exact hK9
    exact (pow_le_pow_iff_left₀ hκ0 (by positivity) (by norm_num)).mp this
  have hB := one_le_mul_root K C₀ d t e ht1 hK hKt he
  have e90 : t ^ (9 * d) = t ^ (9 * d - 1) * t := by rw [← pow_succ]; congr 1; omega
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hBc] at hB
  have hp : 0 ≤ (k : ℝ) * t ^ (9 * d - 1) := by positivity
  have h5 : (k : ℝ) * t ^ (9 * d - 1) ≤ Bc * (k * m * e) :=
    calc (k : ℝ) * t ^ (9 * d - 1) = k * t ^ (9 * d - 1) * 1 := (mul_one _).symm
      _ ≤ k * t ^ (9 * d - 1) * (Bc * e * t) := mul_le_mul_of_nonneg_left hB hp
      _ = Bc * (k * (t ^ (9 * d - 1) * t) * e) := by ring
      _ = Bc * (k * m * e) := by rw [← e90, h90]
  have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg A' : (0 : ℝ) ≤ A')
  have h7 : ((2 + A' * (d ^ C₀ * (C₀.factorial * 2 ^ C₀)) : ℕ) : ℝ) = 2 + (A' : ℝ) * Bc := by rw [hBc]; push_cast; ring
  rw [h7]
  linarith

/-- The same for the exponent of the algorithm of this development, at an index with m^{1/(9d)} ≤ K
≤ m^{1/9}. -/
theorem needTop_le_kme {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m d : ℕ) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ (9 * d)) (he : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ (Atop C₀ d : ℕ) * k * m * e := by
  have h1 : (1 : ℝ) ≤ Real.logb 2 (S.K i) := by simpa using le_logb_of_pow_le (S.K i) 1 (by simpa using hK)
  have he0 : 0 ≤ e := le_trans (by positivity) he
  exact kme_of_main (S.K i) C₀ k m d _ e _ hK (by omega) hm he (needTop_le_main_gen S i e C₀ k m d he0 he1 hK hk hd hm hm' hrate)

/-- Part (c) as an inequality, in the form that the top level of this development asks for
(`ClauseBound.Alg.StTopArith`), proved through the display: with ℓ the level picked for m, the
exponent is at most A·k·m·e_ℓ.
For a general sequence of levels K_{ℓ+1} ≤ K_ℓ^{C₀} takes the place of K_{ℓ+1} ≤ K_ℓ^{10}, so d =
max(C₀, 2) takes the place of 10. -/
theorem stTopArith2 : StTopArith := by
  intro Idx _ S e C₀ Q
  refine ⟨Atop C₀ (max C₀ 2), fun k m hk hm => ?_⟩
  obtain ⟨hr1, hr2⟩ := root9_spec m
  have hK0 : S.K (Q.idx 0) ≤ (root9 m).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 9
    exact absurd (h'.trans hm) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root9 m)
  have hidx := Q.pick_idx (root9 m)
  rw [hidx] at hle ⊢
  refine needTop_le_kme S _ _ C₀ k m (max C₀ 2) (Q.e_le _) (Q.K_two _) hk (le_max_right _ _) ((Nat.pow_le_pow_left hle 9).trans hr1) ?_
    (Q.e_ge _) (Q.rate _)
  have h2 := Q.K_two (Q.pick (root9 m)).1.length
  calc m ≤ ((root9 m).length + 1) ^ 9 := hr2.le
    _ ≤ (S.K (Q.idx (Q.pick (root9 m)).1.length) ^ C₀) ^ 9 := Nat.pow_le_pow_left ((Nat.succ_le_of_lt hmax).trans (Q.K_le _)) 9
    _ = S.K (Q.idx (Q.pick (root9 m)).1.length) ^ (9 * C₀) := by rw [← pow_mul, mul_comm]
    _ ≤ S.K (Q.idx (Q.pick (root9 m)).1.length) ^ (9 * max C₀ 2) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (le_max_left _ _))

/-! ## The top level for the schedule of the theorem -/

/-- The proof of part (c) up to its display, for the algorithm of this development with the schedule
K_ℓ, e_ℓ and any x₀ ≥ 18. Given parts (a) and (b) in the form of a sequence of indices Q, and m ≥
K₀⁹, let ℓ be
the level that the algorithm picks for m. Then K_ℓ ≤ m^{1/9} < K_{ℓ+1} (it is the largest such ℓ),
K_ℓ ≥ m^{1/90}, the exponent is at most
2·e_ℓ·k·m + A·(km/K_ℓ + K_ℓ⁸·log K_ℓ + K_ℓ²·log(km)), and at most 2·e_ℓ·k·m + 203·A·k·m^{1−1/90},
where A = 2C₀ + 15. -/
theorem top_level (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (Q : (solverOf P).Seq (e ρ x₀) C₀)
    (hQ : ∀ l, Q.idx l = idx P x₀ l) (k m : ℕ) (hk : 1 ≤ k) (hm : K x₀ 0 ^ 9 ≤ m) :
    K x₀ (Q.pick (root9 m)).1.length ^ 9 ≤ m ∧ m < K x₀ ((Q.pick (root9 m)).1.length + 1) ^ 9 ∧
    (m : ℝ) ^ (1 / 90 : ℝ) ≤ K x₀ (Q.pick (root9 m)).1.length ∧
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ 2 * e ρ x₀ (Q.pick (root9 m)).1.length * k * m + (2 * C₀ + 15 : ℕ) *
      ((k : ℝ) * m / K x₀ (Q.pick (root9 m)).1.length +
        (K x₀ (Q.pick (root9 m)).1.length : ℝ) ^ 8 * Real.logb 2 (K x₀ (Q.pick (root9 m)).1.length) +
        (K x₀ (Q.pick (root9 m)).1.length : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) ∧
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ 2 * e ρ x₀ (Q.pick (root9 m)).1.length * k * m +
      (203 * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by
  have hKi : ∀ l, (solverOf P).K (Q.idx l) = K x₀ l := fun l => by rw [hQ]; exact Seq.topK_idx P x₀ l
  obtain ⟨hr1, hr2⟩ := root9_spec m
  have hK0 : (solverOf P).K (Q.idx 0) ≤ (root9 m).length := by
    rw [hKi]
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 9
    exact absurd (h'.trans hm) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root9 m)
  have hidx := Q.pick_idx (root9 m)
  rw [hidx, hKi] at hle
  rw [hKi] at hmax
  rw [hidx]
  generalize (Q.pick (root9 m)).1.length = l at *
  have h1 : K x₀ l ^ 9 ≤ m := (Nat.pow_le_pow_left hle 9).trans hr1
  have h2 : m < K x₀ (l + 1) ^ 9 := lt_of_lt_of_le hr2 (Nat.pow_le_pow_left (Nat.succ_le_of_lt hmax) 9)
  have h3 := m_lt_pow x₀ l m (by omega) h2
  have hρ0 : 0 < ρ := by linarith
  have he0 : 0 ≤ e ρ x₀ l := (by positivity : 0 ≤ 1 / 2 * ρ ^ l).trans (e_ge_half_pow ρ x₀ l hρ)
  have hK2 : 2 ≤ (solverOf P).K (Q.idx l) := Q.K_two l
  have d1 := needTop_le_display (solverOf P) (Q.idx l) (e ρ x₀ l) C₀ k m he0 (Q.e_le l) hK2 hk (by rw [hKi]; exact h1) (Q.rate l)
  have d2 := needTop_le_main (solverOf P) (Q.idx l) (e ρ x₀ l) C₀ k m he0 (Q.e_le l) hK2 hk (by rw [hKi]; exact h1)
    (by rw [hKi]; exact h3.le) (Q.rate l)
  rw [hKi] at d1
  exact ⟨h1, h2, K_ge_root90 x₀ l m (by omega) h2, d1, d2⟩

/-- Part (c) as an inequality for the schedule of the theorem, from `top_level`: with ℓ the level
picked for m ≥ K₀⁹, the exponent, at most 2·e_ℓ·k·m + O(k·m^{1−1/90}), is at most
`Atop C₀ 10`·k·m·e_ℓ. This is what the top level in m is given for the schedule;
`stTopArith2` is the same for a general sequence of levels. -/
theorem top_arith (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (Q : (solverOf P).Seq (e ρ x₀) C₀)
    (hQ : ∀ l, Q.idx l = idx P x₀ l) (k m : ℕ) (hk : 1 ≤ k) (hm : K x₀ 0 ^ 9 ≤ m) :
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ (Atop C₀ 10 : ℕ) * k * m * e ρ x₀ (Q.pick (root9 m)).1.length := by
  obtain ⟨h1, -, -, -, h5⟩ := top_level P ρ x₀ C₀ hρ hx Q hQ k m hk hm
  have hKi : (solverOf P).K (Q.idx (Q.pick (root9 m)).1.length) = K x₀ (Q.pick (root9 m)).1.length := by rw [hQ]; exact Seq.topK_idx P x₀ _
  have hK2 := Q.K_two (Q.pick (root9 m)).1.length
  have he := Q.e_ge (Q.pick (root9 m)).1.length
  rw [hKi] at hK2 he
  have e1 : (1 - 1 / 90 : ℝ) = 1 - 1 / (9 * ((10 : ℕ) : ℝ)) := by norm_num
  rw [e1] at h5
  exact kme_of_main _ C₀ k m 10 (203 * (2 * C₀ + 15)) _ _ hK2 (by norm_num) h1 he h5

end GeneralPieces.TopDisplay
