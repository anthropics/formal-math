/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/
import Zeta23.PrimeSideB.PPKernel

/-!
# [prop:PP] — the off-diagonal term 𝒪₁ (§5.4)

Consumed by `Zeta23/PrimeSideB/PP.lean` .  Everything needed is in
`Zeta23/PrimeSideB/PPKernel.lean`:
* `sub_mul_Aminus_eq` : for θ = y−y' ≠ 0,  θ·A⁻(y,y') = explicit combination of 8 terms
    trig(θ·cT)·M(y or y'),  trig ∈ {sin,cos}, c ∈ {1,2}, M ∈ {Cp,Sp,Cm,Sm} (half-line moments of Φ²);
* `abs_Cp_le` … `abs_Sm_le` : |M(y)| ≤ ∫Φ²;
* `MV_real` : |Σ_{n≠m} u_n v_m trig(c(y_n−y_m))/(y_n−y_m)| ≤ C·√(Σ2n u_n²)·√(Σ2n v_n²)  (H-MV + [eq:deltan]);
* `MV_size_le` : with {u,v} = {a, a·w}, |w| ≤ W:  that bound ≤ 2·C·W·Σ_{n≤X}Λ(n)².
So: split the sum below into the 8 MV-shaped sums (after dividing `sub_mul_Aminus_eq` by θ = log n − log m,
nonzero for n ≠ m ≥ 1 by injectivity of log), bound each by 2·C·(∫Φ²)·ΣΛ², total 16·C·(∫Φ²)·ΣΛ².
(Then PP.lean uses [eq:cheb1] ΣΛ(n)² ≪ X log X = XL and ∫Φ² = 2πbL ≤ 2πL to get 𝒪₁ ≪ L²X.)
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-- **[prop:PP], 𝒪₁** (§5.4, "Hence |𝒪₁| ≪ L²X" — here in the pre-Chebyshev form):
for T ≥ 0, continuous Φ with Φ² integrable, and H-MV with constant C ≥ 0,
  |Σ_{n≠m≤X} a_n a_m A⁻(log n, log m)| ≤ 16·C·(∫_ℝ Φ²)·Σ_{n≤X} Λ(n)².
(A⁻ = `Aminus`, the difference-frequency half of 𝓜[cos(·y_n),cos(·y_m)], see PPKernel.) -/
theorem O1_bound {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) {Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))|
      ≤ 16 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  set Λ2 : ℝ := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  -- the eight MV-shaped sums (u/v/c/trig as in sub_mul_Aminus_eq, divided by θ)
  set S1 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    (fun k => acoef k * Cm Φ T (Real.log k)) n * acoef m
      * Real.sin ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS1
  set S2 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    (fun k => acoef k * Sm Φ T (Real.log k)) n * acoef m
      * Real.cos ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS2
  set S3 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Cm Φ T (Real.log k)) m
      * Real.sin (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS3
  set S4 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Sm Φ T (Real.log k)) m
      * Real.cos (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS4
  set S5 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Cp Φ T (Real.log k)) m
      * Real.sin ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS5
  set S6 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Sp Φ T (Real.log k)) m
      * Real.cos ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS6
  set S7 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    (fun k => acoef k * Cp Φ T (Real.log k)) n * acoef m
      * Real.sin (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS7
  set S8 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    (fun k => acoef k * Sp Φ T (Real.log k)) n * acoef m
      * Real.cos (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS8
  -- split the target into the eight sums
  have hsplit : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))
      = S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8 := by
    rw [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    by_cases hnm : n = m
    · simp [hnm]
    · simp only [if_neg hnm]
      have hθ : Real.log n - Real.log m ≠ 0 := by
        have hn1 := one_le_of_mem_primeRange hn
        have hm1 := one_le_of_mem_primeRange hm
        have hinj : Real.log n ≠ Real.log m := by
          rcases lt_or_gt_of_ne hnm with hlt | hgt
          · exact ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt))
          · exact ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt))
        exact sub_ne_zero.mpr hinj
      have hA := sub_mul_Aminus_eq (Φ := Φ) hT hΦ hθ
      have hAm : Aminus Φ T (Real.log n) (Real.log m)
          = ((Real.sin ((Real.log n - Real.log m) * (2 * T)) * Cm Φ T (Real.log n)
              + Real.cos ((Real.log n - Real.log m) * (2 * T)) * Sm Φ T (Real.log n)
              - (Real.sin ((Real.log n - Real.log m) * T) * Cm Φ T (Real.log m)
                + Real.cos ((Real.log n - Real.log m) * T) * Sm Φ T (Real.log m)))
            + (Real.sin ((Real.log n - Real.log m) * (2 * T)) * Cp Φ T (Real.log m)
              + Real.cos ((Real.log n - Real.log m) * (2 * T)) * Sp Φ T (Real.log m)
              - (Real.sin ((Real.log n - Real.log m) * T) * Cp Φ T (Real.log n)
                + Real.cos ((Real.log n - Real.log m) * T) * Sp Φ T (Real.log n))))
            / (Real.log n - Real.log m) := by
        rw [eq_div_iff hθ]
        rw [mul_comm]
        exact hA
      rw [hAm, mul_comm ((2 : ℝ) * T) (Real.log n - Real.log m),
        mul_comm T (Real.log n - Real.log m)]
      field_simp
      ring
  -- bound each sum via H-MV + the moment bounds
  have hw_Cm : ∀ n ∈ primeRange X, |Cm Φ T (Real.log n)| ≤ W := fun n _ => abs_Cm_le hT hΦ hΦ2 _
  have hw_Sm : ∀ n ∈ primeRange X, |Sm Φ T (Real.log n)| ≤ W := fun n _ => abs_Sm_le hT hΦ hΦ2 _
  have hw_Cp : ∀ n ∈ primeRange X, |Cp Φ T (Real.log n)| ≤ W := fun n _ => abs_Cp_le hT hΦ hΦ2 _
  have hw_Sp : ∀ n ∈ primeRange X, |Sp Φ T (Real.log n)| ≤ W := fun n _ => abs_Sp_le hT hΦ hΦ2 _
  have hb1 : |S1| ≤ 2 * C * W * Λ2 := by
    rw [hS1]
    refine le_trans ((MV_real hMV X (2 * T)
      (fun k => acoef k * Cm Φ T (Real.log k)) acoef).2) ?_
    exact (MV_size_le hC X hW0 hw_Cm).2
  have hb2 : |S2| ≤ 2 * C * W * Λ2 := by
    rw [hS2]
    refine le_trans ((MV_real hMV X (2 * T)
      (fun k => acoef k * Sm Φ T (Real.log k)) acoef).1) ?_
    exact (MV_size_le hC X hW0 hw_Sm).2
  have hb3 : |S3| ≤ 2 * C * W * Λ2 := by
    rw [hS3]
    refine le_trans ((MV_real hMV X T
      acoef (fun k => acoef k * Cm Φ T (Real.log k))).2) ?_
    exact (MV_size_le hC X hW0 hw_Cm).1
  have hb4 : |S4| ≤ 2 * C * W * Λ2 := by
    rw [hS4]
    refine le_trans ((MV_real hMV X T
      acoef (fun k => acoef k * Sm Φ T (Real.log k))).1) ?_
    exact (MV_size_le hC X hW0 hw_Sm).1
  have hb5 : |S5| ≤ 2 * C * W * Λ2 := by
    rw [hS5]
    refine le_trans ((MV_real hMV X (2 * T)
      acoef (fun k => acoef k * Cp Φ T (Real.log k))).2) ?_
    exact (MV_size_le hC X hW0 hw_Cp).1
  have hb6 : |S6| ≤ 2 * C * W * Λ2 := by
    rw [hS6]
    refine le_trans ((MV_real hMV X (2 * T)
      acoef (fun k => acoef k * Sp Φ T (Real.log k))).1) ?_
    exact (MV_size_le hC X hW0 hw_Sp).1
  have hb7 : |S7| ≤ 2 * C * W * Λ2 := by
    rw [hS7]
    refine le_trans ((MV_real hMV X T
      (fun k => acoef k * Cp Φ T (Real.log k)) acoef).2) ?_
    exact (MV_size_le hC X hW0 hw_Cp).2
  have hb8 : |S8| ≤ 2 * C * W * Λ2 := by
    rw [hS8]
    refine le_trans ((MV_real hMV X T
      (fun k => acoef k * Sp Φ T (Real.log k)) acoef).1) ?_
    exact (MV_size_le hC X hW0 hw_Sp).2
  -- assemble
  rw [hsplit]
  have habs : |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := by
    have t1 := abs_add_le S1 S2
    have t2 := abs_sub (S1 + S2) S3
    have t3 := abs_sub (S1 + S2 - S3) S4
    have t4 := abs_add_le (S1 + S2 - S3 - S4) S5
    have t5 := abs_add_le (S1 + S2 - S3 - S4 + S5) S6
    have t6 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6) S7
    have t7 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6 - S7) S8
    linarith
  calc |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := habs
    _ ≤ 8 * (2 * C * W * Λ2) := by linarith
    _ = 16 * C * W * Λ2 := by ring

end PrimeSide
end Zeta23
