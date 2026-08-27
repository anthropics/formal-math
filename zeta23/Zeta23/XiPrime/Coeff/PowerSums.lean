/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/PowerSums.lean — Σ_{N ≤ e^u} f(N)/N for Dirichlet powers f = Λ^{∗m}.

  Sdiv f u := Σ_{N ≤ e^u} f(N)/N.
  Recursion (from Coeff/Swap):      Sdiv (g ∗ f) u = Σ_{d ≤ e^u} g(d)/d · Sdiv f (u − log d).
  Chebyshev–Mertens upper bound:    Sdiv (Λ^{∗m}) u ≤ (u + m·K)^m / m!      (u ≥ 0; K = log 4 + 4),
by induction on m, each step being Coeff/Abel.mertens_step applied to the decreasing polynomial
v ↦ (u + mK − v)^m/m!  ([XF′ Remark 7.2]: "M_j(u) ≤ (u+2jC)^j/j! by induction from Mertens").
-/
import Zeta23.XiPrime.Coeff.Basic
import Zeta23.XiPrime.Coeff.Abel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega
open Finset Real MeasureTheory

noncomputable section

namespace Zeta23
namespace XiPrime

/-- Sdiv f u := Σ_{N ≤ e^u} f(N)/N. -/
def Sdiv (f : ArithmeticFunction ℝ) (u : ℝ) : ℝ := ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, f N / N

lemma Sdiv_nonneg {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (u : ℝ) : 0 ≤ Sdiv f u :=
  sum_nonneg fun N _ => div_nonneg (hf N) (Nat.cast_nonneg N)

lemma one_le_floor_exp {u : ℝ} (hu : 0 ≤ u) : 1 ≤ ⌊Real.exp u⌋₊ :=
  Nat.le_floor (by simpa using Real.one_le_exp hu)

lemma log_le_of_mem_Ioc_floor_exp {u : ℝ} {d : ℕ} (hd : d ∈ Ioc 0 ⌊Real.exp u⌋₊) :
    Real.log d ≤ u := by
  have hd0 : 0 < d := (mem_Ioc.mp hd).1
  have hdx : (d : ℝ) ≤ Real.exp u :=
    (Nat.cast_le.mpr (mem_Ioc.mp hd).2).trans (Nat.floor_le (Real.exp_pos u).le)
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hd0)).mpr hdx

lemma log_nonneg_of_mem_Ioc {X : ℕ} {d : ℕ} (_hd : d ∈ Ioc 0 X) : 0 ≤ Real.log d :=
  Real.log_natCast_nonneg d

lemma floor_exp_div (u : ℝ) {d : ℕ} (hd : 0 < d) :
    ⌊Real.exp u⌋₊ / d = ⌊Real.exp (u - Real.log d)⌋₊ := by
  rw [← Nat.floor_div_natCast, Real.exp_sub, Real.exp_log (by exact_mod_cast hd)]

/-- Sdiv δ u = 1 for u ≥ 0. -/
lemma Sdiv_one {u : ℝ} (hu : 0 ≤ u) : Sdiv 1 u = 1 := by
  unfold Sdiv
  have h1 : (1:ℕ) ∈ Ioc 0 ⌊Real.exp u⌋₊ := Finset.mem_Ioc.mpr ⟨one_pos, one_le_floor_exp hu⟩
  rw [sum_eq_single_of_mem 1 h1]
  · simp
  · intro b _ hb
    simp [ArithmeticFunction.one_apply_ne hb]

/-- the recursion  Sdiv (g∗f) u = Σ_{d ≤ e^u} g(d)/d · Sdiv f (u − log d). -/
lemma Sdiv_mul (g f : ArithmeticFunction ℝ) (u : ℝ) :
    Sdiv (g * f) u = ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, g d / d * Sdiv f (u - Real.log d) := by
  unfold Sdiv
  simp_rw [div_eq_mul_inv]
  rw [sum_Ioc_mul_apply g f (fun N => ((N : ℕ) : ℝ)⁻¹)]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (mem_Ioc.mp hd).1
  rw [← floor_exp_div u hd0, mul_assoc, mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [Nat.cast_mul, mul_inv]
  ring

/-- the polynomial-with-shift integral:  ∫₀ᵘ (c − v)^n dv = (c^{n+1} − (c−u)^{n+1})/(n+1). -/
lemma integral_const_sub_pow (c u : ℝ) (n : ℕ) :
    ∫ v in (0:ℝ)..u, (c - v) ^ n = (c ^ (n + 1) - (c - u) ^ (n + 1)) / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun v => v ^ n) c, integral_pow]
  simp

/-- binomial inequality  a^{m+1} + (m+1)·a^m·b ≤ (a+b)^{m+1}  for a, b ≥ 0. -/
lemma pow_add_mul_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ m : ℕ, a ^ (m + 1) + (m + 1) * a ^ m * b ≤ (a + b) ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
      have ih := pow_add_mul_pow_le ha hb m
      have hab : 0 ≤ a + b := add_nonneg ha hb
      have ham : 0 ≤ a ^ m := pow_nonneg ha m
      have key : a ^ (m + 1) ≤ (a + b) ^ (m + 1) := pow_le_pow_left₀ ha (by linarith) _
      calc a ^ (m + 1 + 1) + (↑(m + 1) + 1) * a ^ (m + 1) * b
          = a * (a ^ (m + 1) + (m + 1) * a ^ m * b) + a ^ (m + 1) * b := by push_cast; ring
        _ ≤ a * (a + b) ^ (m + 1) + (a + b) ^ (m + 1) * b :=
            add_le_add (mul_le_mul_of_nonneg_left ih ha) (mul_le_mul_of_nonneg_right key hb)
        _ = (a + b) ^ (m + 1 + 1) := by ring

/-- **Chebyshev–Mertens bound for the Dirichlet powers:**  Σ_{N ≤ e^u} Λ^{∗m}(N)/N ≤ (u + mK)^m/m!. -/
theorem Sdiv_lamPow_le : ∀ (m : ℕ) {u : ℝ}, 0 ≤ u →
    Sdiv (Λ ^ m) u ≤ (u + m * KM) ^ m / m.factorial
  | 0, u, hu => by simp [Sdiv_one hu]
  | m + 1, u, hu => by
      set c : ℝ := u + m * KM with hc
      have hcu : 0 ≤ c - u := by rw [hc]; nlinarith [KM_nonneg, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      have hc0 : 0 ≤ c := by linarith
      -- the comparison polynomial f(v) = (c − v)^m / m!  and its derivative
      set f : ℝ → ℝ := fun v => (c - v) ^ m / m.factorial with hf
      set f' : ℝ → ℝ := fun v => -(m * (c - v) ^ (m - 1)) / m.factorial with hf'
      have hderiv : ∀ v ∈ Set.Icc 0 u, HasDerivAt f (f' v) v := by
        intro v _
        have h := (((hasDerivAt_id v).const_sub c).fun_pow m).div_const (m.factorial : ℝ)
        exact h.congr_deriv (by simp only [hf', id_eq]; ring)
      have hf'c : ContinuousOn f' (Set.Icc 0 u) := by
        simp only [hf']
        fun_prop
      -- step 1: recursion + induction hypothesis inside the sum
      have hrec : Sdiv (Λ ^ (m + 1)) u ≤ ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d * f (Real.log d) := by
        rw [pow_succ', Sdiv_mul]
        refine sum_le_sum fun d hd => ?_
        have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd
        have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
        have ih := Sdiv_lamPow_le m (u := u - Real.log d) (by linarith)
        simp only [hf]
        exact ih.trans_eq (by rw [hc]; ring)
      -- step 2: Mertens step for f
      have hstep := mertens_step hu hderiv hf'c
      have hint_f : ∫ v in (0:ℝ)..u, f v = (c ^ (m + 1) - (c - u) ^ (m + 1)) / ((m + 1) * m.factorial) := by
        simp only [hf]
        rw [intervalIntegral.integral_div, integral_const_sub_pow]
        field_simp
      have hfu : |f u| = (c - u) ^ m / m.factorial := by
        simp only [hf]
        rw [abs_of_nonneg (div_nonneg (pow_nonneg hcu m) (Nat.cast_nonneg _))]
      have hint_f' : ∫ v in (0:ℝ)..u, |f' v| = (c ^ m - (c - u) ^ m) / m.factorial := by
        -- |f'(v)| = m (c−v)^{m−1}/m! on [0,u]  (c − v ≥ 0 there)
        have heq : ∀ v ∈ Set.uIcc 0 u, |f' v| = (m * (c - v) ^ (m - 1)) / m.factorial := by
          intro v hv
          rw [Set.uIcc_of_le hu] at hv
          have hcv : 0 ≤ c - v := by linarith [hv.2]
          simp only [hf', neg_div, abs_neg]
          exact abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hcv _)) (Nat.cast_nonneg _))
        rw [intervalIntegral.integral_congr heq]
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp
        · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_const_sub_pow]
          push_cast
          field_simp
      -- step 3: combine  Σ ≤ ∫f + K(|f u| + ∫|f'|) = (c^{m+1} − (c−u)^{m+1})/(m+1)! + K c^m/m! ≤ (c+K)^{m+1}/(m+1)!
      have hsum_le : ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d * f (Real.log d)
          ≤ (∫ v in (0:ℝ)..u, f v) + KM * (|f u| + ∫ v in (0:ℝ)..u, |f' v|) := by
        have := (abs_sub_le_iff.mp (le_of_eq rfl |>.trans hstep)).1
        linarith
      have hfact : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hmf : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
      calc Sdiv (Λ ^ (m + 1)) u
          ≤ (∫ v in (0:ℝ)..u, f v) + KM * (|f u| + ∫ v in (0:ℝ)..u, |f' v|) := hrec.trans hsum_le
        _ = (c ^ (m + 1) - (c - u) ^ (m + 1)) / ((m + 1) * m.factorial) + KM * (c ^ m / m.factorial) := by
            rw [hint_f, hfu, hint_f']; ring
        _ ≤ c ^ (m + 1) / ((m + 1) * m.factorial) + KM * (c ^ m / m.factorial) := by
            gcongr
            · linarith [pow_nonneg hcu (m + 1)]
        _ = (c ^ (m + 1) + (m + 1) * c ^ m * KM) / ((m + 1) * m.factorial) := by
            field_simp
        _ ≤ (c + KM) ^ (m + 1) / ((m + 1) * m.factorial) := by
            gcongr
            exact pow_add_mul_pow_le hc0 KM_nonneg m
        _ = (u + ↑(m + 1) * KM) ^ (m + 1) / (m + 1).factorial := by
            rw [hfact, hc]; push_cast; ring

/-- monotonicity in u of Sdiv for f ≥ 0. -/
lemma Sdiv_mono {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) : Monotone (Sdiv f) := by
  intro a b hab
  unfold Sdiv
  refine sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl (Nat.floor_le_floor ?_)) ?_
  · exact Real.exp_le_exp.mpr hab
  · exact fun N _ _ => div_nonneg (hf N) (Nat.cast_nonneg N)

/-- the Mertens bound itself in Sdiv form: Sdiv Λ u ≤ u + K. -/
lemma Sdiv_lam_le {u : ℝ} (hu : 0 ≤ u) : Sdiv Λ u ≤ u + KM := by
  simpa using Sdiv_lamPow_le 1 hu

end XiPrime
end Zeta23
