/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Part.Rec

/-! # p(E) ≤ exp(π·√(2E/3))

Induction on E through the recurrence E·p(E) = Σ_{v,k ≥ 1, kv ≤ E} v·p(E − kv), the method of Erdős.
Let c = π·√(2/3) and a = c/(2√E). By √(E − x) ≤ √E − x/(2√E) and the
induction hypothesis, p(E − kv) ≤ exp(c√E)·exp(−akv). For y > 0 we have Σ_{v ≥ 1} v·e^{−yv} =
e^{−y}/(1 − e^{−y})² ≤ 1/y², and Σ_{k ≥ 1} 1/(ak)² = (π²/6)/a² = E. -/

public section

namespace ClauseBound.Part

open Finset Partitions

namespace Upper

/-- c = π·√(2/3) is positive. -/
theorem cHR_pos : 0 < cHR := by
  unfold cHR
  positivity

/-- c² = 2π²/3. -/
theorem cHR_sq : cHR ^ 2 = 2 * Real.pi ^ 2 / 3 := by
  rw [cHR, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

/-- √(n − x) ≤ √n − x/(2√n) for x ≤ n. -/
theorem sqrt_sub_le {n x : ℝ} (hn : 0 < n) (hx : x ≤ n) : Real.sqrt (n - x) ≤ Real.sqrt n - x / (2 * Real.sqrt n) := by
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have h1 : x / (2 * Real.sqrt n) ≤ Real.sqrt n / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  have h2 : (Real.sqrt n - x / (2 * Real.sqrt n)) ^ 2 = n - x + (x / (2 * Real.sqrt n)) ^ 2 := by
    rw [sub_sq, hss]
    field_simp
  rw [h2]
  nlinarith [sq_nonneg (x / (2 * Real.sqrt n))]

/-- e^{−y}/(1 − e^{−y})² ≤ 1/y² for y > 0. -/
theorem exp_div_le {y : ℝ} (hy : 0 < y) : Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 ≤ 1 / y ^ 2 := by
  have hq : 0 < Real.exp (-(y / 2)) := Real.exp_pos _
  have hr : Real.exp (-y) = Real.exp (-(y / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hone : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsinh : y / 2 ≤ (Real.exp (y / 2) - Real.exp (-(y / 2))) / 2 := by
    rw [← Real.sinh_eq]
    exact Real.self_le_sinh_iff.2 (by positivity)
  have h1 : y * Real.exp (-(y / 2)) ≤ 1 - Real.exp (-(y / 2)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsinh hq.le
    nlinarith
  have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  rw [div_le_div_iff₀ (by have : 0 < 1 - Real.exp (-y) := by linarith
                          positivity) (by positivity), one_mul, hr]
  calc Real.exp (-(y / 2)) ^ 2 * y ^ 2 = (y * Real.exp (-(y / 2))) ^ 2 := by ring
    _ ≤ (1 - Real.exp (-(y / 2)) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2

/-- Σ_v v·e^{−yv} ≤ 1/y² over any finite set of v, for y > 0. -/
theorem sum_mul_exp_le {y : ℝ} (hy : 0 < y) (s : Finset ℕ) : ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) ≤ 1 / y ^ 2 := by
  have hr0 : 0 < Real.exp (-y) := Real.exp_pos _
  have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := Real.exp (-y)) (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have h1 : ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) = ∑ v ∈ s, (v : ℝ) * Real.exp (-y) ^ v := by
    refine sum_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [h1]
  exact (sum_le_hasSum s (fun _ _ => by positivity) hsum).trans (exp_div_le hy)

/-- Σ_k 1/k² ≤ π²/6 over any finite set of k. -/
theorem sum_inv_sq_le (s : Finset ℕ) : ∑ k ∈ s, 1 / (k : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum s (fun _ _ => by positivity) hasSum_zeta_two

end Upper

open Upper

/-- p(E) ≤ exp(π·√(2E/3)). -/
theorem p_le_exp (E : ℕ) : (p E : ℝ) ≤ Real.exp (cHR * Real.sqrt E) := by
  induction E using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [p_zero]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := cHR_pos
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hn'
  have hss : s ^ 2 = n := hs ▸ Real.sq_sqrt hn'.le
  obtain ⟨a, ha⟩ : ∃ a, a = cHR / (2 * s) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  rw [← hs]
  have hterm : ∀ v ∈ Icc 1 n, ∀ k ∈ Icc 1 (n / v),
      (v : ℝ) * (p (n - k * v) : ℝ) ≤ Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) := by
    intro v hv k hk
    have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have hkv : k * v ≤ n := (Nat.le_div_iff_mul_le hv1).1 (mem_Icc.1 hk).2
    have hpos : 0 < k * v := Nat.mul_pos hk1 hv1
    have h1 := ih (n - k * v) (by omega)
    have h2 : Real.sqrt ((n - k * v : ℕ) : ℝ) ≤ s - (k * v : ℝ) / (2 * s) := by
      rw [Nat.cast_sub hkv, hs]
      push_cast
      exact sqrt_sub_le hn' (by exact_mod_cast hkv)
    have h3 : Real.exp (cHR * Real.sqrt ((n - k * v : ℕ) : ℝ)) ≤ Real.exp (cHR * s) * Real.exp (-(a * k * v)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      calc cHR * Real.sqrt ((n - k * v : ℕ) : ℝ) ≤ cHR * (s - (k * v : ℝ) / (2 * s)) := by gcongr
        _ = cHR * s + -(a * k * v) := by rw [ha]; ring
    calc (v : ℝ) * (p (n - k * v) : ℝ) ≤ v * (Real.exp (cHR * s) * Real.exp (-(a * k * v))) := by gcongr; exact h1.trans h3
      _ = Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) := by ring
  have hsum : (n : ℝ) * p n ≤ n * Real.exp (cHR * s) := by
    calc (n : ℝ) * p n = ((n * p n : ℕ) : ℝ) := by push_cast; ring
      _ = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * (p (n - k * v) : ℝ) := by rw [mul_p_eq]; push_cast; rfl
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) :=
          sum_le_sum fun v hv => sum_le_sum (hterm v hv)
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 n, Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) :=
          sum_le_sum fun v _ => sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self _ _)) fun _ _ _ => by positivity
      _ = Real.exp (cHR * s) * ∑ k ∈ Icc 1 n, ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(a * k * v)) := by
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ Real.exp (cHR * s) * ∑ k ∈ Icc 1 n, 1 / (a * k) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (Real.exp_pos _).le
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.1 hk).1
          exact sum_mul_exp_le (by positivity) _
      _ = Real.exp (cHR * s) * (1 / a ^ 2 * ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2) := by
          congr 1
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by rw [mul_pow, one_div_mul_one_div]
      _ ≤ Real.exp (cHR * s) * (1 / a ^ 2 * (Real.pi ^ 2 / 6)) := by
          gcongr
          exact sum_inv_sq_le _
      _ = n * Real.exp (cHR * s) := by
          have hpi := Real.pi_pos
          rw [ha, div_pow, mul_pow, cHR_sq, hss]
          field_simp
          ring
  exact le_of_mul_le_mul_left hsum hn'

end ClauseBound.Part
