/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cat.Mean

/-!
# Windows: clamping, the relative place in a window, and two elementary inequalities

Helpers for the proof of Theorem thm:cn (Paper/Fan.lean); nothing here is about prices.
-/

open Filter Topology Finset

namespace Cat

theorem sum_lt {M j : ℕ} (hj : j ≤ M) (x y : ℝ) :
    ∑ l : Fin M, (if (l : ℕ) < j then x else y) = j * x + ((M : ℝ) - j) * y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < j then x else y), Finset.sum_range_add]
  have h1 : ∑ l ∈ range j, (if l < j then x else y) = ∑ l ∈ range j, x :=
    Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_range.1 hl)
  have h2 : ∑ l ∈ range d, (if j + l < j then x else y) = ∑ l ∈ range d, y :=
    Finset.sum_congr rfl fun l _ => if_neg (by omega)
  rw [h1, h2]
  simp

/-- Clamping an integer to `0, …, N`. -/
def cl (N : ℕ) (i : ℤ) : ℕ := min i.toNat N

theorem cl_le (N : ℕ) (i : ℤ) : cl N i ≤ N := min_le_right _ _

theorem cl_sub (N : ℕ) (i i' : ℤ) : |((cl N i : ℕ) : ℝ) - (cl N i' : ℕ)| ≤ |(i : ℝ) - i'| := by
  have h : |((cl N i : ℕ) : ℤ) - (cl N i' : ℕ)| ≤ |i - i'| := by
    unfold cl
    rcases le_total i i' with h | h
    · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
      omega
    · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
  exact_mod_cast h

theorem cl_cast {N : ℕ} {i : ℤ} (h0 : 0 ≤ i) (h1 : i ≤ N) : ((cl N i : ℕ) : ℝ) = i := by
  have : ((cl N i : ℕ) : ℤ) = i := by
    unfold cl
    omega
  exact_mod_cast this

theorem cl_window {n T : ℕ} {i k : ℤ} (h0 : 0 ≤ i + k + n) (h1 : i + k + n ≤ n ^ 2 * T) :
    ((cl (n ^ 2 * T) (i + k + n) : ℕ) : ℝ) = i + k + n := by
  rw [cl_cast h0 (by exact_mod_cast h1)]
  push_cast
  ring

theorem cl_succ (N : ℕ) (i : ℤ) : |((cl N i : ℕ) : ℝ) - (cl N (i + 1) : ℕ)| ≤ 1 := by
  refine (cl_sub _ _ _).trans ?_
  push_cast
  rw [sub_add_cancel_left, abs_neg, abs_one]

theorem cl_sq (n : ℕ) : cl (n ^ 2) ((n : ℤ) ^ 2) = n ^ 2 := by
  have : ((n : ℤ) ^ 2) = ((n ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [this, cl, Int.toNat_natCast, min_self]

theorem cl_zero (N : ℕ) : cl N 0 = 0 := by simp [cl]

theorem max_one_pos (n : ℕ) : 0 < max n 1 := by simp

/-- What "n large" means below. -/
theorem eventually_large {T : ℕ} (hT : 2 ≤ T) (R : ℕ) : ∀ᶠ n : ℕ in atTop, max n 1 = n ∧ (1 : ℝ) ≤ n ∧ R ≤ n ∧
    n ^ 2 + 2 * n ≤ n ^ 2 * T ∧ n ^ 2 + 2 * n ≤ 2 * n ^ 2 := by
  filter_upwards [eventually_ge_atTop (max R 3)] with n hn
  have h3 : 3 ≤ n := (le_max_right _ _).trans hn
  have h4 : n ^ 2 + 2 * n ≤ 2 * n ^ 2 := by nlinarith
  refine ⟨by omega, by exact_mod_cast (by omega : 1 ≤ n), (le_max_left _ _).trans hn, ?_, h4⟩
  nlinarith

theorem prod_add_mk (i k : ℤ) (h : ℤ × ℤ) : ((i, k) : ℤ × ℤ) + h = (i + h.1, k + h.2) := rfl

/-- The relative place in the window. -/
noncomputable def place : Fn := fun n _ i _ => (cl (n ^ 2) i : ℕ) / (n : ℝ) ^ 2

theorem place_nonneg (n : ℕ) (b : Bool) (i k : ℤ) : 0 ≤ place n b i k := by
  unfold place
  positivity

theorem place_le_one (n : ℕ) (b : Bool) (i k : ℤ) : place n b i k ≤ 1 := by
  unfold place
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast cl_le (n ^ 2) i

theorem bd_place : Bd place :=
  ⟨1, fun n b i k => by rw [abs_of_nonneg (place_nonneg _ _ _ _)]; exact place_le_one _ _ _ _⟩

theorem sum_id (N : ℕ) : ∑ i ∈ range N, (i : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem mean_place : mean place = 1 / 2 := by
  apply mean_eq bd_place
  have h1 : Tendsto (fun n : ℕ => 1 / 2 - 1 / 2 * (1 / (n : ℝ)) ^ 2) atTop
      (𝓝 (1 / 2 - 1 / 2 * 0 ^ 2)) :=
    ((tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul _).const_sub _
  norm_num at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h2 : ∀ b : Bool, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n, place n b (i : ℕ) (k : ℕ) =
      n * (((n ^ 2 : ℕ) : ℝ) * ((n ^ 2 : ℕ) - 1) / 2 / n ^ 2) := by
    intro b
    rw [← sum_id, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hp : ∀ k ∈ range n, place n b (i : ℕ) (k : ℕ) = (i : ℝ) / n ^ 2 := by
      intro k _
      rw [place, cl_cast (Int.natCast_nonneg i) (by exact_mod_cast (Finset.mem_range.1 hi).le)]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [avg, Finset.sum_congr rfl fun b _ => h2 b, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp

/-- A sequence f with second differences at most `2ω`, where `φ` stands for the value f(−1): then
f(A) ≤ f(0) + A(f(0) − φ + ω) + A²ω. For ψ(l) = f(l) − l²ω this says ψ(A) ≤ ψ(0) + A(ψ(0) − ψ(−1)). -/
theorem conc {f : ℕ → ℝ} {φ ω : ℝ} (h0 : f 1 + φ ≤ 2 * f 0 + 2 * ω)
    (h : ∀ j, f (j + 2) + f j ≤ 2 * f (j + 1) + 2 * ω) (A : ℕ) :
    f A ≤ f 0 + A * (f 0 - φ + ω) + A ^ 2 * ω := by
  have key : ∀ j, f (j + 1) - f j ≤ (f 0 - φ + ω) + (2 * j + 1) * ω := by
    intro j
    induction j with
    | zero => norm_num; linarith
    | succ j ih => have := h j; push_cast; linarith
  induction A with
  | zero => simp
  | succ A ih => have := key A; push_cast; nlinarith

/-- Squaring |rn²(L′ − L) + aL′| ≤ W, with 2L′(L′ − L) ≥ L′² − L², 1 − r ≤ 2θ and n²(L′² − L²) ≤ K:
W² ≥ a²L′² + a·n²(L′² − L²) − 2aθK. -/
theorem sq_core {n L' L0 r a θ K W : ℝ} (hr0 : 0 ≤ r) (hr2 : 0 ≤ 1 - r) (hr1 : 1 - r ≤ 2 * θ)
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hZ : n ^ 2 * (L' ^ 2 - L0 ^ 2) ≤ K)
    (h1 : r * (n ^ 2 * (L' - L0)) + a * L' ≤ W) (h2 : -(r * (n ^ 2 * (L' - L0)) + a * L') ≤ W) :
    a ^ 2 * (L' * L') + a * (n ^ 2 * (L' ^ 2 - L0 ^ 2)) - a * (2 * θ * K) ≤ W * W := by
  have E3 : (r * (n ^ 2 * (L' - L0)) + a * L') ^ 2 ≤ W ^ 2 := sq_le_sq' (by linarith) h1
  have Z2 : (1 - r) * (n ^ 2 * (L' ^ 2 - L0 ^ 2)) ≤ 2 * θ * K :=
    (mul_le_mul_of_nonneg_left hZ hr2).trans (mul_le_mul_of_nonneg_right hr1 hK)
  have Z4 : 0 ≤ a * r * (n ^ 2 * (L' - L0) ^ 2) := mul_nonneg (mul_nonneg ha hr0) (by positivity)
  have Z5 := mul_le_mul_of_nonneg_left Z2 ha
  have Z6 : 0 ≤ (r * (n ^ 2 * (L' - L0))) ^ 2 := sq_nonneg _
  nlinarith

end Cat
