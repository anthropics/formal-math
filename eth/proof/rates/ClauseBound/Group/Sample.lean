/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import ClauseBound.Rec.Tail

/-! # Hoeffding's inequality for sampling without replacement, as a count

Let e_n be the sum of the products of x over the n-subsets of a set of N elements, x ≥ 0. First e_n
≤ C(N, n)·(mean of x)ⁿ, a case of Maclaurin's inequality (`esymm_le`). The proof is
an induction on the set: with one more element a, e_{k+1} = e_{k+1}' + x_a·e_k'; by the induction
hypothesis and two identities between binomial coefficients this is at most
C(N, k+1)·u^k·((k+1)·w − k·u), where u is the old mean and w the new one; and (k+1)·w·u^k ≤ w^{k+1} +
k·u^{k+1}.

Then the exponential moment: the number of n-subsets S with Σ_{i ∈ S} c_i ≥ a, times e^{θa}, is at
most the sum over all n-subsets of ∏_{i ∈ S} e^{θ c_i}, so at most
C(N, n)·(mean of e^{θ c_i})ⁿ. The mean is bounded by convexity and Hoeffding's lemma on two points,
and θ = 4t/R. -/

public section

namespace ClauseBound.Group

open Finset

variable {ι : Type} [DecidableEq ι]

namespace Sample

/-- (k+1)·w·u^k ≤ w^(k+1) + k·u^(k+1) for u, w ≥ 0. -/
theorem tangent_le (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) (k : ℕ) : ((k : ℝ) + 1) * w * u ^ k ≤ w ^ (k + 1) + k * u ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have key : 0 ≤ (w ^ (k + 1) - u ^ (k + 1)) * (w - u) := by
      rcases le_total u w with h | h
      · exact mul_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hu h _)) (sub_nonneg.2 h)
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hw h _)) (sub_nonpos.2 h)
    have h2 := mul_le_mul_of_nonneg_right ih hu
    push_cast
    simp only [pow_succ] at key h2 ⊢
    generalize u ^ k = A at *
    generalize w ^ k = W at *
    nlinarith

/-- The sum of the products over the (k+1)-subsets when one element is added. -/
theorem sum_powersetCard_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (x : ι → ℝ) (k : ℕ) :
    ∑ S ∈ powersetCard (k + 1) (insert a s), ∏ i ∈ S, x i =
      ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i + x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i := by
  have hnot : ∀ {m : ℕ} {S : Finset ι}, S ∈ powersetCard m s → a ∉ S := fun hS h => ha ((mem_powersetCard.1 hS).1 h)
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun S hS => ?_
    rw [prod_insert (hnot hS)]
  · intro S hS U hU h
    have h' := congrArg (fun V => V.erase a) h
    simpa [erase_insert (hnot hS), erase_insert (hnot hU)] using h'
  · rw [disjoint_left]
    intro S hS hS'
    obtain ⟨U, _, rfl⟩ := mem_image.1 hS'
    exact hnot hS (mem_insert_self a U)

/-- The sum of the products over the n-subsets is at most C(N, n) times the n-th power of the mean. -/
theorem esymm_le (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∀ n : ℕ, ∑ S ∈ powersetCard n s, ∏ i ∈ S, x i ≤ ((#s).choose n : ℝ) * ((∑ i ∈ s, x i) / #s) ^ n := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rcases n with _ | n
    · simp
    · have h : powersetCard (n + 1) (∅ : Finset ι) = ∅ := powersetCard_eq_empty.2 (by simp)
      simp [h]
  | insert a s ha ih =>
    intro n
    rcases n with _ | k
    · simp
    have hxa : 0 ≤ x a := hx a (mem_insert_self a s)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have ih1 := ih hxs (k + 1)
    have ih0 := ih hxs k
    have hS0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    rw [sum_powersetCard_insert ha, card_insert_of_notMem ha, sum_insert ha]
    have hNu : (#s : ℝ) * ((∑ i ∈ s, x i) / #s) = ∑ i ∈ s, x i := by
      by_cases h0 : #s = 0
      · rw [card_eq_zero.1 h0]; simp
      · have : (#s : ℝ) ≠ 0 := by exact_mod_cast h0
        field_simp
    have hNw : ((#s : ℝ) + 1) * ((x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1)) = x a + ∑ i ∈ s, x i := by
      have : (#s : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hu : 0 ≤ (∑ i ∈ s, x i) / #s := by positivity
    have hw : 0 ≤ (x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1) := by positivity
    have h1 : ((#s : ℝ) + 1) * ((#s).choose k : ℝ) = ((#s + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (#s) k
    have h2 : ((#s + 1).choose (k + 1) : ℝ) = ((#s).choose k : ℝ) + ((#s).choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (#s) k
    push_cast
    generalize (∑ i ∈ s, x i) / #s = u at *
    generalize (x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1) = w at *
    have hv : x a = ((#s : ℝ) + 1) * w - #s * u := by linarith
    have ht := tangent_le u w hu hw k
    calc ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i + x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i
        ≤ ((#s).choose (k + 1) : ℝ) * u ^ (k + 1) + x a * (((#s).choose k : ℝ) * u ^ k) :=
          add_le_add ih1 (mul_le_mul_of_nonneg_left ih0 hxa)
      _ = ((#s + 1).choose (k + 1) : ℝ) * (((k : ℝ) + 1) * w * u ^ k - k * u ^ (k + 1)) := by
          rw [hv]
          linear_combination (w * u ^ k - u ^ (k + 1)) * h1 - u ^ (k + 1) * h2
      _ ≤ ((#s + 1).choose (k + 1) : ℝ) * w ^ (k + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

omit [DecidableEq ι] in
/-- The mean of e^{θ c_i} is at most exp(θ·mean + (θR)²/8) if all c_i lie in [0, R]. -/
theorem avg_exp_le (s : Finset ι) (c : ι → ℝ) {R : ℝ} (hR : 0 < R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty) (θ : ℝ) :
    (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤ Real.exp (θ * ((∑ i ∈ s, c i) / #s) + (θ * R) ^ 2 / 8) := by
  have hN : (0 : ℝ) < #s := by exact_mod_cast card_pos.2 hs
  have h1 : ∀ i ∈ s, Real.exp (θ * c i) ≤ (1 - c i / R) + c i / R * Real.exp (θ * R) := by
    intro i hi
    obtain ⟨h0, hle⟩ := hc i hi
    have hb : 0 ≤ c i / R := by positivity
    have ha : 0 ≤ 1 - c i / R := by rw [sub_nonneg, div_le_one hR]; exact hle
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * R)) ha hb (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rwa [show c i / R * (θ * R) = θ * c i by field_simp] at h
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (∑ i ∈ s, c i) / #s / R := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i ∈ s, c i := sum_nonneg fun i hi => (hc i hi).1
  have hsumR : ∑ i ∈ s, c i ≤ #s * R := by
    calc ∑ i ∈ s, c i ≤ ∑ _i ∈ s, R := sum_le_sum fun i hi => (hc i hi).2
      _ = #s * R := by rw [sum_const, nsmul_eq_mul]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_div, div_le_one (by positivity)]; exact hsumR
  have h2 : (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤ (1 - p) + p * Real.exp (θ * R) := by
    rw [div_le_iff₀ hN]
    calc ∑ i ∈ s, Real.exp (θ * c i) ≤ ∑ i ∈ s, ((1 - c i / R) + c i / R * Real.exp (θ * R)) := sum_le_sum h1
      _ = #s - (∑ i ∈ s, c i) / R + (∑ i ∈ s, c i) / R * Real.exp (θ * R) := by
          rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← sum_div, ← sum_mul, ← sum_div]
      _ = ((1 - p) + p * Real.exp (θ * R)) * #s := by rw [hp]; field_simp
  have h3 := ClauseBound.Rec.Tail.two_point_le hp0 hp1 (θ * R)
  have h4 : (1 - p) + p * Real.exp (θ * R) =
      (p * Real.exp (θ * R * (1 - p)) + (1 - p) * Real.exp (θ * R * (0 - p))) * Real.exp (θ * R * p) := by
    have e1 : Real.exp (θ * R * (1 - p)) * Real.exp (θ * R * p) = Real.exp (θ * R) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (θ * R * (0 - p)) * Real.exp (θ * R * p) = 1 := by
      rw [← Real.exp_add, show θ * R * (0 - p) + θ * R * p = 0 by ring, Real.exp_zero]
    linear_combination (-p) * e1 - (1 - p) * e2
  have h5 : θ * ((∑ i ∈ s, c i) / #s) = θ * R * p := by rw [hp]; field_simp
  rw [h5, add_comm, Real.exp_add]
  refine h2.trans ?_
  rw [h4]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

end Sample

open Sample

/-- Among the n-subsets S of s, at most the fraction exp(−2nt²) has Σ_{i ∈ S} c_i ≥ n·(mean of c) +
t·n·R, if all c_i lie in [0, R]. -/
theorem card_sample_tail_le (s : Finset ι) (c : ι → ℝ) {R t : ℝ} (hR : 0 < R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty)
    (n : ℕ) (ht : 0 ≤ t) :
    (#{S ∈ powersetCard n s | n * ((∑ i ∈ s, c i) / #s) + t * n * R ≤ ∑ i ∈ S, c i} : ℝ)
      ≤ Real.exp (-(2 * n * t ^ 2)) * ((#s).choose n : ℝ) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 4 * t / R := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (∑ i ∈ s, c i) / #s := ⟨_, rfl⟩
  rw [← hμ]
  have h1 : (#{S ∈ powersetCard n s | n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) * Real.exp (θ * (n * μ + t * n * R)) ≤
      ∑ S ∈ powersetCard n s, ∏ i ∈ S, Real.exp (θ * c i) := by
    calc (#{S ∈ powersetCard n s | n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) * Real.exp (θ * (n * μ + t * n * R))
        = ∑ _S ∈ powersetCard n s with n * μ + t * n * R ≤ ∑ i ∈ _S, c i, Real.exp (θ * (n * μ + t * n * R)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ powersetCard n s with n * μ + t * n * R ≤ ∑ i ∈ S, c i, ∏ i ∈ S, Real.exp (θ * c i) := by
          refine sum_le_sum fun S hS => ?_
          rw [← Real.exp_sum, ← mul_sum]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (mem_filter.1 hS).2 hθ0)
      _ ≤ ∑ S ∈ powersetCard n s, ∏ i ∈ S, Real.exp (θ * c i) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ => prod_nonneg fun i _ => (Real.exp_pos _).le
  have h2 := esymm_le s (fun i => Real.exp (θ * c i)) (fun i _ => (Real.exp_pos _).le) n
  have h3 : ((∑ i ∈ s, Real.exp (θ * c i)) / #s) ^ n ≤ Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) := by
    rw [Real.exp_nat_mul, hμ]
    exact pow_le_pow_left₀ (by positivity) (avg_exp_le s c hR hc hs θ) n
  have h4 : (#{S ∈ powersetCard n s | n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) * Real.exp (θ * (n * μ + t * n * R)) ≤
      ((#s).choose n : ℝ) * Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
  have h5 : Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) = Real.exp (-(2 * n * t ^ 2)) * Real.exp (θ * (n * μ + t * n * R)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hθ]
    field_simp
    ring
  rw [h5, ← mul_assoc] at h4
  have h6 := le_of_mul_le_mul_right h4 (Real.exp_pos _)
  linarith

end ClauseBound.Group
