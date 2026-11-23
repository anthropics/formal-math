/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.LowDegChains

/-!
# Low degree is fast, over commutative rings

The parts of positive degree of the gates of a circuit, along a line, are power series that satisfy quadratic
equations; `W` sums the coefficients of products of them.
-/

set_option linter.unusedSectionVars false

namespace Nc.Acc

open Finset

variable {F : Type*} [CommRing F] {σ : Type*} {s : ℕ}

open PowerSeries in
/-- The parts of positive degree along the line. -/
noncomputable def ser (u : σ → F) (q : MvPolynomial σ F) : PowerSeries F := PowerSeries.mk fun m => (line u q).coeff (m + 1)

theorem ser_zero (u : σ → F) : ser u (0 : MvPolynomial σ F) = 0 := by
  ext m
  simp [ser]

/-- The quadratic equations. -/
theorem exists_series [Fintype σ] {p : MvPolynomial σ F} {M : ℕ} (hp : Computes p s) (hs : s ≤ 2 ^ M) :
    ∃ (κ : ℕ → ℕ → ℕ → F) (lam : ℕ → σ → F) (P : ℕ → MvPolynomial σ F) (out : ℕ), out < 2 ^ M ∧ P out = p ∧
      ∀ (u : σ → F) (g : ℕ), ser u (P g) = PowerSeries.C (∑ i, lam g i * u i) + PowerSeries.X *
        ∑ l ∈ range (2 ^ M), ∑ r ∈ range (2 ^ M), PowerSeries.C (κ g l r) * (ser u (P l) * ser u (P r)) := by
  classical
  obtain ⟨l, hl, k, hk, rfl⟩ := hp
  obtain ⟨κ, lam, left, right, H⟩ := Paper.lem_lowdeg_chains l hl
  refine ⟨fun g a b => if h : g < s then ∑ j, if (left j).1 = a ∧ (right j).1 = b then κ ⟨g, h⟩ j else 0 else 0,
    fun g => if h : g < s then lam ⟨g, h⟩ else 0, fun g => if g < s then l g else 0, k, hk.trans_le hs,
    if_pos hk, fun u g => ?_⟩
  by_cases hg : g < s
  · simp only [dif_pos hg, if_pos hg]
    have h1 : ∑ a ∈ range (2 ^ M), ∑ b ∈ range (2 ^ M),
        PowerSeries.C (∑ j, if (left j).1 = a ∧ (right j).1 = b then κ ⟨g, hg⟩ j else 0) *
          (ser u (if a < s then l a else 0) * ser u (if b < s then l b else 0)) =
        ∑ j, PowerSeries.C (κ ⟨g, hg⟩ j) * (ser u (l (left j)) * ser u (l (right j))) := by
      simp only [map_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single (left j).1, Finset.sum_eq_single (right j).1]
      · simp
      · intro b _ hb
        rw [if_neg fun h => hb h.2.symm, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.2 ((right j).2.trans_le hs)) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [if_neg fun h => ha h.1.symm, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.2 ((left j).2.trans_le hs)) h
    rw [h1]
    ext m
    have h2 := H ⟨g, hg⟩ u m
    cases m with
    | zero =>
      simp only [ser, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_zero_X_mul, add_zero]
      simpa using h2
    | succ m =>
      simp only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        if_false, map_sum, PowerSeries.coeff_C_mul, Finset.sum_const_zero, zero_add]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, zero_add] at h2
      rw [ser, PowerSeries.coeff_mk, h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [ser, PowerSeries.coeff_mk]
      congr 2
      omega
  · simp only [dif_neg hg, if_neg hg, ser_zero]
    simp

/-- The sum of the coefficients of degree at most `b` of a product. -/
noncomputable def W (E : ℕ → PowerSeries F) (b : ℕ) (gs : List ℕ) : F :=
  ∑ n ∈ range (b + 1), PowerSeries.coeff n (gs.map E).prod

theorem W_nil (E : ℕ → PowerSeries F) (b : ℕ) : W E b [] = 1 := by
  simp [W, PowerSeries.coeff_one]

/-- The contribution of the product gates. -/
noncomputable def Wi (E : ℕ → PowerSeries F) (n : ℕ) (κ : ℕ → ℕ → F) (gs : List ℕ) : ℕ → F
  | 0 => 0
  | b + 1 => ∑ l ∈ range n, ∑ r ∈ range n, κ l r * W E b (l :: r :: gs)

theorem W_cons {E : ℕ → PowerSeries F} {g : ℕ} {a : F} {n : ℕ} {κ : ℕ → ℕ → F}
    (h : E g = PowerSeries.C a + PowerSeries.X * ∑ l ∈ range n, ∑ r ∈ range n, PowerSeries.C (κ l r) * (E l * E r))
    (b : ℕ) (gs : List ℕ) : W E b (g :: gs) = a * W E b gs + Wi E n κ gs b := by
  have h1 : (List.map E (g :: gs)).prod = PowerSeries.C a * (gs.map E).prod + PowerSeries.X *
      ∑ l ∈ range n, ∑ r ∈ range n, PowerSeries.C (κ l r) * (List.map E (l :: r :: gs)).prod := by
    rw [List.map_cons, List.prod_cons, h, add_mul, mul_assoc, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [List.map_cons, List.prod_cons]
    ring
  unfold W
  simp only [h1, map_add, PowerSeries.coeff_C_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_range_succ']
  simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul, add_zero]
  cases b with
  | zero => simp [Wi]
  | succ b =>
    simp only [map_sum, PowerSeries.coeff_C_mul, Wi, W]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]

/-- The parts of degree at most `N`. -/
theorem sum_coeff_line (u : σ → F) (P : ℕ → MvPolynomial σ F) (out N : ℕ) (hN : 0 < N) :
    ∑ i ∈ range (N + 1), (line u (P out)).coeff i =
      MvPolynomial.constantCoeff (P out) + W (fun g => ser u (P g)) (N - 1) [out] := by
  rw [Finset.sum_range_succ', line_coeff_zero, add_comm, W, Nat.sub_add_cancel hN]
  simp [ser]

/-- All parts of a polynomial. -/
theorem sum_coeff_eq_eval (u : σ → F) (p : MvPolynomial σ F) {d n : ℕ} (hd : p.totalDegree ≤ d) (hn : d < n) :
    ∑ i ∈ range n, (line u p).coeff i = MvPolynomial.eval u p := by
  have hdeg : (line u p).natDegree ≤ d := by
    have := MvPolynomial.aeval_natDegree_le p hd
      (fun i => Polynomial.C (u i) * Polynomial.X) (n := 1)
      (fun i => (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
    simpa [line] using this
  rw [← eval_one_line, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg hn)]
  simp

end Nc.Acc
