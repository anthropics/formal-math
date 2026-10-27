/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Defs2
public import ClauseBound.Boson.Scalars

/-! # Lemmas on the dual families of Lemma 10

For a partition μ let a^μ = ∏_i (−1)^{μ_i−1}·y_{μ_i} with y_n = Σ_{j=1}^{n} C(n,j)·t_j, as in Lemma 10.
This file shows that the monomials of a^μ have positive parts and weight at most |μ| (`aFam_ok`)
and that the absolute values of the coefficients of a^μ add up to at most 2^{|μ|}
(`sum_abs_aFam_le`). It also shows that z_ν divides h! for a partition ν of h (`zz_dvd_factorial`),
so that h!/z_ν, the factor of b^ν in Lemma 10, is an integer. The remaining lemmas are on sums over
lists and on factorials, and these proofs use them. -/

public section

namespace ClauseBound.Boson.Dual

open Finset

/-! ### Sums over lists -/

/-- A sum over 0, …, n − 1 as the sum of a list. -/
theorem sum_range_eq_list (F : ℕ → ℤ) (n : ℕ) : ∑ p ∈ range n, F p = ((List.range n).map F).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp

/-- The sum over a concatenation of lists is the sum of the sums. -/
theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (φ : β → ℤ) :
    ((l.flatMap g).map φ).sum = (l.map fun x => ((g x).map φ).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

end ClauseBound.Boson.Dual

namespace ClauseBound.Boson

open Finset

/-- The monomials of a^μ have positive parts and weight at most |μ|. -/
theorem aFam_ok {μ : List ℕ} (hμ : Pos μ) : (aFam μ).Ok μ.sum := by
  induction μ with
  | nil =>
    intro c hc
    rw [aFam, List.mem_singleton] at hc
    subst hc
    exact ⟨fun n hn => absurd hn List.not_mem_nil, le_rfl⟩
  | cons n μ ih =>
    intro c hc
    rw [aFam, List.mem_flatMap] at hc
    obtain ⟨cj, hcj, hc⟩ := hc
    obtain ⟨cL, hcL, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcj
    have hi' := List.mem_range.1 hi
    obtain ⟨h1, h2⟩ := ih (fun k hk => hμ k (List.mem_cons_of_mem _ hk)) cL hcL
    refine ⟨fun k hk => ?_, ?_⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact Nat.succ_pos i
      · exact h1 k hk
    · simp only [List.sum_cons]
      omega

/-- The absolute values of the coefficients of a^μ add up to at most 2^{|μ|}. -/
theorem sum_abs_aFam_le (μ : List ℕ) : ((aFam μ).map fun c => |c.1|).sum ≤ 2 ^ μ.sum := by
  induction μ with
  | nil => simp [aFam]
  | cons n μ ih =>
    have h1 : ((yl n).map fun cj => |cj.1|).sum ≤ 2 ^ n := by
      unfold yl
      rw [List.map_map, ← Dual.sum_range_eq_list]
      have h2 : ∀ i ∈ range n, ((fun cj : ℤ × ℕ => |cj.1|) ∘ fun i => ((-1) ^ (n - 1) * (n.choose (i + 1) : ℤ), i + 1)) i = (n.choose (i + 1) : ℤ) := by
        intro i _
        simp [abs_mul]
      rw [sum_congr rfl h2]
      have h3 := Nat.sum_range_choose n
      rw [sum_range_succ'] at h3
      have h4 : ∑ i ∈ range n, n.choose (i + 1) ≤ 2 ^ n := by omega
      exact_mod_cast h4
    have h0 : 0 ≤ ((aFam μ).map fun c => |c.1|).sum := List.sum_nonneg fun x hx => by
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _
    rw [aFam, Dual.sum_map_flatMap]
    have h5 : ∀ cj : ℤ × ℕ, (((aFam μ).map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)).map fun c : ℤ × List ℕ => |c.1|).sum
        = |cj.1| * ((aFam μ).map fun c => |c.1|).sum := by
      intro cj
      rw [List.map_map, ← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun c _ => abs_mul _ _)
    simp only [h5]
    rw [List.sum_map_mul_right, List.sum_cons, pow_add]
    exact mul_le_mul h1 ih h0 (by positivity)

end ClauseBound.Boson

namespace ClauseBound.Boson.Dual

open Finset

/-! ### z_ν -/

/-- k^m·m! divides (m·k)!. -/
theorem pow_mul_factorial_dvd {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : k ^ m * m.factorial ∣ (m * k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ((m + 1) * k).factorial = (m + 1) * k * ((m + 1) * k - 1).factorial :=
      (Nat.mul_factorial_pred (Nat.mul_ne_zero (Nat.succ_ne_zero m) (by omega))).symm
    have h2 : (m * k).factorial ∣ ((m + 1) * k - 1).factorial := Nat.factorial_dvd_factorial (by rw [Nat.succ_mul]; omega)
    rw [h1, pow_succ, Nat.factorial_succ]
    calc k ^ m * k * ((m + 1) * m.factorial) = (m + 1) * k * (k ^ m * m.factorial) := by ring
      _ ∣ _ := Nat.mul_dvd_mul_left _ (ih.trans h2)

end ClauseBound.Boson.Dual

namespace ClauseBound.Boson

open Finset

/-- z_ν divides h!. -/
theorem zz_dvd_factorial {h : ℕ} (q : Nat.Partition h) : zz q.parts ∣ h.factorial := by
  have h1 : h = ∑ k ∈ q.parts.toFinset, q.parts.count k * k := by
    have := Finset.sum_multiset_count q.parts
    rw [q.parts_sum] at this
    simpa only [smul_eq_mul] using this
  have h2 := Nat.prod_factorial_dvd_factorial_sum q.parts.toFinset fun k => q.parts.count k * k
  rw [← h1] at h2
  exact (prod_dvd_prod_of_dvd _ _ fun k hk => Dual.pow_mul_factorial_dvd (q.parts_pos (Multiset.mem_toFinset.1 hk)) _).trans h2

end ClauseBound.Boson
