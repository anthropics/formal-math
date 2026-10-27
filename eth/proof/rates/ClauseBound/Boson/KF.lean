/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Defs2
public import ClauseBound.Boson.Basic
public import ClauseBound.Boson.Size
public import ClauseBound.Boson.Dual

/-! # The matrices of the parts of a^μ of a given weight

The combination a^μ = ∏_i (−1)^{μ_i−1}·y_{μ_i} has up to ∏_i μ_i monomials, too many to go through
one by one. `KF μ w r` is the matrix of (the part of weight w of a^μ)[r], that is, the sum of
c·L[r] over the monomials L of weight w of a^μ, with their coefficients c. This file proves

* the recursion on the parts of μ (`KF_nil`, `KF_cons`): one more factor (−1)^{n−1}·y_n =
  (−1)^{n−1}·Σ_{j=1}^{n} C(n,j)·t_j takes the tables of the weights w − j to the table of the weight
  w;
* that a sum over the monomials of a^μ with factors that depend on the weight only is a sum over the
  weights 0, …, |μ| (`sum_aFam_eq`);
* a bound on the entries (`abs_KF_le`). -/

public section

namespace ClauseBound.Boson

open Finset

/-- The matrix of (the part of weight w of a^μ)[r]. -/
@[expose] def KF (μ : List ℕ) (w : ℕ) (r : ℤ) : Ker := fun π σ =>
  ((aFam μ).map fun c => if c.2.sum = w then c.1 * op c.2 r π σ else 0).sum

/-! ### Sums over lists -/

private theorem sum_map_flatMap {α β : Type} (A : List α) (f : α → List β) (φ : β → ℤ) :
    ((A.flatMap f).map φ).sum = (A.map fun x => ((f x).map φ).sum).sum := by
  induction A with
  | nil => rfl
  | cons x A ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

private theorem sum_map_range (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

private theorem sum_Icc_one (f : ℕ → ℤ) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

private theorem abs_sum_map_le {α : Type} (A : List α) (f : α → ℤ) : |(A.map f).sum| ≤ (A.map fun x => |f x|).sum := by
  induction A with
  | nil => simp
  | cons x A ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (by omega)

private theorem sum_map_le {α : Type} (A : List α) (f g : α → ℤ) (h : ∀ x ∈ A, f x ≤ g x) : (A.map f).sum ≤ (A.map g).sum := by
  induction A with
  | nil => simp
  | cons x A ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    omega

private theorem sum_mul_sum_map {α : Type} (s : Finset ℕ) (g : ℕ → ℤ) (A : List α) (f : ℕ → α → ℤ) :
    ∑ w ∈ s, g w * (A.map (f w)).sum = (A.map fun c => ∑ w ∈ s, g w * f w c).sum := by
  induction A with
  | nil => simp
  | cons x A ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, sum_add_distrib]
    rw [ih]

/-! ### The normally ordered product is linear in the family -/

private theorem nop_add_smul (n : ℕ) (c : ℤ) (F G : ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) :
    nop n (fun ρ π σ => c * F ρ π σ + G ρ π σ) r π σ = c * nop n F r π σ + nop n G r π σ := by
  have h1 : ∑ l ∈ π.toFinset, bet n l * cre l (fun π σ => c * F (r - l) π σ + G (r - l) π σ) π σ =
      c * ∑ l ∈ π.toFinset, bet n l * cre l (F (r - l)) π σ + ∑ l ∈ π.toFinset, bet n l * cre l (G (r - l)) π σ := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    simp only [cre]
    split_ifs <;> ring
  have h2 : ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (fun π σ => c * F (r + k) π σ + G (r + k) π σ) k π σ =
      c * ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ + ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (G (r + k)) k π σ := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [ann]
    ring
  simp only [nop]
  rw [h1, h2]
  ring

private theorem nop_zero (n : ℕ) (r : ℤ) (π σ : Multiset ℕ) : nop n (fun _ _ _ => 0) r π σ = 0 := by
  simp [nop, cre, ann]

private theorem nop_list_sum {α : Type} (n : ℕ) (A : List α) (c : α → ℤ) (G : α → ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) :
    nop n (fun ρ π σ => (A.map fun x => c x * G x ρ π σ).sum) r π σ = (A.map fun x => c x * nop n (G x) r π σ).sum := by
  induction A with
  | nil => exact nop_zero n r π σ
  | cons x A ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [nop_add_smul n (c x) (G x) (fun ρ π σ => (A.map fun x => c x * G x ρ π σ).sum), ih]

/-! ### The monomials of a^μ -/

private theorem mem_aFam_cons {n : ℕ} {μ : List ℕ} {c : ℤ × List ℕ} (h : c ∈ aFam (n :: μ)) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ ∃ cL ∈ aFam μ, c.2 = j :: cL.2 := by
  obtain ⟨cj, hcj, hc⟩ := List.mem_flatMap.1 h
  obtain ⟨cL, hcL, rfl⟩ := List.mem_map.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcj
  exact ⟨i + 1, by omega, List.mem_range.1 hi, cL, hcL, rfl⟩

/-- A monomial of a^μ has as many parts as μ, its weight is at most that of μ, and its parts are at
most as large as the largest part of μ. -/
private theorem aFam_shape (μ : List ℕ) : ∀ c ∈ aFam μ, c.2.length = μ.length ∧ c.2.sum ≤ μ.sum ∧ ∀ W, (∀ n ∈ μ, n ≤ W) → ∀ j ∈ c.2, j ≤ W := by
  induction μ with
  | nil =>
    intro c hc
    obtain rfl : c = (1, []) := by simpa [aFam] using hc
    simp
  | cons n μ ih =>
    intro c hc
    obtain ⟨j, -, hj, cL, hcL, e⟩ := mem_aFam_cons hc
    obtain ⟨h1, h2, h3⟩ := ih cL hcL
    rw [e]
    refine ⟨by simp [h1], by simp only [List.sum_cons]; omega, fun W hW i hi => ?_⟩
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hj.trans (hW n (by simp))
    · exact h3 W (fun m hm => hW m (by simp [hm])) i hi

/-! ### The statements -/

theorem KF_nil (w : ℕ) (r : ℤ) (π σ : Multiset ℕ) : KF [] w r π σ = if w = 0 then op [] r π σ else 0 := by
  simp only [KF, aFam, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
  by_cases h : w = 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The table of a weight, with the coefficients in front. -/
private theorem KF_eq (μ : List ℕ) (w : ℕ) :
    KF μ w = fun ρ π σ => ((aFam μ).map fun c => (if c.2.sum = w then c.1 else 0) * op c.2 ρ π σ).sum := by
  funext ρ π σ
  refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
  split_ifs <;> simp

/-- One more factor (−1)^{n−1}·y_n. -/
theorem KF_cons (n : ℕ) (μ : List ℕ) (w : ℕ) (r : ℤ) (π σ : Multiset ℕ) :
    KF (n :: μ) w r π σ =
      ∑ j ∈ Icc 1 n, if j ≤ w then (-1) ^ (n - 1) * (n.choose j : ℤ) * nop j (KF μ (w - j)) r π σ else 0 := by
  rw [sum_Icc_one, ← sum_map_range, KF, aFam, sum_map_flatMap, yl, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, List.map_map]
  rw [KF_eq μ (w - (i + 1)), nop_list_sum]
  split_ifs with hw
  · rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    simp only [Function.comp_apply, op]
    have e : ((i + 1) :: c.2).sum = i + 1 + c.2.sum := List.sum_cons
    by_cases hc : c.2.sum = w - (i + 1)
    · rw [if_pos hc, if_pos (by omega)]; ring
    · rw [if_neg hc, if_neg (by omega)]; ring
  · refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    simp only [Function.comp_apply]
    have e : ((i + 1) :: c.2).sum = i + 1 + c.2.sum := List.sum_cons
    rw [if_neg (by omega)]

/-- A sum over the monomials of a^μ with factors that depend only on the weight of the monomial is a
sum over the weights 0, …, |μ|. -/
theorem sum_aFam_eq (μ : List ℕ) (g : ℕ → ℤ) (r : ℤ) (π σ : Multiset ℕ) :
    ((aFam μ).map fun c => c.1 * g c.2.sum * op c.2 r π σ).sum = ∑ w ∈ range (μ.sum + 1), g w * KF μ w r π σ := by
  simp only [KF]
  rw [sum_mul_sum_map (range (μ.sum + 1)) g (aFam μ) fun w c => if c.2.sum = w then c.1 * op c.2 r π σ else 0]
  refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
  have hle := (aFam_shape μ c hc).2.1
  rw [sum_eq_single c.2.sum]
  · rw [if_pos rfl]; ring
  · intro w _ hw
    rw [if_neg (Ne.symm hw), mul_zero]
  · intro h
    exact absurd (mem_range.2 (by omega)) h

/-- Sizes: as for a single monomial, times the sum of the absolute values of the coefficients. -/
theorem abs_KF_le {W : ℕ} (hW : 1 ≤ W) (μ : List ℕ) (hμ : ∀ n ∈ μ, n ≤ W) (w : ℕ) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |KF μ w r π σ| ≤ 2 ^ (μ.sum + (4 * W + 1) * μ.length) := by
  have h1 : ∀ c ∈ aFam μ, |if c.2.sum = w then c.1 * op c.2 r π σ else 0| ≤ |c.1| * 2 ^ ((4 * W + 1) * μ.length) := by
    intro c hc
    obtain ⟨hl, -, hp⟩ := aFam_shape μ c hc
    have h2 := abs_op_le hW c.2 (hp W hμ) r hπ hσ
    rw [hl] at h2
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    · rw [abs_zero]
      positivity
  calc |KF μ w r π σ| ≤ ((aFam μ).map fun c => |if c.2.sum = w then c.1 * op c.2 r π σ else 0|).sum := abs_sum_map_le _ _
    _ ≤ ((aFam μ).map fun c => |c.1| * 2 ^ ((4 * W + 1) * μ.length)).sum := sum_map_le _ _ _ h1
    _ = ((aFam μ).map fun c => |c.1|).sum * 2 ^ ((4 * W + 1) * μ.length) := List.sum_map_mul_right ..
    _ ≤ 2 ^ μ.sum * 2 ^ ((4 * W + 1) * μ.length) := mul_le_mul_of_nonneg_right (sum_abs_aFam_le μ) (by positivity)
    _ = 2 ^ (μ.sum + (4 * W + 1) * μ.length) := (pow_add _ _ _).symm

end ClauseBound.Boson
