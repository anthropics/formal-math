/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.Constant
public import ClauseBound.Boson.Defs2

/-! # The lemma on the operators Q_s, for matrices, with the constant a[−h]b

The three claims: (a) Q_s(a,b) does not change if the two factors are exchanged in all its products
at once; (b) Q_s(a,b) = 0 on the monomials of weight E for |s| > E + h;
(c) the Q_s(a,b) with |s| ≤ E + h add up to (a[−h]b)·Id. Here a is a combination of monomials of
    weight at most h (a list of pairs of a coefficient and a list of parts),
b is one monomial of weight h, and an operator is its matrix, with entries (π, σ) for monomials
without a part 0; the factor of b^μ is put in where the pieces are defined. The condition h ≥ 1 of
the
paper is not needed.
The proof is that of the paper: the claims are linear in a (`Qk_eq_sum`, `Qk'_eq_sum`), and for a
monomial they are read off the one Laurent polynomial F. The theorems here
take the expansion of f₊ and f₋ as a hypothesis; in the file
proof/rates/GeneralPieces/GenF/Main.lean it is proved from the equation in the proof of Lemma 9 that
writes the products in the two orders as e^κ·N and e^{κ'}·N.
Lemma 9 of the paper, on the ring, is `AppHalfPieces.lemmaQ` in the file
proof/rates/GeneralPieces/Main.lean; it applies the theorems of this file to the expansion directly. -/

public section

namespace GeneralPieces.Series

open ClauseBound.Boson Finset

/-- The number a[−h]b for a combination a of monomials: the entry (1, b) of the matrix of a[−h]. -/
@[expose] def pairF (A : FA) (b : List ℕ) : ℤ := (A.map fun c => c.1 * op c.2 (-(b.sum : ℤ)) 0 (b : Multiset ℕ)).sum

/-- A sum over a finite set of sums over a list is the sum over the list of the sums over the set. -/
theorem sum_list_comm {ι α : Type} (s : Finset ι) (A : List α) (f : ι → α → ℤ) : ∑ i ∈ s, (A.map (f i)).sum = (A.map fun c => ∑ i ∈ s, f i c).sum := by
  induction A with
  | nil => simp
  | cons c A ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]

/-- For a monomial of weight h' ≤ h the sum over i ≤ 2h stops at H = h' + h, because C(H,i) = 0 for
i > H. -/
theorem sum_range_two_mul {H h : ℕ} (hH : H ≤ 2 * h) (g : ℕ → ℤ) :
    ∑ i ∈ range (2 * h + 1), (-1) ^ i * (H.choose i : ℤ) * g i = ∑ i ∈ range (H + 1), (-1) ^ i * (H.choose i : ℤ) * g i := by
  refine (sum_subset (range_subset_range.2 (by omega)) fun i _ hi => ?_).symm
  rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range, not_lt] at hi; omega)]
  simp

variable {A : FA} {b : List ℕ}

/-- Q_s(a,b) is linear in a, and a^{⟨i⟩} = C(H,i)·a for a monomial a. -/
theorem Qk_eq_sum (hA : A.Ok b.sum) (s : ℤ) (π σ : Multiset ℕ) : Qk A b s π σ = (A.map fun c => c.1 * qP c.2 b s π σ).sum := by
  unfold Qk
  simp only [← List.sum_map_mul_left]
  rw [sum_list_comm]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  rw [qP, ← sum_range_two_mul (h := b.sum) (by have := (hA c hc).2; omega), mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- The same with the factors exchanged. -/
theorem Qk'_eq_sum (hA : A.Ok b.sum) (s : ℤ) (π σ : Multiset ℕ) : Qk' A b s π σ = (A.map fun c => c.1 * qM c.2 b s π σ).sum := by
  unfold Qk'
  simp only [← List.sum_map_mul_left]
  rw [sum_list_comm]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  rw [qM, ← sum_range_two_mul (h := b.sum) (by have := (hA c hc).2; omega), mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- Claim (c) for monomials, with the constant a[−h]b. -/
theorem sum_qP_of (h : StExpansion) {a : List ℕ} (ha : Pos a) (hb : Pos b) (hab : a.sum ≤ b.sum) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), qP a b s π σ = if π = σ then op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) else 0 := by
  obtain ⟨G, hG⟩ := h a b ha hb
  obtain ⟨X⟩ := hG π σ hπ hσ
  obtain ⟨X0⟩ := hG 0 0 (by simp) (by simp)
  have h1 := X.sum_qP hab
  rw [X0.const hb] at h1
  exact_mod_cast h1

/-- Claim (a): Q_s(a,b) does not change if the two factors are exchanged in all its products at
once. -/
theorem Qk_eq_Qk'_of (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) (s : ℤ) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) : Qk A b s π σ = Qk' A b s π σ := by
  rw [Qk_eq_sum hA, Qk'_eq_sum hA]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨G, hG⟩ := h c.2 b (hA c hc).1 hb
  obtain ⟨X⟩ := hG π σ hπ hσ
  rw [X.qP_eq_qM]

/-- Claim (b): Q_s(a,b) vanishes on the monomials of weight E for |s| > E + h. -/
theorem Qk_eq_zero_of (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) {s : ℤ} {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hs : (σ.sum : ℤ) + b.sum < |s|) :
    Qk A b s π σ = 0 := by
  rw [Qk_eq_sum hA]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  obtain ⟨G, hG⟩ := h c.2 b (hA c hc).1 hb
  obtain ⟨X⟩ := hG π σ hπ hσ
  rw [X.qP_eq_zero (hA c hc).2 hs, mul_zero]

/-- Claim (c): on the monomials of weight E, the Q_s(a,b) with |s| ≤ E + h add up to (a[−h]b)·Id. -/
theorem sum_Qk_of (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), Qk A b s π σ = if π = σ then pairF A b else 0 := by
  simp only [Qk_eq_sum hA]
  rw [sum_list_comm]
  have h1 : (A.map fun c => ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), c.1 * qP c.2 b s π σ)
      = A.map fun c => c.1 * if π = σ then op c.2 (-(b.sum : ℤ)) 0 (b : Multiset ℕ) else 0 :=
    List.map_congr_left fun c hc => by rw [← mul_sum, sum_qP_of h (hA c hc).1 hb (hA c hc).2 hπ hσ]
  rw [h1]
  by_cases hπσ : π = σ
  · simp only [if_pos hπσ, pairF]
  · simp only [if_neg hπσ, mul_zero, List.map_const', List.sum_replicate, smul_zero]

end GeneralPieces.Series
