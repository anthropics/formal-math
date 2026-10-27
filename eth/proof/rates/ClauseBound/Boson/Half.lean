/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Dual
public import ClauseBound.Boson.Defs2
public import ClauseBound.Boson.WickPlus
public import ClauseBound.Boson.Basic
public import ClauseBound.Boson.Scalars
public import ClauseBound.Boson.Defs
public import ClauseBound.Boson.Size
public import ClauseBound.Boson.HalfSum
public import ClauseBound.Rec.Number

/-! # The pieces made from partitions: the two factors of a term of Q_s, and their sizes

The strings of λ bits are encoded by partitions of h. The piece number s, |s| ≤ 2h, is A_s(x,y,u,v) =
(h!/z_{μ(v)})·Q_s(a^{μ(x)}, t^{μ(v)}) at the entry (μ(u), μ(y)), where z_μ is the number of Appendix
B.

* Q_s is a sum over i ≤ 2h of products of two matrices; written out, a product of matrices is a sum
  over the monomials τ of one weight (`Qk_eq`). `topK` and `botK` are the two factors of such a
  term.
* A function that is a sum over i ≤ 2h and over the monomials τ of weight t(i) of products of two
  factors below 2^{eL h} and 2^{eR h} factors through the logarithm of the number of the pairs (i,
  τ),
  with functions below 2^{big h} (`factors`).
* For 2h + 1 different weights up to 4h, the number of these pairs is at most the number of
  monomials of all weights up to 4h (`sum_pz_le`).

The auxiliary statements are in the namespace `ClauseBound.Boson.Half`. -/

public section

namespace ClauseBound.Boson

open Finset

/-- The factor of a term of Q_s that carries a^μ: (−1)^i·Σ_{(c,L) ∈ a^μ} c·C(|L| + h, i)·L[r]. -/
@[expose] def topK (μx : List ℕ) (h i : ℕ) (r : ℤ) : Ker := fun π σ =>
  (-1) ^ i * ((aFam μx).map fun c => c.1 * ((c.2.sum + h).choose i : ℤ) * op c.2 r π σ).sum

/-- The other factor, with h!/z_ν in front: (h!/z_ν)·ν[r]. -/
@[expose] def botK (μv : List ℕ) (h : ℕ) (r : ℤ) : Ker := fun π σ => ((h.factorial / zz (μv : Multiset ℕ) : ℕ) : ℤ) * op μv r π σ

namespace Half

open HalfSum (coe_lst sum_lst pos_lst zero_notMem_parts)

/-! ### Q_s as a double sum of products -/

/-- The factor that carries the combination A: (−1)^i·Σ_{(c,L) ∈ A} c·C(|L| + h, i)·g(L). -/
@[expose] def fL (A : FA) (h i : ℕ) (g : List ℕ → ℤ) : ℤ :=
  (-1) ^ i * (A.map fun c => c.1 * ((c.2.sum + h).choose i : ℤ) * g c.2).sum

/-- A sum over a list of sums of products with a common second factor. -/
theorem list_sum_mul_sum {α ι : Type} (A : List α) (S : Finset ι) (k : α → ℤ) (F : α → ι → ℤ) (G : ι → ℤ) :
    (A.map fun c => k c * ∑ τ ∈ S, F c τ * G τ).sum = ∑ τ ∈ S, (A.map fun c => k c * F c τ).sum * G τ := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Q_s, with the products of matrices written out. -/
theorem Qk_eq (A : FA) (b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) :
    Qk A b s π σ = ∑ i ∈ range (2 * b.sum + 1), ∑ τ ∈ Pz (σ.sum + (b.sum - s - i)),
      fL A b.sum i (fun L => op L (s - b.sum + i) π τ) * op b (b.sum - s - i) τ σ := by
  unfold Qk fL mul2
  refine sum_congr rfl fun i _ => ?_
  rw [list_sum_mul_sum A _ (fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ)) (fun c τ => op c.2 (s - b.sum + i) π τ)
    (fun τ => op b (b.sum - s - i) τ σ), Finset.mul_sum]
  exact sum_congr rfl fun τ _ => (mul_assoc _ _ _).symm

/-! ### Sizes -/

/-- The exponent of the bound for the factor with a^μ. -/
@[expose] def eL (h : ℕ) : ℕ := h + (2 * h + (16 * h + 1) * h)

/-- The exponent of the bound for the factor with h!/z. -/
@[expose] def eR (h : ℕ) : ℕ := h * h + (16 * h + 1) * h

theorem eL_add_eR_lt (h : ℕ) : eL h + eR h < 40 * (h + 1) ^ 2 := by
  unfold eL eR
  nlinarith

/-! ### The number of pairs (i, τ) -/

theorem card_Pz (m : ℤ) : #(Pz m) = ClauseBound.Part.pz m := by
  unfold Pz ClauseBound.Part.pz
  split_ifs
  · exact card_P _
  · exact card_empty

/-- 2h + 1 different weights between 0 and 4h: at most as many monomials as there are of all the
weights up to 4h. -/
theorem sum_pz_le {h : ℕ} (t : ℕ → ℤ) (hinj : ∀ i j, t i = t j → i = j) (hle : ∀ i ∈ range (2 * h + 1), t i ≤ 4 * h) :
    ∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i) ≤ ∑ E ∈ range (4 * h + 1), Partitions.p E := by
  have h1 : ∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i) = ∑ i ∈ (range (2 * h + 1)).filter (fun i => 0 ≤ t i), Partitions.p (t i).toNat := by
    rw [sum_filter]
    exact sum_congr rfl fun i _ => rfl
  rw [h1, ← sum_image (f := Partitions.p) (g := fun i => (t i).toNat)]
  · refine sum_le_sum_of_subset fun E hE => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hE
    have h2 := hle i (mem_filter.1 hi).1
    exact mem_range.2 (by omega)
  · intro i hi j hj hij
    have hi' := (mem_filter.1 (mem_coe.1 hi)).2
    have hj' := (mem_filter.1 (mem_coe.1 hj)).2
    exact hinj i j (by have : (t i).toNat = (t j).toNat := hij; omega)

end Half

/-- The exponent of the bound in `factors`: 40(h + 1)^2, which exceeds eL h + eR h, plus the
logarithm, rounded up, of the number of monomials of weight at most 4h. -/
@[expose] def big (h : ℕ) : ℕ := 40 * (h + 1) ^ 2 + Nat.clog 2 (∑ E ∈ range (4 * h + 1), Partitions.p E)

namespace Half

theorem two_pow_lt_big {h e : ℕ} (he : e ≤ eL h + eR h) : (2 : ℤ) ^ e < 2 ^ big h :=
  pow_lt_pow_right₀ (by norm_num) (by have := eL_add_eR_lt h; unfold big; omega)

/-- A function that is a sum over i ≤ 2h and over the monomials τ of weight t(i) of products of two
bounded factors factors through the number of the pairs (i, τ). -/
theorem factors {Z Z' : Type} {h : ℕ} (F : Z → Z' → ℤ) (t : ℕ → ℤ) (f : ℕ → Multiset ℕ → Z → ℤ) (f' : ℕ → Multiset ℕ → Z' → ℤ)
    (hF : ∀ z z', F z z' = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (t i), f i τ z * f' i τ z')
    (hf : ∀ i ∈ range (2 * h + 1), ∀ τ ∈ Pz (t i), ∀ z, |f i τ z| ≤ 2 ^ eL h)
    (hf' : ∀ i ∈ range (2 * h + 1), ∀ τ ∈ Pz (t i), ∀ z, |f' i τ z| ≤ 2 ^ eR h) :
    Pieces.FactorsThrough F (Nat.clog 2 (∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i))) (2 ^ big h) := by
  refine ClauseBound.Rec.factorsThrough_of_sum ((range (2 * h + 1)).sigma fun i => Pz (t i)) F (fun x z => f x.1 x.2 z) (fun x z => f' x.1 x.2 z)
    _ _ (fun z z' => ?_) ?_ (by positivity) (fun x hx z => ?_) fun x hx z => ?_
  · rw [hF, sum_sigma']
  · rw [card_sigma]
    simp_rw [card_Pz]
    exact Nat.le_pow_clog (by norm_num) _
  · exact (hf x.1 (mem_sigma.1 hx).1 x.2 (mem_sigma.1 hx).2 z).trans_lt (two_pow_lt_big (Nat.le_add_right _ _))
  · exact (hf' x.1 (mem_sigma.1 hx).1 x.2 (mem_sigma.1 hx).2 z).trans_lt (two_pow_lt_big (Nat.le_add_left _ _))

end Half

variable {lam h : ℕ} (enc : Pieces.Bits lam → Nat.Partition h)

namespace Half

end Half

end ClauseBound.Boson
