/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs
import Ov.Core.Wire

/-!
# Sums up to ε: powers, extraction of a coefficient, restrictions

The helpers of the lemma `few`. A local map with entries in `K[ε]` is a family of matrices of polynomials;
`polyApp` is the array that it makes of a tensor.
-/

namespace Nc.Price

open Ov Ov.Ten Finset Polynomial

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- The array over `K[ε]` that local maps with polynomial entries make of a tensor. -/
noncomputable def polyApp {α : I → Type} (z : Ten K I) (Φ : ∀ p, α p → z.ι p → Polynomial K)
    (x : ∀ p, α p) : Polynomial K :=
  ∑ y : ∀ p, z.ι p, (∏ p, Φ p (x p) (y p)) * C (z.val y)

/-- A product of images of tensors is the image of the product of the tensors. -/
theorem polyApp_prod {τ : Type} [Fintype τ] [DecidableEq τ] {α : τ → I → Type} (b : τ → Ten K I)
    (Φ : ∀ i p, α i p → (b i).ι p → Polynomial K) (x : ∀ p i, α i p) :
    polyApp (α := fun p => ∀ i, α i p) (Ten.prod b) (fun p a c => ∏ i, Φ i p (a i) (c i)) x =
      ∏ i, polyApp (b i) (Φ i) fun p => x p i := by
  unfold polyApp
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piComm _) _ _ fun y => ?_
  change (∏ p, ∏ i, Φ i p (x p i) (y p i)) * C (∏ i, (b i).val fun p => y p i) =
    ∏ i, (∏ p, Φ i p (x p i) (y p i)) * C ((b i).val fun p => y p i)
  rw [map_prod, Finset.prod_comm, ← Finset.prod_mul_distrib]

/-- **Paper: Lemma few, powers of a sum up to ε, the words.** If the images of the b k have the sum
ε ^ D * t up to higher powers, then the products of N images, over all words, have the sum
ε ^ (N * D) * t^N up to higher powers. -/
theorem coeff_sum_words {κ : Type} [Fintype κ] {D : ℕ} {t : Ten K I} {b : κ → Ten K I}
    {L : ∀ k p, t.ι p → (b k).ι p → Polynomial K}
    (hL : ∀ x, ∀ i ≤ D, (∑ k, polyApp (b k) (L k) x).coeff i = if i = D then t.val x else 0)
    (N : ℕ) (x : ∀ p, Fin N → t.ι p) {j : ℕ} (hj : j ≤ N * D) :
    (∑ w : Fin N → κ, ∏ i, polyApp (b (w i)) (L (w i)) fun p => x p i).coeff j =
      if j = N * D then (Ten.kpow t N).val x else 0 := by
  classical
  rw [← Fintype.prod_sum (f := fun (i : Fin N) k => polyApp (b k) (L k) fun p => x p i)]
  have hQ : ∀ i : Fin N, ∃ Q : Polynomial K, (∑ k, polyApp (b k) (L k) fun p => x p i) = X ^ D * Q ∧
      Q.coeff 0 = t.val fun p => x p i := by
    intro i
    obtain ⟨Q, hQ⟩ : X ^ D ∣ ∑ k, polyApp (b k) (L k) fun p => x p i :=
      X_pow_dvd_iff.2 fun d hd => (hL _ d hd.le).trans (if_neg hd.ne)
    refine ⟨Q, hQ, ?_⟩
    have := (hL (fun p => x p i) D le_rfl).trans (if_pos rfl)
    rwa [hQ, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at this
  choose Q hQ hQ0 using hQ
  simp only [hQ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm D N, coeff_X_pow_mul']
  rcases eq_or_lt_of_le hj with rfl | hlt
  · rw [if_pos le_rfl, if_pos rfl, Nat.sub_self, coeff_zero_prod]
    exact Finset.prod_congr rfl fun i _ => hQ0 i
  · rw [if_neg hlt.not_ge, if_neg hlt.ne]

/-- The coefficient of ε ^ D of a product of polynomials, as a sum over the choices of the exponents. -/
theorem coeff_prod_choices {τ : Type} [Fintype τ] [DecidableEq τ] (f : τ → Polynomial K) (D : ℕ) :
    (∏ p, f p).coeff D =
      ∑ d : τ → Fin (D + 1), if (∑ p, (d p).1) = D then ∏ p, (f p).coeff (d p) else 0 := by
  rw [← Polynomial.coeff_coe, show ((∏ p, f p : Polynomial K) : PowerSeries K) = ∏ p, (f p : PowerSeries K) from
    map_prod Polynomial.coeToPowerSeries.ringHom f univ, PowerSeries.coeff_prod, ← Finset.sum_filter]
  simp only [Polynomial.coeff_coe]
  refine Finset.sum_bij' (fun l hl p => ⟨l p, ?_⟩) (fun d _ => Finsupp.equivFunOnFinite.symm fun p => (d p).1)
    ?_ ?_ ?_ ?_ ?_
  · rw [Finset.mem_finsuppAntidiag] at hl
    exact Nat.lt_succ_of_le (hl.1 ▸ Finset.single_le_sum (fun q _ => Nat.zero_le (l q)) (Finset.mem_univ p))
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    simpa using hl.1
  · intro d hd
    simp only [Finset.mem_filter] at hd
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by simpa using hd.2, Finset.subset_univ _⟩
  · intro l _
    ext p
    simp
  · intro d _
    funext p
    simp
  · intro l _
    rfl

/-- **Paper: Lemma few, extraction of a coefficient.** The coefficient of ε ^ D of the image of a tensor z under
local maps with polynomial entries is a sum of at most (D + 1) ^ #parties restrictions of z, so a spectral point
is at most that many times its value at z. -/
theorem le_coeff (F : Spec K I) [Nonempty I] {s z : Ten K I} {D : ℕ} (Φ : ∀ p, s.ι p → z.ι p → Polynomial K)
    (h : ∀ x, s.val x = (polyApp z Φ x).coeff D) :
    F.F s ≤ ((D : ℝ) + 1) ^ Fintype.card I * F.F z := by
  classical
  let p₀ : I := Classical.arbitrary I
  let L : (I → Fin (D + 1)) → Loc s z := fun d p a c =>
    (if p = p₀ then (if (∑ q, (d q).1) = D then (1 : K) else 0) else 1) * (Φ p a c).coeff (d p)
  have hs : SumRestr s fun _ : I → Fin (D + 1) => z := by
    refine ⟨L, fun x => ?_⟩
    simp only [h, polyApp, Polynomial.finsetSum_coeff, coeff_mul_C, coeff_prod_choices, app, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ p₀, if_pos (Finset.mem_univ _)]
    split_ifs <;> simp
  refine (F.le_sum _ _ hs).trans (le_of_eq ?_)
  simp [Finset.card_univ]

end Nc.Price
