/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Products
public import GeneralPieces.GenF.Bra

/-! # Proof of Lemma 9, paragraph "Generating functions": e^{A⁻}e^{B⁺} = e^κ·e^{B⁺}e^{A⁻} and the display that compares the two orders of the four exponentials

e^{A⁻} is a ring homomorphism. It maps B⁺ = Σ_k 𝖡_k·t_k to B⁺ + κ (`Phi_Bp`): A⁻ applied to B⁺ is κ =
Σ_{p,q} x_p·x'_q·J_p^-(ω₁)(J_q^+(ω₂)), where J_p^-(ω₁)(J_q^+(ω₂)) is the sum over k in the display
for κ
(`JmT_JpV`), and A⁻ applied to κ is 0. Hence e^{A⁻}(e^{B⁺}·w) = e^κ·e^{B⁺}·e^{A⁻}w
(`Phi_expW_Bp_mul`). Between e^{A⁺} on the left and e^{B⁻}·t^σ' on the right this is the display
with 𝒩 = e^{A⁺}e^{B⁺}e^{A⁻}e^{B⁻} (`stTwoOrders`): its first half, in 𝓛₊, for one value of the
Boolean `rd`, and its second half, in
𝓛₋ with A and B exchanged, for the other. In the Lean names the letters u and v stand for the
paper's ω₁ and ω₂. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X

/-- J_p^-(ω₁) on a multiple of t_k. -/
theorem JmU_C_mul_X (p : ℕ) (c : Lu) (k : ℕ) :
    JmU p (MvPolynomial.C c * MvPolynomial.X k) = MvPolynomial.C (c * (C ((k : ℚ) * (bet p (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - p))) := by
  have h0 : JmU p (MvPolynomial.C c) = 0 := (JmU p).map_algebraMap c
  rw [Derivation.leibniz, h0, smul_zero, add_zero, JmU, MvPolynomial.mkDerivation_X, smul_eq_mul, ← map_mul]

/-- J_p^-(ω₁) applied to J_q^+(ω₂) is the sum over k in the display for κ. -/
theorem JmT_JpV (p q : ℕ) : JmT p (JpV q) = emb (kapS p q) := by
  refine HahnSeries.ext (funext fun y => ?_)
  show JmU p ((JpV q).coeff y) = MvPolynomial.C ((kapS p q).coeff y)
  rw [JpV, HahnSeries.coeff_ofSuppBddBelow]
  have hR : ∀ x : ℤ, ((kapS p q).coeff y).coeff x = cfP (kapS p q) x y := fun _ => rfl
  by_cases hy : 0 ≤ y
  · rw [if_pos hy, JmU_C_mul_X]
    congr 1
    ext x
    rw [hR, kapS, cfP_sumP, ← mul_assoc, ← map_mul, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    have hk : (((y + q).toNat : ℕ) : ℤ) = y + q := Int.toNat_of_nonneg (by omega)
    rw [hk]
    have hkq : (((y + q).toNat : ℕ) : ℚ) = (y : ℚ) + q := by exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hk
    rw [hkq]
    by_cases h0 : y + q = 0
    · have hb : bet q (y + q) = 0 := by rw [bet, if_pos h0]
      rw [hb, Int.cast_zero, zero_mul, ite_self, if_neg (by omega)]
    · by_cases hx : x + y = -((p : ℤ) + q)
      · rw [if_pos (by omega), if_pos ⟨by omega, hx⟩, bet, if_neg h0, bet, if_neg (by omega)]
        push_cast
        ring
      · rw [if_neg (by omega), if_neg (fun g => hx g.2)]
  · rw [if_neg hy, map_zero]
    symm
    rw [← map_zero (MvPolynomial.C : Lu →+* Vu)]
    congr 1
    ext x
    rw [hR, kapS, cfP_sumP]
    split_ifs with h
    · rw [Scalars.choose_eq_zero (r := y + q - 1) (k := q - 1) (by omega) (by omega)]
      simp
    · rfl

/-- J_p^-(ω₁) kills the series without t_k. -/
theorem JmT_emb (p : ℕ) (s : S) : JmT p (emb s) = 0 := by
  refine HahnSeries.ext (funext fun y => ?_)
  show JmU p (MvPolynomial.C (s.coeff y)) = 0
  exact (JmU p).map_algebraMap (s.coeff y)

/-- The coefficient of x_i·x_{i'} in κ. -/
@[expose] noncomputable def kq (rd : Bool) (i i' : X) : S := sel rd (fun p => sel rd 0 (fun q => kapS p q) i') 0 i

theorem kap_eq (rd : Bool) : kap rd = bil (kq rd) := rfl

/-- The operator beside x_i in A⁻, applied to the coefficient of x_v in B⁺. -/
theorem DD_sel (rd : Bool) (i v : X) : DD rd i (sel rd 0 JpV v) = emb (kq rd i v) := by
  cases rd <;> rcases i with i | i <;> rcases v with v | v <;> simp only [DD, kq, sel, z0, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, if_true, Pi.zero_apply] <;>
    split_ifs <;> simp [JmT_JpV]

theorem DD_emb (rd : Bool) (i : X) (s : S) : DD rd i (emb s) = 0 := by
  cases rd <;> rcases i with i | i <;> simp only [DD, sel, z0, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, if_true, Pi.zero_apply] <;>
    split_ifs <;> simp [JmT_emb]

theorem kq_self (rd : Bool) (i : X) : kq rd i i = 0 := by
  cases rd <;> rcases i with i | i <;> simp only [kq, sel, z0, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, if_true, Pi.zero_apply] <;>
    split_ifs <;> rfl

/-- A⁻ applied to B⁺ is κ. -/
theorem dsum_Bp (rd : Bool) : dsum (DD rd) (Bp rd) = embW (kap rd) := by
  refine MvPowerSeries.ext fun α => ?_
  have hL := coeff_dsum (X := X) (A := Tv) (DD rd) (Bp rd) α
  have hlin : ∀ β : X →₀ ℕ, coeff β (Bp rd) = if β.degree = 1 then ∑ v ∈ β.support, sel rd 0 JpV v else 0 := fun _ => rfl
  rw [hL, embW, coeff_map, kap_eq, coeff_bil]
  by_cases h2 : α.degree = 2
  · rw [if_pos h2, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hlin, if_pos (by have := degree_sub_single hi; omega), map_sum, map_sum]
    simp only [DD_sel]
    refine Finset.sum_subset Finsupp.support_tsub fun v hv hv' => ?_
    have hvi : v = i := by
      by_contra hne
      apply hv'
      rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hne, tsub_zero]
      exact Finsupp.mem_support_iff.1 hv
    rw [hvi, kq_self, map_zero]
  · rw [if_neg h2, map_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hlin, if_neg (by have := degree_sub_single hi; omega), map_zero]

/-- e^{A⁻} maps B⁺ = Σ_k 𝖡_k·t_k to B⁺ + κ. -/
theorem Phi_Bp (rd : Bool) : Phi rd (Bp rd) = Bp rd + embW (kap rd) := by
  have h : ∀ (i j : X) (α : X →₀ ℕ), DD rd i (DD rd j (coeff α (Bp rd))) = 0 := by
    intro i j α
    have hlin : coeff α (Bp rd) = if α.degree = 1 then ∑ v ∈ α.support, sel rd 0 JpV v else 0 := rfl
    rw [hlin]
    split_ifs
    · rw [map_sum]
      simp only [DD_sel]
      rw [← map_sum, DD_emb]
    · simp
  have h1 := expD_of_sq_zero (X := X) (A := Tv) (w := Bp rd) (DD rd) h
  rw [dsum_Bp] at h1
  exact h1

theorem constantCoeff_embW_kap (rd : Bool) : constantCoeff (embW (kap rd)) = 0 := by
  rw [embW, constantCoeff_map, kap_eq, constantCoeff_bil, map_zero]

/-- e^{A⁻}·e^{B⁺} = e^κ·e^{B⁺}·e^{A⁻}. -/
theorem Phi_expW_Bp_mul (rd : Bool) (w : W) : Phi rd (expW (Bp rd) * w) = embW (expW (kap rd)) * (expW (Bp rd) * Phi rd w) := by
  have h0 : constantCoeff (Bp rd) = 0 := constantCoeff_lin (X := X) (A := Tv) _
  have h1 := expD_expW (X := X) (A := Tv) (w := Bp rd) (DD rd) h0
  have h2 : Phi rd (expW (Bp rd)) = expW (Phi rd (Bp rd)) := h1
  have h3 := expW_add (X := X) (R := Tv) h0 (constantCoeff_embW_kap rd)
  have h4 := map_expW (X := X) (R := S) (R' := Tv) emb (kap rd)
  have h5 : embW (expW (kap rd)) = expW (embW (kap rd)) := h4
  rw [map_mul, h2, Phi_Bp, h3, h5]
  ring

/-- The display on the two orders, one half: e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻} = e^κ·𝒩, as an equation
between the matrix entries. For one value of `rd` this is the equation in 𝓛₊, for the other (A and B
exchanged) the one in 𝓛₋. -/
theorem stTwoOrders : StTwoOrders := by
  intro rd E σ σ'
  rw [plusSide, normal, Phi_expW_Bp_mul, ← braW_embW_mul]
  congr 1
  ring

end GeneralPieces.GenF
