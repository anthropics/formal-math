/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Products
public import GeneralPieces.GenF.Bra

/-! # The lemma on the operators Q_s, paragraph "One Laurent polynomial": the coefficients of ⟨𝒩⟩

"Only the ∇_k with |k| ≤ E contribute to ⟨𝒩⟩, so the coefficient n_{μ'',ν''} of x^{μ''}x'^{ν''} in
⟨𝒩⟩ lies in 𝓛; and n_{∅,∅} = [σ = σ']"; and, in the paragraph "The constant", "For E = 0 we have ⟨𝒩⟩ =
1".
Here these three sentences (`StN1`, `StN2`, `StN3`) are derived from the differential equation of
⟨𝒩⟩ in the variables x_n, x'_n, which is the hypothesis `StNeq`: the derivative of ⟨𝒩⟩ for (σ, σ')
with respect
to a variable is a combination, with monomials of 𝓛 as coefficients, of the ⟨𝒩⟩ for (σ − l, σ'), l a
part of σ, and for (σ, σ' − k), k a part of σ'. So by induction on the degree every coefficient is a
Laurent polynomial; and since the factors are the images of the same elements of 𝓛 in 𝓛₊ and in 𝓛₋
(`toP_cL`, `toM_cL`), so are the coefficients. The paper argues by inspection of 𝒩 instead. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson

/-- The factor that comes with ∇_{−r} beside the variable x_i, in 𝓛₊ (`rd = false`) or in 𝓛₋
(`rd = true`): C(r−1, n−1)·ω₁^{r−n} for x_n and C(r−1, n−1)·ω₂^{r−n} for x'_n. -/
@[expose] noncomputable def cS (rd : Bool) (i : X) (r : ℤ) : S := sel rd (fun n => (bet n r : ℚ) • mo (r - n) 0) (fun n => (bet n r : ℚ) • mo 0 (r - n)) i

/-- The differential equation of ⟨𝒩⟩: one term for every different part l of σ (from A⁺ or B⁺) and
one for every different part k of σ' (from A⁻ or B⁻). -/
@[expose] def StNeq : Prop := ∀ (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) (i : X), σ.sum ≤ E →
  MvPowerSeries.pderiv S i (normal rd E σ σ') =
    ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i l) * normal rd E (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k)

/-- The same factor as an element of 𝓛: C(r−1, n−1)·ω₁^{r−n} for x_n and C(r−1, n−1)·ω₂^{r−n} for
x'_n. -/
@[expose] noncomputable def cL (i : X) (r : ℤ) : L :=
  Sum.elim (z0 fun n => (bet n r : ℚ) • Series.W (r - n) 0) (z0 fun n => (bet n r : ℚ) • Series.W 0 (r - n)) i

/-- In 𝓛₊ (`rd = false`) the factor is the image of that element of 𝓛. -/
theorem toP_cL (i : X) (r : ℤ) : toP (cL i r) = cS false i r := by
  rcases i with n | n <;> by_cases hn : n = 0 <;> simp [cS, cL, sel, z0, hn, toP_W]

/-- In 𝓛₋ (`rd = true`) it is the image of the same element of 𝓛. -/
theorem toM_cL (i : X) (r : ℤ) : toM (cL i r) = cS true i r := by
  rcases i with n | n <;> by_cases hn : n = 0 <;> simp [cS, cL, sel, z0, hn, toM_W]

/-- A coefficient from the derivative: (γ_i + 1) times the coefficient at γ + x_i is the coefficient
of the derivative at γ. -/
theorem coeff_add_single (F : PS) (γ : X →₀ ℕ) (i : X) :
    MvPowerSeries.coeff (γ + Finsupp.single i 1) F = ((γ i : ℚ) + 1)⁻¹ • MvPowerSeries.coeff γ (MvPowerSeries.pderiv S i F) := by
  have h : ((γ i : ℚ) + 1) ≠ 0 := by positivity
  rw [MvPowerSeries.coeff_pderiv, mul_natCast_succ, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem constantCoeff_ket (rd : Bool) (σ' : Multiset ℕ) : MvPowerSeries.constantCoeff (ket rd σ') = (σ'.map tT).prod := by
  unfold ket
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun k _ => ?_
  have e : MvPowerSeries.constantCoeff ((k : ℚ) • embW (sfB' rd k)) = (k : ℚ) • MvPowerSeries.constantCoeff (embW (sfB' rd k)) :=
    coeff_rat_smul (X := X) (R := Tv) 0 _ _
  rw [Function.comp_apply, map_add, MvPowerSeries.constantCoeff_C, e, embW, MvPowerSeries.constantCoeff_map, sfB', constantCoeff_lin, map_zero, smul_zero, add_zero]

/-- "n_{∅,∅} = [σ = σ']". -/
theorem stN2 : StN2 := by
  intro rd E σ σ'
  rw [normal, constantCoeff_braW, map_mul, map_mul, constantCoeff_expW (X := X) (R := Tv), constantCoeff_expW (X := X) (R := Tv), one_mul, one_mul, Phi,
    constantCoeff_expD (X := X) (A := Tv), constantCoeff_ket, bra_prod_tT]

/-- The coefficient at γ of the right side of the differential equation. -/
theorem coeff_rhs (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) (i : X) (γ : X →₀ ℕ) :
    MvPowerSeries.coeff γ (∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i l) * normal rd E (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k)) =
    ∑ l ∈ σ.toFinset, cS rd i l * MvPowerSeries.coeff γ (normal rd E (σ.erase l) σ') +
      ∑ k ∈ σ'.toFinset, (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * MvPowerSeries.coeff γ (normal rd E σ (σ'.erase k)) := by
  rw [map_add, map_sum, map_sum]
  simp only [MvPowerSeries.coeff_C_mul]

theorem sum_erase_le_of_le {σ : Multiset ℕ} {E : ℕ} (h : σ.sum ≤ E) (l : ℕ) : (σ.erase l).sum ≤ E := by
  by_cases hl : l ∈ σ
  · have := Multiset.sum_erase hl
    omega
  · rwa [Multiset.erase_of_notMem hl]

/-- "the coefficient n_{μ'',ν''} of x^{μ''}x'^{ν''} in ⟨𝒩⟩ lies in 𝓛": its forms in 𝓛₊ and in 𝓛₋ are
the images of one element of 𝓛. -/
theorem stN1 (hN : StNeq) : StN1 := by
  intro E σ σ' γ hσ
  suffices H : ∀ γ : X →₀ ℕ, ∀ σ σ' : Multiset ℕ, ∃ n : L, σ.sum ≤ E →
      MvPowerSeries.coeff γ (normal false E σ σ') = toP n ∧ MvPowerSeries.coeff γ (normal true E σ σ') = toM n by
    obtain ⟨n, hn⟩ := H γ σ σ'
    exact ⟨n, hn hσ⟩
  intro γ
  induction γ using induction_single with
  | h0 =>
    intro σ σ'
    refine ⟨if σ = σ' then 1 else 0, fun _ => ?_⟩
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, stN2, stN2]
    split_ifs <;> simp
  | hs γ i ih =>
    intro σ σ'
    choose nf hnf using ih
    refine ⟨((γ i : ℚ) + 1)⁻¹ • (∑ l ∈ σ.toFinset, cL i l * nf (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, (((k : ℚ) * σ'.count k) • cL i (-(k : ℤ))) * nf σ (σ'.erase k)), fun hσ => ⟨?_, ?_⟩⟩
    · rw [coeff_add_single, hN false E σ σ' i hσ, coeff_rhs, map_smul, map_add, map_sum, map_sum]
      congr 2
      · exact Finset.sum_congr rfl fun l _ => by rw [map_mul, toP_cL, (hnf _ _ (sum_erase_le_of_le hσ l)).1]
      · exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_smul, toP_cL, (hnf _ _ hσ).1]
    · rw [coeff_add_single, hN true E σ σ' i hσ, coeff_rhs, map_smul, map_add, map_sum, map_sum]
      congr 2
      · exact Finset.sum_congr rfl fun l _ => by rw [map_mul, toM_cL, (hnf _ _ (sum_erase_le_of_le hσ l)).2]
      · exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_smul, toM_cL, (hnf _ _ hσ).2]

/-- "For E = 0 we have ⟨𝒩⟩ = 1": for σ = σ' = ∅ all derivatives vanish. -/
theorem stN3 (hN : StNeq) : StN3 := by
  intro rd E
  ext γ : 1
  induction γ using induction_single with
  | h0 => rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, stN2, if_pos rfl, MvPowerSeries.coeff_zero_one]
  | hs γ i _ =>
    classical
    rw [coeff_add_single, hN rd E 0 0 i (by simp), MvPowerSeries.coeff_one, if_neg]
    · simp
    · intro h
      have := congrArg (fun m : X →₀ ℕ => m i) h
      simp at this

end GeneralPieces.GenF
