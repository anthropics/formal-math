/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Products
public import GeneralPieces.GenF.Kappa
public import ClauseBound.Boson.Basic
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Weight

/-! # Lemma 9 (Appendix B), paragraph "One Laurent polynomial": comparing the coefficients of x^μ·x'^ν in display (51), which writes the two orders of the product as e^κ·𝒩 in 𝓛₊ and e^{κ'}·𝒩 in 𝓛₋ (below: the display on the two orders)

"Comparing the coefficients of x^μ·x'^ν in (51) gives f_± = μ!·ν!·Σ
Γ_{μ',ν'}·ε_±^{|μ'|+|ν'|}·n_{μ'',ν''}, summed over all pairs of partitions μ', μ'' with union μ and
ν', ν'' with union ν"
(`compare_plus`, `compare_minus`). Here a and b list the parts of μ and ν, the monomial x^μ·x'^ν is
its exponent `ex a b`, and a pair of splittings is a pair (β, γ) of exponents with
β + γ = `ex a b`: β is the exponent of x^{μ'}·x'^{ν'} and γ that of x^{μ''}·x'^{ν''}.
Taken as hypotheses (the statements `StTwoOrders`, `StY`, `StN1`, `StN2`, `StN3`): display (51);
that ⟨Y(a,ω₁)·Y(b,ω₂)⟩ and ⟨Y(b,ω₂)·Y(a,ω₁)⟩ are μ!·ν! times the coefficients of x^μ·x'^ν on its
left sides;
that the coefficients of ⟨𝒩⟩ lie in 𝓛 and are the same in both readings; n_{∅,∅} = [σ = σ']; and ⟨𝒩⟩ =
1 for E = 0. The coefficients of e^κ and e^{κ'} are those of `coeff_expW_kap_false`,
`coeff_expW_kap_true`.
The result is the statement `GeneralPieces.Series.StExpansion`, from which the later paragraphs of
the proof start (`stExpansion_of`). -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

/-! ### The exponent of x^μ·x'^ν -/

/-- The exponent of x^μ·x'^ν, for the lists a, b of the parts of μ, ν. -/
@[expose] noncomputable def ex (a b : List ℕ) : X →₀ ℕ := aL Sum.inl a + aL Sum.inr b

/-- In the `false` case (the first order, Y(a,ω₁)·Y(b,ω₂)) the parts of a enter through `xi` and
those of b through `xo`; the sum is the exponent of x^μ·x'^ν. -/
theorem ex_false (a b : List ℕ) : aL (xi false) a + aL (xo false) b = ex a b := rfl

/-- In the `true` case (the second order, Y(b,ω₂)·Y(a,ω₁)) the roles are exchanged: b enters through
`xi` and a through `xo`. -/
theorem ex_true (a b : List ℕ) : aL (xi true) b + aL (xo true) a = ex a b := add_comm _ _

/-- |μ| + |ν| = h' + h. -/
theorem wtX_ex (a b : List ℕ) : wtX (ex a b) = a.sum + b.sum := by
  rw [ex, map_add, aL, aL, wtX_list_inl, wtX_list_inr]

/-- Only the variables with an index in the list occur. -/
theorem aL_apply_ne_zero {ι : ℕ → X} {a : List ℕ} {i : X} (h : aL ι a i ≠ 0) : ∃ n ∈ a, i = ι n := by
  classical
  induction a with
  | nil => exact absurd rfl h
  | cons n a ih =>
    unfold aL at h ih
    rw [List.map_cons, List.sum_cons, Finsupp.add_apply] at h
    by_cases h1 : Finsupp.single (ι n) 1 i = 0
    · rw [h1, zero_add] at h
      obtain ⟨m, hm, e⟩ := ih h
      exact ⟨m, List.mem_cons_of_mem _ hm, e⟩
    · rw [Finsupp.single_apply] at h1
      have h2 : ι n = i := by
        by_contra h2
        exact h1 (if_neg h2)
      exact ⟨n, List.mem_cons_self, h2.symm⟩

/-- A divisor of x^μ·x'^ν of weight 0 is 1, because all parts are positive. -/
theorem eq_zero_of_wtX {a b : List ℕ} (ha : Pos a) (hb : Pos b) {γ : X →₀ ℕ} (hγ : γ ≤ ex a b) (h0 : wtX γ = 0) : γ = 0 := by
  ext i
  by_contra hi
  have h1 : ex a b i ≠ 0 := fun h => hi (Nat.le_zero.1 (h ▸ hγ i))
  have h2 : (Sum.elim id id : X → ℕ) i ≠ 0 := by
    rw [ex, Finsupp.add_apply] at h1
    by_cases h3 : aL Sum.inl a i = 0
    · rw [h3, zero_add] at h1
      obtain ⟨n, hn, rfl⟩ := aL_apply_ne_zero h1
      exact (Nat.pos_iff_ne_zero.1 (hb n hn))
    · obtain ⟨n, hn, rfl⟩ := aL_apply_ne_zero h3
      exact (Nat.pos_iff_ne_zero.1 (ha n hn))
  have h4 := Finsupp.le_weight (Sum.elim id id : X → ℕ) h2 γ
  exact hi (Nat.le_zero.1 (h0 ▸ h4))

/-- In a splitting of x^μ·x'^ν the first factor has the full weight only if the second is 1. -/
theorem snd_eq_zero {a b : List ℕ} (ha : Pos a) (hb : Pos b) {p : (X →₀ ℕ) × (X →₀ ℕ)} (hp : p ∈ antidiagonal (ex a b)) (hw : wtX p.1 = a.sum + b.sum) :
    p.2 = 0 := by
  have e := mem_antidiagonal.1 hp
  have h1 : wtX p.1 + wtX p.2 = a.sum + b.sum := by rw [← map_add, e, wtX_ex]
  exact eq_zero_of_wtX ha hb (e ▸ le_add_self) (by omega)

/-! ### Comparing coefficients -/

/-- f₋ is f₊ with the names exchanged. -/
theorem fM_eq_fP (a b : List ℕ) (π σ : Multiset ℕ) : fM a b π σ = fP b a π σ := by
  unfold fM fP
  rw [add_comm]

/-- A product a[r]∘b[−r] has no entries between monomials of different weights. -/
theorem mul2_eq_zero_of_sum_ne (a b : List ℕ) {r r' : ℤ} (h : r + r' = 0) {π σ : Multiset ℕ} (hne : π.sum ≠ σ.sum) : mul2 a r b r' π σ = 0 := by
  unfold mul2
  refine Finset.sum_eq_zero fun τ _ => ?_
  by_contra h0
  have h1 := op_grade (left_ne_zero_of_mul h0)
  have h2 := op_grade (right_ne_zero_of_mul h0)
  exact hne (by omega)

/-- So f₊ = 0 if the two monomials have different weights. The paper takes both of weight E. -/
theorem fP_eq_zero (a b : List ℕ) {π σ : Multiset ℕ} (hne : π.sum ≠ σ.sum) : fP a b π σ = 0 := ext_cf fun x y => by
  have h := cfP_fP a b π σ x y
  rw [cfP] at h
  rw [h, cf_zero]
  split_ifs with h1
  · rw [mul2_eq_zero_of_sum_ne a b (by omega) hne, Int.cast_zero]
  · rfl

/-- Comparing the coefficients of x^μ·x'^ν in the first half of display (51). -/
theorem compare_plus (h15 : StTwoOrders) (hY : StY) {a b : List ℕ} (ha : Pos a) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hw : π.sum = σ.sum)
    {E : ℕ} (hE : π.sum ≤ E) : fP a b π σ = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • epsP ^ wtX p.1) * coeff p.2 (normal false E π σ) := by
  rw [← hY false E a b π σ ha hb hπ hσ hw hE, ex_false, h15, coeff_mul]
  simp_rw [coeff_expW_kap_false]

/-- Comparing the coefficients of x^μ·x'^ν in the second half. -/
theorem compare_minus (h15 : StTwoOrders) (hY : StY) {a b : List ℕ} (ha : Pos a) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hw : π.sum = σ.sum)
    {E : ℕ} (hE : π.sum ≤ E) : fM a b π σ = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • epsM ^ wtX p.1) * coeff p.2 (normal true E π σ) := by
  rw [fM_eq_fP, ← hY true E b a π σ hb ha hπ hσ hw hE, ex_true, h15, coeff_mul]
  simp_rw [coeff_expW_kap_true]

/-! ### The expansion -/

/-- A sum over the terms of a list that pass a test. -/
theorem sum_filter_map {ι : Type} (l : List ι) (F : ι → ℚ × ℕ × L) (H : ℕ) :
    (((l.map F).filter fun c => c.2.1 = H).map fun c => c.1).sum = (l.map fun x => if (F x).2.1 = H then (F x).1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.filter_cons, decide_eq_true_eq, List.sum_cons]
    split_ifs with h
    · rw [List.map_cons, List.sum_cons, ih]
    · rw [ih, zero_add]

end GeneralPieces.GenF

namespace GeneralPieces

open GeneralPieces.Series GeneralPieces.GenF ClauseBound.Boson MvPowerSeries Finset

/-- The expansion of f₊ and f₋ from display (51): the terms are indexed by the splittings (β, γ) of
x^μ·x'^ν, with Γ_c = μ!·ν!·Γ_β, N_c the weight of β, and n_c the coefficient of γ in ⟨𝒩⟩;
the number G is μ!·ν!·Γ_{μ,ν}. For monomials of different weights, which the paper does not
consider, f₊ = f₋ = 0 and one term with n_c = 0 serves. -/
theorem stExpansion_of (h15 : StTwoOrders) (hN1 : StN1) (hN2 : StN2) (hN3 : StN3) (hY : StY) : StExpansion := by
  intro a b ha hb
  refine ⟨fac (ex a b) * gam (ex a b), fun π σ hπ hσ => ?_⟩
  by_cases hw : π.sum = σ.sum
  swap
  · have hne : π ≠ σ := fun h => hw (by rw [h])
    exact ⟨{  terms := [(fac (ex a b) * gam (ex a b), a.sum + b.sum, 0)]
              le := fun c hc => by rw [List.mem_singleton.1 hc]
              plus := by simp [fP_eq_zero a b hw]
              minus := by simp [fM_eq_fP, fP_eq_zero b a hw]
              top := fun c hc _ => by rw [List.mem_singleton.1 hc, if_neg hne]
              tot := by simp
              vac := fun h1 h2 => absurd (h1.trans h2.symm) hne }⟩
  choose n hnP hnM using fun γ => hN1 π.sum π σ γ le_rfl
  have hsum : ∀ (ε : S) (φ : L → S), (((antidiagonal (ex a b)).toList.map fun p => (fac (ex a b) * gam p.1, wtX p.1, n p.2)).map
      fun c : ℚ × ℕ × L => c.1 • (ε ^ c.2.1 * φ c.2.2)).sum = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • ε ^ wtX p.1) * φ (n p.2) := by
    intro ε φ
    rw [List.map_map, Finset.sum_map_toList, smul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [Function.comp_apply, smul_mul_assoc, smul_smul]
  refine ⟨{ terms := (antidiagonal (ex a b)).toList.map fun p => (fac (ex a b) * gam p.1, wtX p.1, n p.2)
            le := ?_, plus := ?_, minus := ?_, top := ?_, tot := ?_, vac := ?_ }⟩
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have e := mem_antidiagonal.1 (mem_toList.1 hp)
    have h1 : wtX p.1 + wtX p.2 = a.sum + b.sum := by rw [← map_add, e, wtX_ex]
    exact h1 ▸ Nat.le_add_right _ _
  · rw [hsum epsP toP, compare_plus h15 hY ha hb hπ hσ hw le_rfl]
    simp_rw [hnP]
  · rw [hsum epsM toM, compare_minus h15 hY ha hb hπ hσ hw le_rfl]
    simp_rw [hnM]
  · intro c hc hH
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have h0 := snd_eq_zero ha hb (mem_toList.1 hp) hH
    refine toP_injective ?_
    change toP (n p.2) = _
    rw [← hnP, h0, coeff_zero_eq_constantCoeff_apply, hN2]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  · rw [sum_filter_map, Finset.sum_map_toList]
    rw [Finset.sum_eq_single (ex a b, 0)]
    · rw [if_pos (wtX_ex a b)]
    · intro p hp hne
      refine if_neg fun hH => hne ?_
      have h0 := snd_eq_zero ha hb hp hH
      have e := mem_antidiagonal.1 hp
      rw [h0, add_zero] at e
      exact Prod.ext e h0
    · intro h
      exact absurd (mem_antidiagonal.2 (add_zero _)) h
  · intro hπ0 hσ0 c hc hlt
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have e := mem_antidiagonal.1 (mem_toList.1 hp)
    have hne : p.2 ≠ 0 := by
      intro h0
      rw [h0, add_zero] at e
      have h1 : wtX p.1 < a.sum + b.sum := hlt
      rw [e, wtX_ex] at h1
      exact lt_irrefl _ h1
    refine toP_injective ?_
    change toP (n p.2) = _
    rw [← hnP, hπ0, hσ0, hN3, map_zero, coeff_one, if_neg hne]

end GeneralPieces
