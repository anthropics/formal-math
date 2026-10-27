/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Borel
public import GeneralPieces.GenF.NormalL
public import ClauseBound.Boson.Basic

/-! # The lemma on the operators Q_s, paragraph "Generating functions": the series Y, and e^{B⁺}e^{B⁻} = Σ_ν x'^ν·Y(t^ν, ω₂)/ν!

The paper puts Y(a, ω) = Σ_r a[r]·ω^{r−h'} for a = t^μ of weight h'. Here `Yent e b τ σ` is the
entry (τ, σ) of its matrix, for the list b of the parts and with e x in the place of ω^x. The
operator a[r] raises the weight by r,
so the sum over r has one term. `Yent_cons` is the recursion Y(t_n·a, ω) = J_n^+(ω)·Y(a, ω) + Y(a,
ω)·J_n^-(ω), which is the recursion that defines the matrices a[r], multiplied by the powers of ω.
"Expanding the exponentials" is proved for the outer family (B in the first reading, A in the
second), applied to a monomial t^σ' (`bra_coeff_outer`, `Y1`): the series e^{B⁺}e^{B⁻}·t^σ'
satisfies
∂/∂x'_n (e^{B⁺}e^{B⁻}·t^σ') = J_n^+(v)·e^{B⁺}e^{B⁻}·t^σ' + e^{B⁺}e^{B⁻}·J_n^-(v)·t^σ'
(`pderiv_xo_outer`), which is the same recursion, and ν! times the coefficient of x'^ν is got by
differentiating once for every part of ν.
This takes the place of the count of the subsets with given multiplicities. The variables of the
inner family do not occur in this series (`pderiv_xi_outer`). -/

@[expose] public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson MvPowerSeries


/-! ### The series Y -/

section Yent
variable {R : Type} [CommRing R] [Algebra ℚ R]

/-- The entry (τ, σ) of Y(t^ν, ω) = Σ_r t^ν[r]·ω^{r−h}, where b lists the parts of ν, h is their sum
and e x stands for ω^x: t^ν[r] raises the weight by r, so only r = |τ| − |σ| contributes. -/
noncomputable def Yent (e : ℤ → R) (b : List ℕ) (τ σ : Multiset ℕ) : R := ((op b ((τ.sum : ℤ) - σ.sum) τ σ : ℤ) : ℚ) • e ((τ.sum : ℤ) - σ.sum - b.sum)

/-- Y(1, ω) is the identity. -/
theorem Yent_nil (e : ℤ → R) (h0 : e 0 = 1) (τ σ : Multiset ℕ) : Yent e [] τ σ = if τ = σ then 1 else 0 := by
  unfold Yent
  by_cases h : τ = σ
  · subst h
    simp [op, one, h0]
  · rw [if_neg h]
    have : op [] ((τ.sum : ℤ) - σ.sum) τ σ = 0 := by
      unfold op
      split_ifs
      · exact if_neg h
      · rfl
    rw [this, Int.cast_zero, zero_smul]

/-- Y(t_n·t^ν, ω) = J_n^+(ω)·Y(t^ν, ω) + Y(t^ν, ω)·J_n^-(ω), entry by entry: the recursion for the
operators t^ν[r], multiplied by the powers of ω. -/
theorem Yent_cons (e : ℤ → R) (he : ∀ x y, e x * e y = e (x + y)) (n : ℕ) (b : List ℕ) (τ σ : Multiset ℕ) :
    Yent e (n :: b) τ σ = ∑ l ∈ τ.toFinset, ((bet n l : ℚ) • e ((l : ℤ) - n)) * Yent e b (τ.erase l) σ +
      ∑ k ∈ σ.toFinset, (((k : ℚ) * σ.count k * bet n (-(k : ℤ))) • e (-(k : ℤ) - n)) * Yent e b τ (σ.erase k) := by
  unfold Yent
  rw [op, nop, Int.cast_add, Int.cast_sum, Int.cast_sum, add_smul, Finset.sum_smul, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Multiset.mem_toFinset.1 hl
    rw [cre, if_pos hl', Basic.sum_erase_cast hl', smul_mul_smul_comm, he, Int.cast_mul, List.sum_cons, Nat.cast_add]
    congr 2
    · congr 2
      ring
    · ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Multiset.mem_toFinset.1 hk
    rw [ann, Basic.sum_erase_cast hk', smul_mul_smul_comm, he, List.sum_cons, Nat.cast_add, show (τ.sum : ℤ) - σ.sum + k = τ.sum - (σ.sum - k) by ring,
      Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    congr 1
    · ring
    · congr 1
      ring

end Yent

/-! ### General rules -/

namespace Y

/-- The product rule for a product over a multiset. -/
theorem der_prod {R B ι : Type} [CommRing R] [CommRing B] [Algebra R B] [DecidableEq ι] (d : Derivation R B B) (s : Multiset ι) (f : ι → B) :
    d (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (d (f k) * ((s.erase k).map f).prod) := by
  rw [← Finset.sum_multiset_map_count]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons k s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head, add_comm,
      ← Multiset.sum_map_mul_left, mul_comm]
    congr 1
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun j hj => ?_)
    rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
    ring

variable {Z R : Type} [CommRing R] [Algebra ℚ R]

theorem pderiv_rat_smul (i : Z) (q : ℚ) (F : MvPowerSeries Z R) : pderiv R i (q • F) = q • pderiv R i F := map_rat_smul (pderiv R i).toLinearMap q F

theorem C_rat_smul (q : ℚ) (r : R) : (C (q • r) : MvPowerSeries Z R) = q • C r := map_rat_smul (C (σ := Z) (R := R)) q r

theorem mo_zero_mul (x y : ℤ) : mo 0 x * mo 0 y = mo 0 (x + y) := by rw [mo_mul_mo, add_zero]

theorem aL_nil (ι : ℕ → X) : aL ι [] = 0 := rfl

theorem aL_cons (ι : ℕ → X) (n : ℕ) (a : List ℕ) : aL ι (n :: a) = aL ι a + Finsupp.single (ι n) 1 := by
  rw [aL, aL, List.map_cons, List.sum_cons, add_comm]

end Y

open Y

/-! ### The outer family -/

/-- e^{B⁺}·e^{B⁻}·t^σ'. -/
noncomputable def outer (rd : Bool) (σ' : Multiset ℕ) : W := expW (Bp rd) * ket rd σ'

namespace Y

/-- The coefficient of ∇_k in J_n^-(v), as a function of the variable beside which J_n^-(v) stands. -/
noncomputable def cB (rd : Bool) (k : ℕ) : X → S := sel rd 0 fun n => (bet n (-(k : ℤ)) : ℚ) • mo 0 (-(k : ℤ) - n)

theorem emb_rat_smul (q : ℚ) (s : S) : emb (q • s) = q • emb s := by
  have h := map_rat_smul emb.toAddMonoidHom q s
  exact h

theorem embW_lin (c : X → S) : embW (lin c) = lin fun i => emb (c i) := by
  have h := map_lin (Y := X) (A := S) (A' := Tv) emb c
  exact h

theorem pderiv_factor (rd : Bool) (i : X) (k : ℕ) : pderiv Tv i (C (tT k) + (k : ℚ) • embW (sfB' rd k)) = C (emb ((k : ℚ) • cB rd k i)) := by
  rw [map_add, pderiv_C, zero_add, pderiv_rat_smul (R := Tv), sfB', embW_lin, pderiv_lin, emb_rat_smul, C_rat_smul (R := Tv)]
  rfl

/-- ∂/∂x_i of e^{B⁻}·t^σ': one of the factors is differentiated. -/
theorem pderiv_ket (rd : Bool) (i : X) (σ' : Multiset ℕ) :
    pderiv Tv i (ket rd σ') = ∑ k ∈ σ'.toFinset, C (emb (((k : ℚ) * σ'.count k) • cB rd k i)) * ket rd (σ'.erase k) := by
  rw [ket, der_prod (R := Tv) (B := W) (pderiv Tv i) σ']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_factor, ← Nat.cast_smul_eq_nsmul ℚ, ← smul_mul_assoc, ← C_rat_smul (R := Tv), ← emb_rat_smul, smul_smul, mul_comm (σ'.count k : ℚ), ket]

theorem constantCoeff_outer (rd : Bool) (σ' : Multiset ℕ) : constantCoeff (outer rd σ') = (σ'.map tT).prod := by
  rw [outer, map_mul, constantCoeff_expW (Bp rd), one_mul, constantCoeff_ket]

end Y

/-- ∂/∂x'_n (e^{B⁺}e^{B⁻}·t^σ') = J_n^+(v)·e^{B⁺}e^{B⁻}·t^σ' + e^{B⁺}e^{B⁻}·J_n^-(v)·t^σ'. -/
theorem pderiv_xo_outer (rd : Bool) {n : ℕ} (hn : 1 ≤ n) (σ' : Multiset ℕ) :
    pderiv Tv (xo rd n) (outer rd σ') = C (JpV n) * outer rd σ' +
      ∑ k ∈ σ'.toFinset, C (emb (((k : ℚ) * σ'.count k * bet n (-(k : ℤ))) • mo 0 (-(k : ℤ) - n))) * outer rd (σ'.erase k) := by
  rw [outer, Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_expW (xo rd n) (w := Bp rd) (constantCoeff_lin _), Bp, pderiv_lin, sel_xo rd _ _ hn, pderiv_ket, Finset.mul_sum, add_comm]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [cB, sel_xo rd _ _ hn, smul_smul, outer, Bp]
    ring

/-- The variables of the inner family do not occur in e^{B⁺}e^{B⁻}·t^σ'. -/
theorem pderiv_xi_outer (rd : Bool) (n : ℕ) (σ' : Multiset ℕ) : pderiv Tv (xi rd n) (outer rd σ') = 0 := by
  rw [outer, Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_expW (xi rd n) (w := Bp rd) (constantCoeff_lin _), Bp, pderiv_lin, sel_zero_xi, pderiv_ket, map_zero, zero_mul, mul_zero, add_zero,
    Finset.sum_eq_zero fun k _ => by rw [cB, sel_zero_xi, smul_zero, map_zero, map_zero, zero_mul], mul_zero]

/-- "Expanding the exponentials gives e^{B⁺}e^{B⁻} = Σ_ν x'^ν·Y(t^ν, v)/ν!": ν! times the
coefficient of x'^ν in e^{B⁺}e^{B⁻}·t^σ' has, at t^τ, the coefficient ⟨τ|Y(t^ν, v)|σ'⟩. -/
theorem bra_coeff_outer (rd : Bool) (b : List ℕ) (hb : Pos b) (τ σ' : Multiset ℕ) :
    bra τ (fac (aL (xo rd) b) • coeff (aL (xo rd) b) (outer rd σ')) = Yent (mo 0) b τ σ' := by
  induction b generalizing τ σ' with
  | nil => rw [aL_nil, fac_zero, one_smul, coeff_zero_eq_constantCoeff_apply, constantCoeff_outer, bra_prod_tT, Yent_nil _ mo_zero]
  | cons n b ih =>
    have hn : 1 ≤ n := hb n List.mem_cons_self
    have hb' : Pos b := fun m hm => hb m (List.mem_cons_of_mem _ hm)
    rw [aL_cons, borel_step (aL (xo rd) b) (xo rd n) (outer rd σ'), pderiv_xo_outer rd hn, map_add, map_sum, coeff_C_mul, smul_add, Finset.smul_sum, bra_add, bra_sum, ← mul_smul_comm, bra_JpV_mul,
      Yent_cons _ mo_zero_mul]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by rw [ih hb']
    · exact Finset.sum_congr rfl fun k _ => by rw [coeff_C_mul, ← mul_smul_comm, bra_emb_mul, ih hb']

/-- The same with the definitions written out. -/
theorem Y1 (rd : Bool) (b : List ℕ) (hb : Pos b) (τ σ' : Multiset ℕ) :
    bra τ (fac (aL (xo rd) b) • coeff (aL (xo rd) b) (expW (Bp rd) * ket rd σ')) =
      ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum) :=
  bra_coeff_outer rd b hb τ σ'

/-- t₀ does not occur: the entries of t^ν[r] in the rows of the monomials with t₀ vanish. -/
theorem op_eq_zero_of_zero_mem (b : List ℕ) (r : ℤ) {τ σ : Multiset ℕ} (hτ : 0 ∈ τ) (hσ : 0 ∉ σ) : op b r τ σ = 0 := by
  induction b generalizing r τ σ with
  | nil =>
    unfold op
    split_ifs
    · exact if_neg fun h : τ = σ => hσ (h ▸ hτ)
    · rfl
  | cons n b ih =>
    rw [op, nop, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro k _
      rw [ann, ih _ hτ fun h => hσ (Multiset.mem_of_mem_erase h), mul_zero, mul_zero]
    · intro l hl
      by_cases h0 : l = 0
      · rw [h0, bet, if_pos Nat.cast_zero, zero_mul]
      · rw [cre, if_pos (Multiset.mem_toFinset.1 hl), ih _ ((Multiset.mem_erase_of_ne (Ne.symm h0)).2 hτ) hσ, mul_zero]

end GeneralPieces.GenF
