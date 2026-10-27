/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.Rings
public import ClauseBound.Boson.Scalars
public import Mathlib.RingTheory.Derivation.Basic

/-! # The lemma on the operators Q_s, paragraph "Series": termwise differentiation, and display (49)

This follows the paragraph "Series" of the proof of the lemma on the operators Q_s (Appendix B),
from "and are closed under termwise differentiation" to display (49), and the two sentences of the
paragraph "Generating functions" that evaluate the sums over k in κ and κ'. As in `Rings.lean`,
everything is proved once in the ring `S` with an inner variable u and an outer variable v, and then
read twice: in 𝓛₊, ∂_{ω₁} = ∂/∂u and ∂_{ω₂} = ∂/∂v; in 𝓛₋ it is the other way round.
The differentiations are derivations of the ℚ-algebra `S` in Mathlib's sense (`du`, `dv`); `cf_du`,
`cf_dv` say that they act term by term. The product rule is proved first for u·∂/∂u and
v·∂/∂v, which multiply the coefficient of u^x·v^y by x and by y (`twist_mul`), and ∂/∂u is u⁻¹ times
u·∂/∂u.
Display (49) is proved in any ring with two derivations and an element ε with D₁ε = −ε² and D₂ε = ε²
(`displayGamma`), which is why Γ_{j,n} is the same for both signs; it is the number
`ClauseBound.Boson.Gam j n` = n·C(−n−1, j−1). The paper does not write out the sum over k in κ';
`kappa'_sum` does. -/

@[expose] public section

namespace GeneralPieces.Series

open LaurentPolynomial

/-! ### An operator that acts on every coefficient of a series -/

section Twist
variable {R : Type} [CommRing R]

/-- The series whose coefficient of v^y is D_y applied to the coefficient of v^y in f. -/
def twist (D : ℤ → R →+ R) (f : HahnSeries ℤ R) : HahnSeries ℤ R where
  coeff y := D y (f.coeff y)
  isPWO_support' := f.isPWO_support.mono fun y hy h => hy (by simp [h])

theorem support_twist (D : ℤ → R →+ R) (f : HahnSeries ℤ R) : (twist D f).support ⊆ f.support :=
  fun y hy h => hy (by simp [twist, h])

/-- If D_{i+j}(ab) = D_i(a)·b + a·D_j(b), the operator satisfies the product rule. -/
theorem twist_mul (D : ℤ → R →+ R) (hD : ∀ i j a b, D (i + j) (a * b) = D i a * b + a * D j b) (f g : HahnSeries ℤ R) :
    twist D (f * g) = twist D f * g + f * twist D g := by
  ext y
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (support_twist D f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_twist D g), ← Finset.sum_add_distrib]
  change D y ((f * g).coeff y) = _
  rw [HahnSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have h : ij.1 + ij.2 = y := (Finset.mem_antidiagonal.1 hij).2.2
  rw [← h, hD]
  rfl

end Twist

/-! ### u·∂/∂u and v·∂/∂v -/

/-- u·d/du on the Laurent polynomials in u: the coefficient of u^x is multiplied by x. -/
noncomputable def thI : LaurentPolynomial ℚ →+ LaurentPolynomial ℚ where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.coeff.support (fun x => (x : ℚ) * p.coeff x) fun x h => by
    rw [Finsupp.mem_support_iff]
    exact right_ne_zero_of_mul h)
  map_zero' := by ext x; simp
  map_add' p q := by ext x; simp [mul_add]

theorem coeff_thI (p : LaurentPolynomial ℚ) (x : ℤ) : (thI p).coeff x = x * p.coeff x := rfl

theorem thI_single (a : ℤ) (r : ℚ) : thI (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single a ((a : ℚ) * r) := by
  ext x
  rw [coeff_thI, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-- The product rule for u·d/du on the Laurent polynomials. -/
theorem thI_mul (p q : LaurentPolynomial ℚ) : thI (p * q) = thI p * q + p * thI q := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, map_add, hf, hg, map_add]; ring
  | single a r =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => rw [mul_add, map_add, hf, hg, map_add]; ring
    | single b s =>
      rw [thI_single, thI_single, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, thI_single,
        ← AddMonoidAlgebra.single_add]
      congr 1
      push_cast
      ring

/-- u·∂/∂u on the series. -/
noncomputable def thU (f : S) : S := twist (fun _ => thI) f

/-- v·∂/∂v on the series. -/
noncomputable def thV (f : S) : S := twist (fun y => (y : ℚ) • AddMonoidHom.id _) f

theorem cf_thU (f : S) (x y : ℤ) : cf (thU f) x y = x * cf f x y := rfl

theorem cf_thV (f : S) (x y : ℤ) : cf (thV f) x y = y * cf f x y := rfl

theorem thU_mul (f g : S) : thU (f * g) = thU f * g + f * thU g := twist_mul _ (fun _ _ a b => thI_mul a b) f g

theorem thV_mul (f g : S) : thV (f * g) = thV f * g + f * thV g :=
  twist_mul _ (fun i j a b => by
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    push_cast
    rw [add_smul, smul_mul_assoc, mul_smul_comm]) f g

theorem thU_add (f g : S) : thU (f + g) = thU f + thU g := ext_cf fun x y => by simp [cf_thU, mul_add]

theorem thV_add (f g : S) : thV (f + g) = thV f + thV g := ext_cf fun x y => by simp [cf_thV, mul_add]

theorem thU_smul (r : ℚ) (f : S) : thU (r • f) = r • thU f := ext_cf fun x y => by simp [cf_thU, mul_left_comm]

theorem thV_smul (r : ℚ) (f : S) : thV (r • f) = r • thV f := ext_cf fun x y => by simp [cf_thV, mul_left_comm]

/-! ### Termwise differentiation -/

/-- ∂/∂u, termwise: u⁻¹ times u·∂/∂u. It is linear and satisfies the product rule. -/
noncomputable def du : Derivation ℚ S S :=
  Derivation.mk'
    { toFun := fun f => mo (-1) 0 * thU f
      map_add' := fun f g => by rw [thU_add, mul_add]
      map_smul' := fun r f => by rw [thU_smul, mul_smul_comm, RingHom.id_apply] }
    fun a b => by
      change mo (-1) 0 * thU (a * b) = a • (mo (-1) 0 * thU b) + b • (mo (-1) 0 * thU a)
      rw [thU_mul, smul_eq_mul, smul_eq_mul]
      ring

/-- ∂/∂v, termwise: v⁻¹ times v·∂/∂v. It is linear and satisfies the product rule. -/
noncomputable def dv : Derivation ℚ S S :=
  Derivation.mk'
    { toFun := fun f => mo 0 (-1) * thV f
      map_add' := fun f g => by rw [thV_add, mul_add]
      map_smul' := fun r f => by rw [thV_smul, mul_smul_comm, RingHom.id_apply] }
    fun a b => by
      change mo 0 (-1) * thV (a * b) = a • (mo 0 (-1) * thV b) + b • (mo 0 (-1) * thV a)
      rw [thV_mul, smul_eq_mul, smul_eq_mul]
      ring

/-- ∂/∂u is termwise: the term c·u^{x+1}·v^y becomes (x+1)·c·u^x·v^y. -/
theorem cf_du (f : S) (x y : ℤ) : cf (du f) x y = ((x : ℚ) + 1) * cf f (x + 1) y := by
  change cf (mo (-1) 0 * thU f) x y = _
  rw [cf_mo_mul, cf_thU, sub_neg_eq_add, sub_zero]
  push_cast
  rfl

/-- ∂/∂v is termwise: the term c·u^x·v^{y+1} becomes (y+1)·c·u^x·v^y. -/
theorem cf_dv (f : S) (x y : ℤ) : cf (dv f) x y = ((y : ℚ) + 1) * cf f x (y + 1) := by
  change cf (mo 0 (-1) * thV f) x y = _
  rw [cf_mo_mul, cf_thV, sub_neg_eq_add, sub_zero]
  push_cast
  rfl

theorem du_mo (a b : ℤ) : du (mo a b) = (a : ℚ) • mo (a - 1) b := by
  refine ext_cf fun x y => ?_
  rw [cf_du, cf_smul, cf_mo, cf_mo]
  by_cases h : x = a - 1 ∧ y = b
  · rw [if_pos h, if_pos ⟨by omega, h.2⟩, h.1]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨by omega, g.2⟩), mul_zero, mul_zero]

theorem dv_mo (a b : ℤ) : dv (mo a b) = (b : ℚ) • mo a (b - 1) := by
  refine ext_cf fun x y => ?_
  rw [cf_dv, cf_smul, cf_mo, cf_mo]
  by_cases h : x = a ∧ y = b - 1
  · rw [if_pos h, if_pos ⟨h.1, by omega⟩, h.2]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨g.1, by omega⟩), mul_zero, mul_zero]

theorem du_sub : du (mo 1 0 - mo 0 1) = 1 := by
  rw [map_sub, du_mo, du_mo, sub_self, mo_zero]
  simp

theorem dv_sub : dv (mo 1 0 - mo 0 1) = -1 := by
  rw [map_sub, dv_mo, dv_mo, sub_self, mo_zero]
  simp

theorem eps_mul_sub : eps * (mo 1 0 - mo 0 1) = 1 := by rw [mul_comm, sub_mul_eps]

/-- Differentiating (u − v)·ε = 1 with respect to u. -/
theorem du_eps : du eps = -eps ^ 2 := by
  rw [du.leibniz_of_mul_eq_one eps_mul_sub, du_sub, smul_eq_mul, mul_one]

/-- Differentiating (u − v)·ε = 1 with respect to v. -/
theorem dv_eps : dv eps = eps ^ 2 := by
  rw [dv.leibniz_of_mul_eq_one eps_mul_sub, dv_sub, smul_eq_mul]
  ring

/-! ### The two readings -/

/-- ∂_{ω₁} on 𝓛₊. -/
noncomputable def d1P : Derivation ℚ Lp Lp := du

/-- ∂_{ω₂} on 𝓛₊. -/
noncomputable def d2P : Derivation ℚ Lp Lp := dv

/-- ∂_{ω₁} on 𝓛₋. -/
noncomputable def d1M : Derivation ℚ Lm Lm := dv

/-- ∂_{ω₂} on 𝓛₋. -/
noncomputable def d2M : Derivation ℚ Lm Lm := du

/-- "Differentiating (ω₁ − ω₂)·ε₊ = 1 gives ∂_{ω₁}ε₊ = −ε₊²". -/
theorem d1P_epsP : d1P epsP = -epsP ^ 2 := du_eps

/-- "… and ∂_{ω₂}ε₊ = ε₊²". -/
theorem d2P_epsP : d2P epsP = epsP ^ 2 := dv_eps

/-- "Differentiating (ω₁ − ω₂)·ε₋ = 1 gives ∂_{ω₁}ε₋ = −ε₋²". -/
theorem d1M_epsM : d1M epsM = -epsM ^ 2 := by
  rw [epsM, d1M, map_neg, dv_eps]
  ring

/-- "… and ∂_{ω₂}ε₋ = ε₋²". -/
theorem d2M_epsM : d2M epsM = epsM ^ 2 := by
  rw [epsM, d2M, map_neg, du_eps]
  ring

/-! ### Display (49), in any ring with two derivations and an element ε with D₁ε = −ε² and D₂ε = ε² -/

section Abstract
variable {A : Type} [CommRing A] [Algebra ℚ A]

theorem iter_smul (D : Derivation ℚ A A) (a : ℕ) (r : ℚ) (z : A) : D^[a] (r • z) = r • D^[a] z := by
  induction a generalizing z with
  | zero => rfl
  | succ a ih => rw [Function.iterate_succ_apply, D.map_smul, ih, Function.iterate_succ_apply]

/-- If Dε = s·ε², then D(ε^m) = s·m·ε^{m+1}. -/
theorem deriv_pow (D : Derivation ℚ A A) {ε : A} {s : ℚ} (h : D ε = s • ε ^ 2) (m : ℕ) : D (ε ^ m) = (s * m) • ε ^ (m + 1) := by
  rcases m with _ | m
  · simp
  · rw [D.leibniz_pow, h, Nat.add_sub_cancel, smul_eq_mul, mul_smul_comm, ← pow_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_comm s]

/-- m!·D₂^b(ε^{m+1}) = (m+b)!·ε^{m+1+b}. -/
theorem iter_pos (D : Derivation ℚ A A) {ε : A} (h : D ε = ε ^ 2) (b m : ℕ) :
    (m.factorial : ℚ) • D^[b] (ε ^ (m + 1)) = ((m + b).factorial : ℚ) • ε ^ (m + 1 + b) := by
  induction b generalizing m with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ_apply, deriv_pow D (s := 1) (by rw [one_smul, h]), iter_smul, smul_smul, one_mul]
    have e : (m.factorial : ℚ) * ((m + 1 : ℕ) : ℚ) = ((m + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [e, ih (m + 1), show m + 1 + b = m + (b + 1) by omega, show m + 1 + 1 + b = m + 1 + (b + 1) by omega]

/-- D₁^a(ε^m) = a!·C(−m, a)·ε^{m+a}. -/
theorem iter_neg (D : Derivation ℚ A A) {ε : A} (h : D ε = -ε ^ 2) (a m : ℕ) :
    D^[a] (ε ^ m) = ((a.factorial : ℚ) * (Ring.choose (-(m : ℤ)) a : ℤ)) • ε ^ (m + a) := by
  induction a generalizing m with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, deriv_pow D (s := -1) (by rw [neg_one_smul, h]), iter_smul, ih (m + 1), smul_smul,
      show m + 1 + a = m + (a + 1) by omega]
    congr 1
    have e := congrArg (Int.cast : ℤ → ℚ) (ClauseBound.Boson.Scalars.succ_mul_choose (-(m : ℤ)) a)
    push_cast at e
    rw [Nat.factorial_succ]
    push_cast
    rw [show (-((m : ℤ) + 1)) = -(m : ℤ) - 1 by ring]
    linear_combination (a.factorial : ℚ) * (-e)

/-- Display (49) with Γ_{j,n} = n·C(−n−1, j−1). -/
theorem displayGamma (D₁ D₂ : Derivation ℚ A A) {ε : A} (h₁ : D₁ ε = -ε ^ 2) (h₂ : D₂ ε = ε ^ 2) {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • D₁^[j - 1] (D₂^[n - 1] (ε ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • ε ^ (j + n) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have e := iter_pos D₂ h₂ b 1
  rw [Nat.factorial_one, Nat.cast_one, one_smul] at e
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, e, iter_smul, iter_neg D₁ h₁, smul_smul, smul_smul,
    show 1 + 1 + b + a = a + 1 + (b + 1) by omega]
  congr 1
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  rw [ClauseBound.Boson.Gam, Nat.add_sub_cancel, show 1 + b = b + 1 by omega, Nat.factorial_succ]
  push_cast
  rw [show (-(2 + (b : ℤ))) = -((b : ℤ) + 1) - 1 by ring]
  field_simp

end Abstract

/-- Display (49) for ε₊: (1/((j−1)!(n−1)!))·∂_{ω₁}^{j−1}∂_{ω₂}^{n−1}ε₊² = Γ_{j,n}·ε₊^{j+n}. -/
theorem displayGamma_P {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1P^[j - 1] (d2P^[n - 1] (epsP ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • epsP ^ (j + n) :=
  displayGamma d1P d2P d1P_epsP d2P_epsP hj hn

/-- Display (49) for ε₋, with the same number Γ_{j,n}. -/
theorem displayGamma_M {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1M^[j - 1] (d2M^[n - 1] (epsM ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • epsM ^ (j + n) :=
  displayGamma d1M d2M d1M_epsM d2M_epsM hj hn

/-! ### The series Σ_{k ≥ 1} c_k·u^{−k−p}·v^{k−q}, differentiated term by term -/

/-- Σ_{k ≥ 1} c_k·u^{−k−p}·v^{k−q}. -/
noncomputable def ser (p q : ℕ) (c : ℤ → ℚ) : S := diag (-((p : ℤ) + q)) (fun y => c (y + q)) (1 - q)

theorem cf_ser (p q : ℕ) (c : ℤ → ℚ) (x y : ℤ) : cf (ser p q c) x y = if 1 ≤ y + q ∧ x + y = -((p : ℤ) + q) then c (y + q) else 0 := by
  rw [ser, cf_diag]
  exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩) rfl rfl

theorem ser_congr (p q : ℕ) {c c' : ℤ → ℚ} (h : ∀ k, c k = c' k) : ser p q c = ser p q c' := by
  rw [funext h]

theorem smul_ser (r : ℚ) (p q : ℕ) (c : ℤ → ℚ) : r • ser p q c = ser p q fun k => r * c k := by
  refine ext_cf fun x y => ?_
  rw [cf_smul, cf_ser, cf_ser]
  split_ifs
  · rfl
  · rw [mul_zero]

/-- ∂/∂u of the term u^{−k−p}·v^{k−q} is (−k−p)·u^{−k−p−1}·v^{k−q}. -/
theorem du_ser (p q : ℕ) (c : ℤ → ℚ) : du (ser p q c) = ser (p + 1) q fun k => (-(k : ℚ) - p) * c k := by
  refine ext_cf fun x y => ?_
  rw [cf_du, cf_ser, cf_ser]
  by_cases h : 1 ≤ y + q ∧ x + y = -(((p + 1 : ℕ) : ℤ) + q)
  · have h2 := h.2
    push_cast at h2
    rw [if_pos h, if_pos ⟨h.1, by omega⟩]
    have e : (x : ℚ) = -((p : ℚ) + 1 + q) - y := by
      have : x = -((p : ℤ) + 1 + q) - y := by omega
      exact_mod_cast this
    rw [e]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨g.1, by have := g.2; push_cast; omega⟩), mul_zero]

/-- ∂/∂v of the term u^{−k−p}·v^{k−q} is (k−q)·u^{−k−p}·v^{k−q−1}. -/
theorem dv_ser (p q : ℕ) (c : ℤ → ℚ) : dv (ser p q c) = ser p (q + 1) fun k => ((k : ℚ) - q) * c k := by
  refine ext_cf fun x y => ?_
  rw [cf_dv, cf_ser, cf_ser]
  have e : y + 1 + (q : ℤ) = y + ((q + 1 : ℕ) : ℤ) := by push_cast; ring
  by_cases h : 1 ≤ y + ((q + 1 : ℕ) : ℤ) ∧ x + y = -((p : ℤ) + ((q + 1 : ℕ) : ℤ))
  · have h2 := h.2
    push_cast at h2
    rw [if_pos h, if_pos ⟨by rw [e]; exact h.1, by omega⟩, e]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨by rw [← e]; exact g.1, by have := g.2; push_cast; omega⟩), mul_zero]

/-- ∂^a/∂u^a of the term u^{−k−p}·v^{k−q} is a!·C(−k−p, a)·u^{−k−p−a}·v^{k−q}. -/
theorem du_iter_ser (a p q : ℕ) (c : ℤ → ℚ) :
    du^[a] (ser p q c) = ser (p + a) q fun k => (a.factorial : ℚ) * (Ring.choose (-k - (p : ℤ)) a : ℤ) * c k := by
  induction a generalizing p c with
  | zero => exact ser_congr _ _ fun k => by simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, du_ser, ih, show p + 1 + a = p + (a + 1) by omega]
    refine ser_congr _ _ fun k => ?_
    have e := congrArg (Int.cast : ℤ → ℚ) (ClauseBound.Boson.Scalars.succ_mul_choose (-k - (p : ℤ)) a)
    push_cast at e
    rw [Nat.factorial_succ, show -k - ((p + 1 : ℕ) : ℤ) = -k - (p : ℤ) - 1 by push_cast; ring]
    push_cast
    linear_combination (-(a.factorial : ℚ) * c k) * e

/-- ∂^b/∂v^b of the term u^{−k−p}·v^{k−q} is b!·C(k−q, b)·u^{−k−p}·v^{k−q−b}. -/
theorem dv_iter_ser (b p q : ℕ) (c : ℤ → ℚ) :
    dv^[b] (ser p q c) = ser p (q + b) fun k => (b.factorial : ℚ) * (Ring.choose (k - (q : ℤ)) b : ℤ) * c k := by
  induction b generalizing q c with
  | zero => exact ser_congr _ _ fun k => by simp
  | succ b ih =>
    rw [Function.iterate_succ_apply, dv_ser, ih, show q + 1 + b = q + (b + 1) by omega]
    refine ser_congr _ _ fun k => ?_
    have e := congrArg (Int.cast : ℤ → ℚ) (ClauseBound.Boson.Scalars.succ_mul_choose (k - (q : ℤ)) b)
    push_cast at e
    rw [Nat.factorial_succ, show k - ((q + 1 : ℕ) : ℤ) = k - (q : ℤ) - 1 by push_cast; ring]
    push_cast
    linear_combination (-(b.factorial : ℚ) * c k) * e

/-- ∂ε/∂v = Σ_{k ≥ 1} k·u^{−k−1}·v^{k−1}. -/
theorem dv_eps_eq : dv eps = ser 1 1 fun k => (k : ℚ) := by
  refine ext_cf fun x y => ?_
  rw [cf_dv, eps, cf_diag, cf_ser]
  by_cases h : 1 ≤ y + ((1 : ℕ) : ℤ) ∧ x + y = -(((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ))
  · have h1 := h.1
    have h2 := h.2
    push_cast at h1 h2
    rw [if_pos h, if_pos ⟨by omega, by omega⟩]
    push_cast
    ring
  · rw [if_neg h]
    by_cases h' : 0 ≤ y + 1 ∧ x + (y + 1) = -1
    · have hy : y = -1 := by
        by_contra hne
        exact h ⟨by push_cast; omega, by push_cast; omega⟩
      rw [hy]
      norm_num
    · rw [if_neg h', mul_zero]

/-- Σ_{k ≥ 1} c_k·ω₁^{−k−j}·ω₂^{k−n} in 𝓛₊. -/
noncomputable def sumP (j n : ℕ) (c : ℤ → ℚ) : Lp := ser j n c

/-- Σ_{k ≥ 1} c_k·ω₁^{k−j}·ω₂^{−k−n} in 𝓛₋. -/
noncomputable def sumM (j n : ℕ) (c : ℤ → ℚ) : Lm := ser n j c

/-- In Σ_{k ≥ 1} c_k·ω₁^{−k−j}·ω₂^{k−n} the coefficient of ω₁^{−k−j}·ω₂^{k−n}, k ≥ 1, is c_k; all
other coefficients vanish. -/
theorem cfP_sumP (j n : ℕ) (c : ℤ → ℚ) (x y : ℤ) : cfP (sumP j n c) x y = if 1 ≤ y + n ∧ x + y = -((j : ℤ) + n) then c (y + n) else 0 := cf_ser j n c x y

/-- "ε₊² = ∂_{ω₂}ε₊ = Σ_k k·ω₁^{−k−1}·ω₂^{k−1}". -/
theorem epsP_sq : epsP ^ 2 = d2P epsP ∧ d2P epsP = sumP 1 1 fun k => (k : ℚ) := ⟨d2P_epsP.symm, dv_eps_eq⟩

/-- "ε₋² = −∂_{ω₁}ε₋ = Σ_k k·ω₂^{−k−1}·ω₁^{k−1}". -/
theorem epsM_sq : epsM ^ 2 = -d1M epsM ∧ -d1M epsM = sumM 1 1 fun k => (k : ℚ) :=
  ⟨by rw [d1M_epsM, neg_neg], by rw [epsM, d1M, map_neg, neg_neg]; exact dv_eps_eq⟩

/-- "The sum over k is the left side of (49)", in 𝓛₊: differentiating Σ_k k·ω₁^{−k−1}·ω₂^{k−1} term
by term. -/
theorem leftGamma_P {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1P^[j - 1] (d2P^[n - 1] (epsP ^ 2)) =
      sumP j n fun k => (k : ℚ) * (Ring.choose (-k - 1) (j - 1) : ℤ) * (Ring.choose (k - 1) (n - 1) : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  rw [epsP_sq.1, epsP_sq.2, Nat.add_sub_cancel, Nat.add_sub_cancel, sumP, sumP, d1P, d2P, dv_iter_ser, du_iter_ser, smul_ser,
    Nat.add_comm 1 a, Nat.add_comm 1 b]
  refine ser_congr _ _ fun k => ?_
  push_cast
  field_simp

/-- The same in 𝓛₋: differentiating Σ_k k·ω₂^{−k−1}·ω₁^{k−1} term by term. -/
theorem leftGamma_M {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1M^[j - 1] (d2M^[n - 1] (epsM ^ 2)) =
      sumM j n fun k => (k : ℚ) * (Ring.choose (k - 1) (j - 1) : ℤ) * (Ring.choose (-k - 1) (n - 1) : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  rw [epsM_sq.1, epsM_sq.2, Nat.add_sub_cancel, Nat.add_sub_cancel, sumM, sumM, d1M, d2M, du_iter_ser, dv_iter_ser, smul_ser,
    Nat.add_comm 1 a, Nat.add_comm 1 b]
  refine ser_congr _ _ fun k => ?_
  push_cast
  field_simp

/-- The sum in the display for κ: Σ_{k ≥ 1} k·C(−k−1, j−1)·C(k−1, n−1)·ω₁^{−k−j}·ω₂^{k−n} =
Γ_{j,n}·ε₊^{j+n}, "because the sum over k is the left side of (49)". -/
theorem kappa_sum {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (sumP j n fun k => (k : ℚ) * (Ring.choose (-k - 1) (j - 1) : ℤ) * (Ring.choose (k - 1) (n - 1) : ℤ)) = (ClauseBound.Boson.Gam j n : ℚ) • epsP ^ (j + n) := by
  rw [← leftGamma_P hj hn, displayGamma_P hj hn]

/-- The sum for κ', "in the same way": Σ_{k ≥ 1} k·C(k−1, j−1)·C(−k−1, n−1)·ω₁^{k−j}·ω₂^{−k−n} =
Γ_{j,n}·ε₋^{j+n}. -/
theorem kappa'_sum {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (sumM j n fun k => (k : ℚ) * (Ring.choose (k - 1) (j - 1) : ℤ) * (Ring.choose (-k - 1) (n - 1) : ℤ)) = (ClauseBound.Boson.Gam j n : ℚ) • epsM ^ (j + n) := by
  rw [← leftGamma_M hj hn, displayGamma_M hj hn]

end GeneralPieces.Series
