/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-! # The lemma on the operators Q_s, paragraph "Series": the rings 𝓛, 𝓛₊, 𝓛₋ and the two inverses of ω₁ − ω₂

𝓛 = ℚ[ω₁, ω₁⁻¹, ω₂, ω₂⁻¹] is the additive monoid algebra of ℤ × ℤ over ℚ, so that the coefficient of
ω₁^x·ω₂^y is `F.coeff (x, y)`. 𝓛₊, the ring of the series
Σ_{j ≥ j₀} q_j(ω₁)·ω₂^j with Laurent polynomials q_j, is Mathlib's ring of Laurent series over the
Laurent polynomials. 𝓛₋ is the same Lean type, read with ω₁ and ω₂ exchanged:
the outer variable is ω₁ there. So everything is proved once, for a ring `S` with an inner variable
u and an outer variable v, and then read twice.
Here: both rings contain 𝓛 (`toP`, `toM`, with the same coefficients: `cfP_toP`, `cfM_toM`; `toP` is
injective), ω₁ − ω₂ has the inverse ε₊ in 𝓛₊ and ε₋ in 𝓛₋, and the coefficients of the powers of ε₊
(`eps_pow_succ`). -/

@[expose] public section

namespace GeneralPieces.Series

open LaurentPolynomial

/-- 𝓛 = ℚ[ω₁, ω₁⁻¹, ω₂, ω₂⁻¹]. -/
abbrev L : Type := AddMonoidAlgebra ℚ (ℤ × ℤ)

/-- The series Σ_{j ≥ j₀} q_j(u)·v^j with Laurent polynomials q_j over ℚ. -/
abbrev S : Type := HahnSeries ℤ (LaurentPolynomial ℚ)

/-- 𝓛₊: the ring `S` with u = ω₁ and v = ω₂. -/
abbrev Lp : Type := S

/-- 𝓛₋: the ring `S` with u = ω₂ and v = ω₁. -/
abbrev Lm : Type := S

/-- The monomial u^x·v^y. -/
noncomputable def mo (x y : ℤ) : S := HahnSeries.single y (T x)

/-- The coefficient of u^x·v^y. -/
noncomputable def cf (f : S) (x y : ℤ) : ℚ := (f.coeff y).coeff x

theorem ext_cf {f g : S} (h : ∀ x y, cf f x y = cf g x y) : f = g := by
  ext y x
  exact h x y

@[simp] theorem cf_zero (x y : ℤ) : cf 0 x y = 0 := rfl

@[simp] theorem cf_add (f g : S) (x y : ℤ) : cf (f + g) x y = cf f x y + cf g x y := rfl

@[simp] theorem cf_neg (f : S) (x y : ℤ) : cf (-f) x y = -cf f x y := rfl

@[simp] theorem cf_sub (f g : S) (x y : ℤ) : cf (f - g) x y = cf f x y - cf g x y := rfl

@[simp] theorem cf_smul (r : ℚ) (f : S) (x y : ℤ) : cf (r • f) x y = r * cf f x y := rfl

theorem cf_mo (a b x y : ℤ) : cf (mo a b) x y = if x = a ∧ y = b then 1 else 0 := by
  unfold cf mo
  by_cases hy : y = b
  · subst hy
    simp [eq_comm]
  · rw [HahnSeries.coeff_single_of_ne hy]
    simp [hy]

theorem mo_zero : mo 0 0 = 1 := rfl

theorem mo_mul_mo (a b c d : ℤ) : mo a b * mo c d = mo (a + c) (b + d) := by
  unfold mo
  rw [HahnSeries.single_mul_single, T_add]

/-- Multiplication by a monomial shifts the coefficients. -/
theorem cf_mo_mul (a b : ℤ) (f : S) (x y : ℤ) : cf (mo a b * f) x y = cf f (x - a) (y - b) := by
  unfold cf mo
  rw [HahnSeries.coeff_single_mul, T, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (x - a) (fun m _ => by constructor <;> intro h <;> omega), one_mul]

/-- The coefficients of a finite sum. -/
theorem cf_sum {α : Type} (s : Finset α) (g : α → S) (x y : ℤ) : cf (∑ c ∈ s, g c) x y = ∑ c ∈ s, cf (g c) x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => simp [Finset.sum_insert hc, ih]

theorem diag_bddBelow (d : ℤ) (c : ℤ → ℚ) (j₀ : ℤ) :
    BddBelow (Function.support fun j : ℤ => if j₀ ≤ j then (C (c j) * T (d - j) : LaurentPolynomial ℚ) else 0) :=
  ⟨j₀, fun j hj => by
    by_contra h
    exact hj (if_neg h)⟩

/-- The series Σ_{j ≥ j₀} c_j·u^{d−j}·v^j, all of whose monomials have total degree d. -/
noncomputable def diag (d : ℤ) (c : ℤ → ℚ) (j₀ : ℤ) : S :=
  HahnSeries.ofSuppBddBelow (fun j => if j₀ ≤ j then C (c j) * T (d - j) else 0) (diag_bddBelow d c j₀)

theorem cf_diag (d : ℤ) (c : ℤ → ℚ) (j₀ x y : ℤ) : cf (diag d c j₀) x y = if j₀ ≤ y ∧ x + y = d then c y else 0 := by
  unfold cf diag
  rw [HahnSeries.coeff_ofSuppBddBelow]
  by_cases h : j₀ ≤ y
  · rw [if_pos h, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h2 : x + y = d
    · rw [if_pos (by omega), if_pos ⟨h, h2⟩]
    · rw [if_neg (by omega), if_neg (fun g => h2 g.2)]
  · rw [if_neg h, if_neg (fun g => h g.1)]
    rfl

/-! ### Both rings contain 𝓛 -/

/-- The monomials of `S` as a homomorphism of monoids. -/
noncomputable def moHom : Multiplicative (ℤ × ℤ) →* S where
  toFun p := mo p.toAdd.1 p.toAdd.2
  map_one' := mo_zero
  map_mul' _ _ := (mo_mul_mo _ _ _ _).symm

/-- The same with the two exponents exchanged. -/
noncomputable def moHom' : Multiplicative (ℤ × ℤ) →* S where
  toFun p := mo p.toAdd.2 p.toAdd.1
  map_one' := mo_zero
  map_mul' _ _ := (mo_mul_mo _ _ _ _).symm

/-- 𝓛 → 𝓛₊: ω₁ goes to u and ω₂ to v. -/
noncomputable def toP : L →ₐ[ℚ] Lp := AddMonoidAlgebra.lift ℚ S (ℤ × ℤ) moHom

/-- 𝓛 → 𝓛₋: ω₁ goes to v and ω₂ to u. -/
noncomputable def toM : L →ₐ[ℚ] Lm := AddMonoidAlgebra.lift ℚ S (ℤ × ℤ) moHom'

/-- The coefficient of ω₁^x·ω₂^y in an element of 𝓛₊. -/
noncomputable def cfP (f : Lp) (x y : ℤ) : ℚ := cf f x y

/-- The coefficient of ω₁^x·ω₂^y in an element of 𝓛₋. -/
noncomputable def cfM (f : Lm) (x y : ℤ) : ℚ := cf f y x

/-- The monomial ω₁^x·ω₂^y of 𝓛. -/
noncomputable def W (x y : ℤ) : L := AddMonoidAlgebra.single (x, y) 1

theorem toP_single (x y : ℤ) (r : ℚ) : toP (AddMonoidAlgebra.single (x, y) r) = r • mo x y := AddMonoidAlgebra.lift_single _ _ _

theorem toM_single (x y : ℤ) (r : ℚ) : toM (AddMonoidAlgebra.single (x, y) r) = r • mo y x := AddMonoidAlgebra.lift_single _ _ _

theorem toP_W (x y : ℤ) : toP (W x y) = mo x y := by rw [W, toP_single, one_smul]

theorem toM_W (x y : ℤ) : toM (W x y) = mo y x := by rw [W, toM_single, one_smul]

/-- An element of 𝓛 has the same coefficients in 𝓛₊. -/
theorem cfP_toP (F : L) (x y : ℤ) : cfP (toP F) x y = F.coeff (x, y) := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp [cfP]
  | add f g hf hg =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← hf, ← hg]
    rfl
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [toP_single, cfP, cf_smul, cf_mo, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : x = a ∧ y = b
    · rw [if_pos h, if_pos (by rw [h.1, h.2]), mul_one]
    · rw [if_neg h, if_neg (fun g => h ⟨(congrArg Prod.fst g).symm, (congrArg Prod.snd g).symm⟩), mul_zero]

/-- An element of 𝓛 has the same coefficients in 𝓛₋. -/
theorem cfM_toM (F : L) (x y : ℤ) : cfM (toM F) x y = F.coeff (x, y) := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp [cfM]
  | add f g hf hg =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← hf, ← hg]
    rfl
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [toM_single, cfM, cf_smul, cf_mo, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : y = b ∧ x = a
    · rw [if_pos h, if_pos (by rw [h.1, h.2]), mul_one]
    · rw [if_neg h, if_neg (fun g => h ⟨(congrArg Prod.snd g).symm, (congrArg Prod.fst g).symm⟩), mul_zero]

/-- 𝓛₊ contains 𝓛. -/
theorem toP_injective : Function.Injective toP := fun F G h => by
  ext ⟨x, y⟩
  rw [← cfP_toP, ← cfP_toP, h]

/-! ### The two inverses of ω₁ − ω₂ -/

/-- Σ_{j ≥ 0} u^{−j−1}·v^j. -/
noncomputable def eps : S := diag (-1) (fun _ => 1) 0

/-- (u − v)·f, coefficient by coefficient. -/
theorem cf_sub_mul (f : S) (x y : ℤ) : cf ((mo 1 0 - mo 0 1) * f) x y = cf f (x - 1) y - cf f x (y - 1) := by
  rw [sub_mul, cf_sub, cf_mo_mul, cf_mo_mul, sub_zero, sub_zero]

theorem cf_one (x y : ℤ) : cf 1 x y = if x = 0 ∧ y = 0 then 1 else 0 := by rw [← mo_zero, cf_mo]

/-- (u − v)·Σ_{j ≥ 0} u^{−j−1}·v^j = 1. -/
theorem sub_mul_eps : (mo 1 0 - mo 0 1) * eps = 1 := by
  refine ext_cf fun x y => ?_
  rw [cf_sub_mul, eps, cf_diag, cf_diag, cf_one]
  split_ifs <;> first | rfl | omega | norm_num

/-- ω₁ − ω₂. -/
noncomputable def dW : L := W 1 0 - W 0 1

/-- ε₊ = Σ_{j ≥ 0} ω₁^{−j−1}·ω₂^j. -/
noncomputable def epsP : Lp := eps

/-- ε₋ = −Σ_{j ≥ 0} ω₂^{−j−1}·ω₁^j. -/
noncomputable def epsM : Lm := -eps

theorem toP_dW : toP dW = mo 1 0 - mo 0 1 := by rw [dW, map_sub, toP_W, toP_W]

theorem toM_dW : toM dW = -(mo 1 0 - mo 0 1) := by rw [dW, map_sub, toM_W, toM_W, neg_sub]

/-- ε₊ is the inverse of ω₁ − ω₂ in 𝓛₊. -/
theorem dW_mul_epsP : toP dW * epsP = 1 := by rw [toP_dW, epsP, sub_mul_eps]

/-- ε₋ is the inverse of ω₁ − ω₂ in 𝓛₋. -/
theorem dW_mul_epsM : toM dW * epsM = 1 := by
  rw [toM_dW, epsM]
  linear_combination sub_mul_eps

/-- The powers of Σ_{j ≥ 0} u^{−j−1}·v^j: its (N+1)-st power is Σ_{j ≥ 0} C(j+N, N)·u^{−j−N−1}·v^j. -/
theorem eps_pow_succ (N : ℕ) : eps ^ (N + 1) = diag (-(N : ℤ) - 1) (fun j => ((j.toNat + N).choose N : ℚ)) 0 := by
  induction N with
  | zero =>
    rw [zero_add, pow_one, eps]
    refine ext_cf fun x y => ?_
    rw [cf_diag, cf_diag]
    simp
  | succ N ih =>
    have key : (mo 1 0 - mo 0 1) * diag (-((N + 1 : ℕ) : ℤ) - 1) (fun j => ((j.toNat + (N + 1)).choose (N + 1) : ℚ)) 0 = eps ^ (N + 1) := by
      rw [ih]
      refine ext_cf fun x y => ?_
      rw [cf_sub_mul, cf_diag, cf_diag, cf_diag]
      by_cases hd : x + y = -(N : ℤ) - 1
      · rcases lt_trichotomy y 0 with hy | hy | hy
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), sub_zero]
        · subst hy
          rw [if_pos ⟨le_refl _, by push_cast; omega⟩, if_neg (by omega), if_pos ⟨le_refl _, hd⟩]
          simp
        · obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = n + 1 := ⟨(y - 1).toNat, by omega⟩
          rw [if_pos ⟨by omega, by push_cast; omega⟩, if_pos ⟨by omega, by push_cast; omega⟩, if_pos ⟨by omega, hd⟩]
          have e1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
          have e2 : ((n : ℤ) + 1 - 1).toNat = n := by omega
          rw [e1, e2, show n + 1 + (N + 1) = (n + 1 + N) + 1 by ring, Nat.choose_succ_succ, show n + 1 + N = n + (N + 1) by ring]
          push_cast
          ring
      · rw [if_neg (fun g => hd (by have := g.2; push_cast at this; omega)), if_neg (fun g => hd (by have := g.2; push_cast at this; omega)),
          if_neg (fun g => hd g.2), sub_zero]
    calc eps ^ (N + 1 + 1) = eps ^ (N + 1) * eps := pow_succ _ _
      _ = ((mo 1 0 - mo 0 1) * eps) * diag (-((N + 1 : ℕ) : ℤ) - 1) (fun j => ((j.toNat + (N + 1)).choose (N + 1) : ℚ)) 0 := by rw [← key]; ring
      _ = _ := by rw [sub_mul_eps, one_mul]

end GeneralPieces.Series
