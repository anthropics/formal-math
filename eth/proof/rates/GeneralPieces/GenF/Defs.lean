/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.Expansion
public import GeneralPieces.Series.Deriv
public import GeneralPieces.GenF.Taylor
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Data.Finsupp.Multiset

/-! # Lemma 9 (Appendix B), paragraph "Generating functions" of its proof: the rings and the series J, A, B, κ

As for the rings 𝓛₊ and 𝓛₋, everything is set up once, for an inner variable u and an outer variable
v, and read twice. In the first reading (`rd = false`) u = ω₁, v = ω₂, the inner family
is A (variables x_n) and the outer family is B (variables x'_n); in the second (`rd = true`) u = ω₂,
v = ω₁, the inner family is B and the outer family is A.
The paper says what an equation between products of exponentials means: apply both sides to a
polynomial and take the coefficient of a monomial in the t_k and of a monomial in the x_n, x'_n.
Here this is the typing: an element of `W` has, for every monomial in the x_n, x'_n and every power
of v, a polynomial in the t_k over ℚ[u, u⁻¹] as its coefficient.
The parts, the indices k of t_k and the indices n of x_n are natural numbers; x₀ and x'₀ are there
but occur nowhere, and t₀ does not occur in the statements that are used (they ask 0 ∉ σ, 0 ∉ σ').
The series J_n are the paper's for n ≥ 1; at n = 0 their values are not used. Definitions, and the
bound on the support that `JpV` needs. -/

@[expose] public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

/-- ℚ[u, u⁻¹]. -/
abbrev Lu : Type := LaurentPolynomial ℚ

/-- The polynomials in the t_k over ℚ[u, u⁻¹]. -/
abbrev Vu : Type := MvPolynomial ℕ Lu

/-- The series Σ_{j ≥ j₀} p_j·v^j whose coefficients p_j are polynomials in the t_k over ℚ[u, u⁻¹]. -/
abbrev Tv : Type := HahnSeries ℤ Vu

/-- The names of the further variables: x_n is `Sum.inl n` and x'_n is `Sum.inr n`. -/
abbrev X : Type := ℕ ⊕ ℕ

/-- The formal power series in the x_n, x'_n over `Tv`. -/
abbrev W : Type := MvPowerSeries X Tv

/-- The formal power series in the x_n, x'_n over the ring `S` of series in u and v: here the matrix
entries live. -/
abbrev PS : Type := MvPowerSeries X S

/-- `S` is contained in `Tv`: the constant polynomials. -/
noncomputable def emb : S →+* Tv where
  toFun f := f.map (MvPolynomial.C : Lu →+* Vu)
  map_one' := HahnSeries.map_one (MvPolynomial.C : Lu →+* Vu).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (MvPolynomial.C : Lu →+* Vu).toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero (MvPolynomial.C : Lu →+* Vu).toZeroHom
  map_add' _ _ := HahnSeries.map_add (MvPolynomial.C : Lu →+* Vu).toAddMonoidHom

/-- `PS` is contained in `W`. -/
noncomputable def embW : PS →+* W := MvPowerSeries.map emb

/-- t_k as an element of `Tv`. -/
noncomputable def tT (k : ℕ) : Tv := HahnSeries.C (MvPolynomial.X k)

/-- The coefficient of the monomial t^σ, taken in the coefficient of every power of v. -/
noncomputable def bra (σ : Multiset ℕ) (f : Tv) : S := f.map (MvPolynomial.coeffAddMonoidHom (Multiset.toFinsupp σ) : Vu →+ Lu)

/-- The same, taken in the coefficient of every monomial in the x_n, x'_n. This is ⟨·⟩ before the
operator is applied to t^σ'. -/
noncomputable def braW (σ : Multiset ℕ) (w : W) : PS := fun α => bra σ (MvPowerSeries.coeff α w)

/-- The variable of the inner family with index n. -/
def xi (rd : Bool) (n : ℕ) : X := if rd then Sum.inr n else Sum.inl n

/-- The variable of the outer family with index n. -/
def xo (rd : Bool) (n : ℕ) : X := if rd then Sum.inl n else Sum.inr n

/-- f, made 0 at the index 0. -/
def z0 {R : Type} [Zero R] (f : ℕ → R) : ℕ → R := fun n => if n = 0 then 0 else f n

/-- The function on the variables that is f on the inner and g on the outer family, and 0 on x₀ and
x'₀: these two variables occur nowhere. -/
def sel {R : Type} [Zero R] (rd : Bool) (f g : ℕ → R) : X → R := if rd then Sum.elim (z0 g) (z0 f) else Sum.elim (z0 f) (z0 g)

/-- The bilinear form Σ_{i,i'} q_{i,i'}·x_i·x_{i'}; used only when q_{i,i'} = 0 unless x_i is of the
inner and x_{i'} of the outer family. -/
noncomputable def bil {R : Type} [Semiring R] (q : X → X → R) : MvPowerSeries X R :=
  fun α => if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, q i i' else 0

theorem JpV_bddBelow (n : ℕ) :
    BddBelow (Function.support fun y : ℤ => if 0 ≤ y then (MvPolynomial.C (C (bet n (y + n) : ℚ)) * MvPolynomial.X (y + n).toNat : Vu) else 0) :=
  ⟨0, fun y hy => by
    by_contra h
    exact hy (if_neg h)⟩

/-- J_n^+(v) = Σ_{l ≥ 1} C(l−1, n−1)·t_l·v^{l−n}, an element of `Tv`; the operator is the
multiplication by it. For n ≥ 1 the terms with l < n vanish. -/
noncomputable def JpV (n : ℕ) : Tv :=
  HahnSeries.ofSuppBddBelow (fun y : ℤ => if 0 ≤ y then MvPolynomial.C (C (bet n (y + n) : ℚ)) * MvPolynomial.X (y + n).toNat else 0) (JpV_bddBelow n)

/-- The part of J_n^+(u) with l ≤ E: Σ_{1 ≤ l ≤ E} C(l−1, n−1)·t_l·u^{l−n}. The other terms do not
contribute to the coefficient of a monomial of weight at most E. -/
noncomputable def JpU (E n : ℕ) : Vu := ∑ l ∈ Finset.Icc 1 E, MvPolynomial.C (C (bet n l : ℚ) * T (l - n)) * MvPolynomial.X l

/-- J_n^-(u) = Σ_{k ≥ 1} C(−k−1, n−1)·u^{−k−n}·∇_k, with ∇_k = k·∂/∂t_k: the derivation of the
polynomials in the t_k with t_k ↦ k·C(−k−1, n−1)·u^{−k−n}. -/
noncomputable def JmU (n : ℕ) : Derivation Lu Vu Vu :=
  MvPolynomial.mkDerivation Lu fun k => MvPolynomial.C (C ((k : ℚ) * (bet n (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - n))

/-- Σ_n x'_n·C(−k−1, n−1)·v^{−k−n}, the coefficient of ∇_k in B⁻ (outer family). -/
noncomputable def sfB' (rd : Bool) (k : ℕ) : PS := lin (sel rd 0 (fun n => (bet n (-(k : ℤ)) : ℚ) • mo 0 (-(k : ℤ) - n)))

/-- B⁺ = Σ_n x'_n·J_n^+(v). -/
noncomputable def Bp (rd : Bool) : W := lin (sel rd 0 JpV)

/-- The part of A⁺ = Σ_n x_n·J_n^+(u) with l ≤ E. -/
noncomputable def Ap (rd : Bool) (E : ℕ) : W := lin (sel rd (fun n => HahnSeries.C (JpU E n)) 0)

/-- e^{B⁻}·t^σ', defined as the product of the t_k + k·(the coefficient of ∇_k in B⁻) over the parts
k of σ'. By Taylor's formula this is the series Σ_m (B⁻)^m/m! applied to t^σ'.
e^{B⁻} is always applied first, to a monomial. -/
noncomputable def ket (rd : Bool) (σ' : Multiset ℕ) : W := (σ'.map fun k => MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)).prod

/-- The sum over k in the display for κ, for the index p of the inner and q of the outer family:
Σ_{k ≥ 1} k·C(−k−1, p−1)·C(k−1, q−1)·u^{−k−p}·v^{k−q}. -/
noncomputable def kapS (p q : ℕ) : S := sumP p q fun k => (k : ℚ) * (Ring.choose (-k - 1) (p - 1) : ℤ) * (Ring.choose (k - 1) (q - 1) : ℤ)

/-- κ = Σ_{p,q} x_p·x'_q·(the sum over k). By the display for κ in the paper, this is Σ_k k·𝖠_k·𝖡_k,
with the 𝖠_k and 𝖡_k of the paper. -/
noncomputable def kap (rd : Bool) : PS := bil fun i i' => sel rd (fun p => sel rd 0 (fun q => kapS p q) i') 0 i

end GeneralPieces.GenF
