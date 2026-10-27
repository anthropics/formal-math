/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Defs
public import GeneralPieces.GenF.Hahn
public import GeneralPieces.GenF.Coeff

/-! # The lemma on the operators Q_s, paragraph "Generating functions": e^{A⁻} and the products of four exponentials
Here u and v stand for the paper's ω₁ and ω₂ in the first reading, and for ω₂ and ω₁ in the second.
The inner variables are the x_n of A and the outer variables the x'_n of B (in the second reading,
those of B and of A).
A⁻ = Σ_n x_n·J_n^-(u) acts on `W`: J_n^-(u) is applied to the coefficient of every power of v and of
every monomial in the x_n, x'_n. Its exponential `Phi` is Σ_m (A⁻)^m/m!, a finite sum in the
coefficient
of every monomial in the x_n, x'_n. e^{B⁺} and e^{A⁺} are the multiplications by the exponentials of
B⁺ and of the part of A⁺ with l ≤ E, and e^{B⁻}·t^σ' is `ket`.
`plusSide` is ⟨e^{A⁺}·e^{A⁻}·e^{B⁺}·e^{B⁻}⟩ and `normal` is ⟨𝒩⟩ = ⟨e^{A⁺}·e^{B⁺}·e^{A⁻}·e^{B⁻}⟩, for
the monomials t^σ (coefficient taken) and t^σ' (argument), as power series in the x_n, x'_n over
`S`.
The reading is chosen by `rd`: `rd = false` is the first reading, the paper's order (in 𝓛₊);
`rd = true` is the second, in which the names A and B are exchanged (in 𝓛₋).
These are defined for every E; they are the paper's entries when |σ| ≤ E, because A⁺ is cut at l ≤ E
and e^{A⁺} stands leftmost, and then they do not depend on E. Definitions only. -/

@[expose] public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson

/-- J_n^-(u), applied to the coefficient of every power of v. -/
noncomputable def JmT (n : ℕ) : Derivation ℚ Tv Tv := hder ((JmU n).restrictScalars ℚ)

/-- The operator that stands beside each variable in A⁻: J_n^-(u) beside the inner variable with
index n, and 0 beside the outer variables. -/
noncomputable def DD (rd : Bool) : X → Derivation ℚ Tv Tv := sel rd JmT 0

/-- e^{A⁻}. -/
noncomputable def Phi (rd : Bool) : W →+* W := expD (X := X) (A := Tv) (DD rd)

/-- ⟨e^{A⁺}·e^{A⁻}·e^{B⁺}·e^{B⁻}⟩. -/
noncomputable def plusSide (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) : PS := braW σ (expW (Ap rd E) * Phi rd (expW (Bp rd) * ket rd σ'))

/-- ⟨𝒩⟩ = ⟨e^{A⁺}·e^{B⁺}·e^{A⁻}·e^{B⁻}⟩. -/
noncomputable def normal (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) : PS := braW σ (expW (Ap rd E) * (expW (Bp rd) * Phi rd (ket rd σ')))

/-- The exponent of the monomial ∏_{n ∈ a} x_{ι n}, for a list a of parts. -/
noncomputable def aL (ι : ℕ → X) (a : List ℕ) : X →₀ ℕ := (a.map fun n => Finsupp.single (ι n) 1).sum

/-- One half of the display in the proof of Lemma 9 that writes both orders of the products through
𝒩, as an equation between the entries ⟨t^σ| · t^σ'⟩: ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩ = e^κ·⟨𝒩⟩, in 𝓛₊ in
the first reading
and in 𝓛₋ in the second (there A and B are exchanged and κ is κ'). It holds wherever A⁺ is cut. -/
def StTwoOrders : Prop := ∀ (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ), plusSide rd E σ σ' = expW (kap rd) * normal rd E σ σ'

/-- For |σ| ≤ E, the coefficient of every monomial in the x_n, x'_n in ⟨𝒩⟩ lies in 𝓛, and it is the
same element of 𝓛 in both readings. -/
def StN1 : Prop := ∀ (E : ℕ) (σ σ' : Multiset ℕ) (γ : X →₀ ℕ), σ.sum ≤ E →
  ∃ n : L, MvPowerSeries.coeff γ (normal false E σ σ') = toP n ∧ MvPowerSeries.coeff γ (normal true E σ σ') = toM n

/-- n_{∅,∅} = [σ = σ']. -/
def StN2 : Prop := ∀ (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ), MvPowerSeries.constantCoeff (normal rd E σ σ') = if σ = σ' then 1 else 0

/-- For σ = σ' = ∅ (the paper's case E = 0) we have ⟨𝒩⟩ = 1, wherever A⁺ is cut. -/
def StN3 : Prop := ∀ (rd : Bool) (E : ℕ), normal rd E 0 0 = 1

/-- μ!·ν! times the coefficient of x^μ·x'^ν in ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩ is ⟨Y(a,u)·Y(b,v)⟩ = Σ_r
⟨a[r]∘b[−r]⟩·u^{r−h'}·v^{−r−h}; a lists the parts of the inner, b of the outer family,
and σ, σ' have the same weight, as in the paper; all parts are positive, σ and σ' have no part 0 (t₀
is not used), and |σ| ≤ E. -/
def StY : Prop := ∀ (rd : Bool) (E : ℕ) (a b : List ℕ) (σ σ' : Multiset ℕ), Pos a → Pos b → 0 ∉ σ → 0 ∉ σ' → σ.sum = σ'.sum → σ.sum ≤ E →
  fac (aL (xi rd) a + aL (xo rd) b) • MvPowerSeries.coeff (aL (xi rd) a + aL (xo rd) b) (plusSide rd E σ σ') = fP a b σ σ'

end GeneralPieces.GenF
