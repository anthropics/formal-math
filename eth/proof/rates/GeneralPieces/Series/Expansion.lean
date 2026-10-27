/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.Rings
public import ClauseBound.Boson.Defs

/-! # The lemma on the operators Q_s: the series f₊ and f₋, and what the comparison of coefficients in the two orders gives

Here a and b are lists of positive integers, the parts of μ and ν, so h' = a.sum, h = b.sum and H =
h' + h. The monomials t^σ, t^σ' of the paper are the multisets π, σ here, and
⟨X⟩ is the entry (π, σ) of the matrix of X. E is the weight of σ; it is not asked that π has the
same weight (if not, all entries below vanish).
`fP` and `fM` are f₊ ∈ 𝓛₊ and f₋ ∈ 𝓛₋ in the form of the paragraph "Reading off" of the proof of
Lemma 9. The structure `Expansion` says what the paragraph "One Laurent polynomial" gets by
comparing the
coefficients of x^μ·x'^ν in the display of that proof that writes both orders with 𝒩 =
e^{A⁺}e^{B⁺}e^{A⁻}e^{B⁻}: f₊ and f₋ are the same combination of powers of ε₊, or ε₋, times elements
of 𝓛. The later paragraphs use nothing else. -/

@[expose] public section

namespace GeneralPieces.Series

open ClauseBound.Boson

/-- b[r'] vanishes on monomials of weight below −r', and so does every product a[r]∘b[r']. -/
theorem mul2_eq_zero (a b : List ℕ) (r : ℤ) {r' : ℤ} (π : Multiset ℕ) {σ : Multiset ℕ} (h : (σ.sum : ℤ) + r' < 0) : mul2 a r b r' π σ = 0 := by
  rw [mul2, Pz, if_neg (by omega), Finset.sum_empty]

/-- f₊ = Σ_r ⟨a[r]∘b[−r]⟩·ω₁^{r−h'}·ω₂^{−r−h}, written as a series in ω₂: the exponent of ω₂ is j =
−r − h, and it starts at j = −E − h. -/
noncomputable def fP (a b : List ℕ) (π σ : Multiset ℕ) : Lp :=
  diag (-((a.sum : ℤ) + b.sum)) (fun j => (mul2 a (-j - b.sum) b (j + b.sum) π σ : ℚ)) (-(σ.sum : ℤ) - b.sum)

/-- f₋ = Σ_r ⟨b[−r]∘a[r]⟩·ω₁^{r−h'}·ω₂^{−r−h}, written as a series in ω₁: the exponent of ω₁ is j =
r − h', and it starts at j = −E − h'. -/
noncomputable def fM (a b : List ℕ) (π σ : Multiset ℕ) : Lm :=
  diag (-((a.sum : ℤ) + b.sum)) (fun j => (mul2 b (-j - a.sum) a (j + a.sum) π σ : ℚ)) (-(σ.sum : ℤ) - a.sum)

/-- The coefficients of f₊. The start of the series cuts nothing off: there are no terms for r > E. -/
theorem cfP_fP (a b : List ℕ) (π σ : Multiset ℕ) (x y : ℤ) :
    cfP (fP a b π σ) x y = if x + y = -((a.sum : ℤ) + b.sum) then (mul2 a (x + a.sum) b (y + b.sum) π σ : ℚ) else 0 := by
  rw [cfP, fP, cf_diag]
  by_cases h : x + y = -((a.sum : ℤ) + b.sum)
  · rw [if_pos h, show -y - (b.sum : ℤ) = x + a.sum by omega]
    by_cases h2 : -(σ.sum : ℤ) - b.sum ≤ y
    · rw [if_pos ⟨h2, h⟩]
    · rw [if_neg (fun g => h2 g.1), mul2_eq_zero a b _ π (by omega), Int.cast_zero]
  · rw [if_neg h, if_neg (fun g => h g.2)]

/-- The coefficients of f₋. The start of the series cuts nothing off: there are no terms for r < −E. -/
theorem cfM_fM (a b : List ℕ) (π σ : Multiset ℕ) (x y : ℤ) :
    cfM (fM a b π σ) x y = if x + y = -((a.sum : ℤ) + b.sum) then (mul2 b (y + b.sum) a (x + a.sum) π σ : ℚ) else 0 := by
  rw [cfM, fM, cf_diag]
  by_cases h : x + y = -((a.sum : ℤ) + b.sum)
  · rw [if_pos h, show -x - (a.sum : ℤ) = y + b.sum by omega]
    by_cases h2 : -(σ.sum : ℤ) - a.sum ≤ x
    · rw [if_pos ⟨h2, by omega⟩]
    · rw [if_neg (fun g => h2 g.1), mul2_eq_zero b a _ π (by omega), Int.cast_zero]
  · rw [if_neg h, if_neg (fun g => h (by omega))]

/-- What the comparison of the coefficients of x^μ·x'^ν in the display with 𝒩 in the proof of Lemma
9 gives, for the entry (π, σ): finitely many terms (Γ_c, N_c, n_c), a number, an exponent
N_c ≤ H and an element n_c of 𝓛, the same for both signs, with f₊ = Σ_c Γ_c·ε₊^{N_c}·n_c in 𝓛₊ and
f₋ = Σ_c Γ_c·ε₋^{N_c}·n_c in 𝓛₋. In the paper c is a pair of splittings
μ = μ' ∪ μ'', ν = ν' ∪ ν'', with Γ_c = μ!·ν!·Γ_{μ',ν'}, N_c = |μ'| + |ν'| and n_c = n_{μ'',ν''}. The
terms with N_c = H are those with μ'' = ν'' = ∅: there n_c = [π = σ], and their Γ_c add
up to the number G = μ!·ν!·Γ_{μ,ν}, a parameter of the structure because it is the same for all π,
σ. The last field is "for E = 0 we have ⟨𝒩⟩ = 1". -/
structure Expansion (a b : List ℕ) (G : ℚ) (π σ : Multiset ℕ) where
  /-- The terms (Γ_c, N_c, n_c). -/
  terms : List (ℚ × ℕ × L)
  le : ∀ c ∈ terms, c.2.1 ≤ a.sum + b.sum
  plus : fP a b π σ = (terms.map fun c => c.1 • (epsP ^ c.2.1 * toP c.2.2)).sum
  minus : fM a b π σ = (terms.map fun c => c.1 • (epsM ^ c.2.1 * toM c.2.2)).sum
  top : ∀ c ∈ terms, c.2.1 = a.sum + b.sum → c.2.2 = if π = σ then 1 else 0
  tot : ((terms.filter fun c => c.2.1 = a.sum + b.sum).map fun c => c.1).sum = G
  vac : π = 0 → σ = 0 → ∀ c ∈ terms, c.2.1 < a.sum + b.sum → c.2.2 = 0

/-- The expansion exists for all monomials a, b with positive parts and every entry (π, σ) whose
monomials have no part 0, with one number G that does not depend on π and σ. -/
def StExpansion : Prop := ∀ a b : List ℕ, Pos a → Pos b → ∃ G : ℚ, ∀ π σ : Multiset ℕ, 0 ∉ π → 0 ∉ σ → Nonempty (Expansion a b G π σ)

end GeneralPieces.Series
