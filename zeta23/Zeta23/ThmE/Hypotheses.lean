/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Hypotheses.lean — Theorem E (Dirichlet L-functions), the χ-dependent densities and the
published inputs restated for L(s,χ).

Canonical text: the paper §7.2 [subsec:dirichlet], [thm:E] and its proof, items (i)–(iii), VERBATIM:
"(i) Explicit formula: with κ = (1−χ(−1))/2, Proposition prop:EF holds for
 W_χ(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)) (zeros of L(s,χ)) with ν_X replaced by
 ν_{X,χ} := μ_χ + P_{X,χ},  μ_χ(τ) := (1/2π)[log(q/π) + Re Γ′/Γ(1/4 + κ/2 + iτ/2)],
 P_{X,χ}(τ) := −(1/π) Re Σ_{n≤X} Λ(n)χ(n) n^{−1/2−iτ}, and no pole term (Π_X ≡ 0); the derivation of
 Appendix A applies to [IK04, Theorem 5.12] for L(s,χ). Since ν_{X,χ} is real, G is again real
 symmetric. (ii) Zero side: the multiset of zeros of L(s,χ) is invariant under ρ ↦ 1−ρ̄ with
 multiplicities (functional equation χ ↔ χ̄ composed with conj L(conj s,χ) = L(s,χ̄)), all zeros have
 0<β<1, and N_χ(t+1) − N_χ(t) ≪_q log(t+3); Section 4 is otherwise verbatim. (iii) Prime side:
 |Λ(n)χ(n)| = Λ(n)·1_{(n,q)=1}, so Lemma lem:cheb holds for these coefficients with O_q(·) errors
 (finitely many primes removed); … μ_χ = (1/2π) log(q|τ|/2π) + O(τ⁻²) satisfies (eq:mufacts)–(eq:muints)
 with ℓ₁ replaced by ℓ_{1,χ} := log(qT/2π) + 2log2 − 1, and λ₁ = L/ℓ_{1,χ} → λ as q is fixed."

This file is ζ-free AND L-free: it defines the densities μ_χ, P_{X,χ}, ν_{X,χ}
as explicit real functions of (κ, q, the coefficient character values) and states the hypotheses
for an ABSTRACT `ZeroConfig`; only `Zeta23/ThmE/Statement.lean` mentions Mathlib's
`DirichletCharacter.LFunction`.  Everything the paper derives from these inputs is proved in the sibling files;
this file only states the inputs.
-/
import Zeta23.Hypotheses
import Mathlib.NumberTheory.DirichletCharacter.Basic

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23
namespace ThmE

/-! ## 1. The χ-dependent scalars and densities  ([thm:E] proof (i), (iii)) -/

/-- `ℓ_{1,χ} := log(qT/2π) + 2 log 2 − 1`  ([thm:E] proof (iii)); for q = 1 this is `Zeta23.ell1`. -/
def ell1q (q : ℕ) (T : ℝ) : ℝ := Real.log (q * T / (2 * Real.pi)) + 2 * Real.log 2 - 1

/-- `μ_χ(τ) := (1/2π)[log(q/π) + Re Γ′/Γ(1/4 + κ/2 + iτ/2)]`  ([thm:E] proof (i)), as a function of the
parity `κ ∈ {0,1}` (`κ = (1−χ(−1))/2`) and the modulus `q`.  For `κ = 0, q = 1` this is `Zeta23.mu`
(since log(1/π) = −log π).  Γ′/Γ = `Complex.digamma`. -/
def muq (κ : ℕ) (q : ℕ) (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (Real.log (q / Real.pi) + (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + Complex.I * τ / 2)).re)

/-- `P_{X,χ}(τ) := −(1/π) Re Σ_{n≤X} Λ(n) χ(n) n^{−1/2−iτ}`  ([thm:E] proof (i)), as a function of the
coefficient sequence `c n = χ(n)` (values of the character on ℕ).  Sum over `Finset.Ioc 0 ⌊X⌋₊` as in
`Zeta23.PX`; for `c ≡ 1` this is `Zeta23.PX` since Re n^{−iτ} = cos(τ log n). -/
def PXc (c : ℕ → ℂ) (X : ℝ) (τ : ℝ) : ℝ :=
  -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
    ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re

/-- `ν_{X,χ} := μ_χ + P_{X,χ}`, "and no pole term (Π_X ≡ 0)"  ([thm:E] proof (i)). -/
def nuXc (κ q : ℕ) (c : ℕ → ℂ) (X : ℝ) (τ : ℝ) : ℝ := muq κ q τ + PXc c X τ

/-- Admissible coefficient sequences for modulus q ([thm:E] (iii)): unimodular-or-zero character
values, vanishing off (n,q) = 1.  (For χ primitive, c n = χ(n) qualifies.) -/
structure CoeffOK (q : ℕ) (c : ℕ → ℂ) : Prop where
  norm_le : ∀ n, ‖c n‖ ≤ 1
  vanish : ∀ n, ¬ Nat.Coprime n q → c n = 0

/-- Unimodular coefficient sequences: additionally `‖c n‖ = 1` exactly on `(n,q) = 1`, `n > 0`
(true for a primitive χ).  Needed wherever the main term is TWO-sided ([prop:PP]'s diagonal uses
`|χ(n)|² = 1`); the four upper-bound statements only need `CoeffOK`. -/
structure CoeffUnimodular (q : ℕ) (c : ℕ → ℂ) : Prop extends CoeffOK q c where
  norm_eq : ∀ n, 0 < n → Nat.Coprime n q → ‖c n‖ = 1

/-! ## 2. The published inputs, restated for L(s,χ)  (abstract zero configuration Z) -/

/-- **H-EF(χ), paper form** ([thm:E] proof (i) applied to [prop:EF]/[eq:EF]): for f,g ∈ C_c²(ℝ) with
supports in [−L/2, L/2],  W_χ(f,g) = ∫_ℝ h_f(τ) conj(h_g(τ)) ν_{X,χ}(τ) dτ, X = e^L, with the zero sum
absolutely convergent and the integrand integrable (same shape as `Zeta23.ExplicitFormulaPaper`, whose
ν_X is replaced by ν_{X,χ}). -/
def ExplicitFormulaPaperChi (κ q : ℕ) (c : ℕ → ℂ) (Z : ZeroConfig) : Prop :=
  ∀ (L : ℝ), 0 < L → ∀ (f g : ℝ → ℂ), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    tsupport f ⊆ Icc (-(L / 2)) (L / 2) → tsupport g ⊆ Icc (-(L / 2)) (L / 2) →
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
    Integrable (fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuXc κ q c (Real.exp L) τ : ℂ)) ∧
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuXc κ q c (Real.exp L) τ : ℂ)

/-- **H-RvM(χ)**: `N_χ(T,2T) = (T/2π) ℓ_{1,χ} + O_q(log T)` ([thm:E] intro sentence with (iii)'s ℓ_{1,χ};
classical, [Dav00 §16]) and the local count `N_χ(t+1) − N_χ(t) ≪_q log(|t|+3)` ([thm:E] proof (ii)),
two-sided as in `Zeta23.RiemannVonMangoldt`. Constants may depend on q (q is fixed in [thm:E]). -/
structure RiemannVonMangoldtChi (q : ℕ) (Z : ZeroConfig) : Prop where
  main : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ C * Real.log T
  local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)

/-- **H-Γ(χ)**: "μ_χ = (1/2π)log(q|τ|/2π) + O(τ⁻²) satisfies (eq:mufacts)–(eq:muints) with ℓ₁ replaced
by ℓ_{1,χ}" ([thm:E] proof (iii)) — the nine fields of `Zeta23.GammaFacts` for `muq κ q` and `ell1q q`. -/
structure GammaFactsChi (κ q : ℕ) : Prop where
  even : ∀ τ : ℝ, muq κ q (-τ) = muq κ q τ
  smooth : ContDiff ℝ ⊤ (muq κ q)
  monotoneOn : MonotoneOn (muq κ q) (Ici 0)
  mu_zero_le : ∀ τ : ℝ, muq κ q 0 ≤ muq κ q τ
  neg_one_lt_mu_zero : -1 < muq κ q 0
  stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv (muq κ q) τ| ≤ C / |τ|
  int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), muq κ q τ) - T * ell1q q T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2

/-- **The Chebyshev–Mertens bounds for the coefficients Λ(n)χ(n)** ([thm:E] proof (iii): "|Λ(n)χ(n)| =
Λ(n)·1_{(n,q)=1}, so Lemma lem:cheb holds for these coefficients with O_q(·) errors (finitely many
primes removed)").  Since only |a_n| enters, and |χ(n)| ≤ 1, the UPPER bounds of [lem:cheb] hold
verbatim; the two-sided [eq:cheb2] asymptotics need the (n,q)=1 restriction.  Stated here in
hypothesis shape (cf. `Zeta23.Cheb.chebyshevMertens`). -/
structure ChebyshevMertensCoprime (q : ℕ) : Prop where
  cheb2a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), Λ n ^ 2 / n
      - Real.log x ^ 2 / 2| ≤ C * Real.log x
  cheb2b : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
        Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6| ≤ C * Real.log x ^ 2

/-- The published inputs for Theorem E at parity κ, modulus q, coefficient character values c,
for an abstract zero configuration Z (analogue of `Zeta23.PaperInputs`). -/
structure PaperInputsChi (κ q : ℕ) (c : ℕ → ℂ) (Z : ZeroConfig) : Prop where
  EF : ExplicitFormulaPaperChi κ q c Z
  RvM : RiemannVonMangoldtChi q Z
  cheb : ChebyshevMertens
  chebq : ChebyshevMertensCoprime q
  MV : ∃ C : ℝ, 0 < C ∧ MVHilbert C
  Gamma : GammaFactsChi κ q

/-! ## PXc unfolding lemmas (shared by the Theorem E prime-side files) -/

section PXcUnfold

/-- `n^{−1/2−iτ} = n^{−1/2}·e^{−iτ log n}` for `n ≥ 1`. -/
lemma natCast_cpow_neg_half_sub_I_mul {n : ℕ} (hn : 0 < n) (τ : ℝ) :
    (n : ℂ) ^ (-(1/2 : ℂ) - Complex.I * τ)
      = (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (τ * Real.log n))) := by
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℂ)) = (((n : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog, show ((Real.log n : ℝ) : ℂ) * (-(1/2 : ℂ) - Complex.I * τ)
      = ((-(Real.log n) / 2 : ℝ) : ℂ) + -(Complex.I * (τ * Real.log n)) by push_cast; ring,
    Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  norm_cast
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
  ring_nf

/-- `e^{−iθ} = cos θ − i sin θ`, real θ, cast form. -/
lemma exp_neg_I_mul_ofReal (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ : ℂ)))
      = ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, show ((-θ : ℝ) : ℂ) = -((θ : ℝ) : ℂ) by push_cast; ring,
    Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- `P_{X,χ}` as a real sum of phase-split cosines/sines, coefficients `(c n).re, (c n).im`:
`P_{X,c}(τ) = −π⁻¹ Σ_{n≤X} Λ(n) n^{−1/2} ((c n).re·cos(τ log n) + (c n).im·sin(τ log n))`. -/
lemma PXc_eq_sum_cos_sin (c : ℕ → ℂ) (X τ : ℝ) :
    PXc c X τ = -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) *
        ((c n).re * Real.cos (τ * Real.log n) + (c n).im * Real.sin (τ * Real.log n)) := by
  unfold PXc
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  rw [natCast_cpow_neg_half_sub_I_mul hn0,
    show -(Complex.I * ((τ : ℂ) * ((Real.log n : ℝ) : ℂ)))
      = -(Complex.I * ((τ * Real.log n : ℝ) : ℂ)) by push_cast; ring,
    exp_neg_I_mul_ofReal]
  have e1 : ((Λ n : ℝ) : ℂ) * c n * ((((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ)
      * (((Real.cos (τ * Real.log n) : ℝ) : ℂ) - ((Real.sin (τ * Real.log n) : ℝ) : ℂ) * Complex.I))
      = ((((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) : ℝ)) : ℂ)
        * (c n * (((Real.cos (τ * Real.log n) : ℝ) : ℂ)
            - ((Real.sin (τ * Real.log n) : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [e1, Complex.re_ofReal_mul]
  have hw : (c n * (((Real.cos (τ * Real.log n) : ℝ) : ℂ)
      - ((Real.sin (τ * Real.log n) : ℝ) : ℂ) * Complex.I)).re
      = (c n).re * Real.cos (τ * Real.log n) + (c n).im * Real.sin (τ * Real.log n) := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [hw]

end PXcUnfold

/-! ## Uniform-constant ("Bounded") variants, for the hybrid range [rem:otherL](i):
same fields as `GammaFactsChi` / `ChebyshevMertensCoprime`
but with every existential constant replaced by the given bound, so families of characters can
carry ONE constant uniformly in q. -/

/-- `GammaFactsChi` with all constants bounded by `C` (and all thresholds by `C`). -/
structure GammaFactsChiBounded (κ q : ℕ) (C : ℝ) : Prop where
  even : ∀ τ : ℝ, muq κ q (-τ) = muq κ q τ
  smooth : ContDiff ℝ ⊤ (muq κ q)
  monotoneOn : MonotoneOn (muq κ q) (Ici 0)
  mu_zero_le : ∀ τ : ℝ, muq κ q 0 ≤ muq κ q τ
  neg_one_lt_mu_zero : -1 < muq κ q 0
  stirling : ∀ τ : ℝ, 1 ≤ |τ| →
    |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  deriv_bound : ∀ τ : ℝ, 1 ≤ |τ| → |deriv (muq κ q) τ| ≤ C / |τ|
  int_mu : ∀ T : ℝ, C ≤ T →
    |(∫ τ in T..(2 * T), muq κ q τ) - T * ell1q q T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∀ T : ℝ, C ≤ T →
    |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2

/-- forgetting the uniformity. -/
lemma GammaFactsChiBounded.toGammaFactsChi {κ q : ℕ} {C : ℝ}
    (h : GammaFactsChiBounded κ q C) : GammaFactsChi κ q :=
  ⟨h.even, h.smooth, h.monotoneOn, h.mu_zero_le, h.neg_one_lt_mu_zero,
    ⟨C, h.stirling⟩, ⟨C, h.deriv_bound⟩, ⟨C, C, h.int_mu⟩, ⟨C, C, h.int_mu_sq⟩⟩

/-- `ChebyshevMertensCoprime` with both constants bounded by `B`. -/
structure ChebyshevMertensCoprimeBounded (q : ℕ) (B : ℝ) : Prop where
  cheb2a : ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), Λ n ^ 2 / n
      - Real.log x ^ 2 / 2| ≤ B * Real.log x
  cheb2b : ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
        Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6| ≤ B * Real.log x ^ 2

/-- forgetting the uniformity. -/
lemma ChebyshevMertensCoprimeBounded.toChebyshevMertensCoprime {q : ℕ} {B : ℝ}
    (h : ChebyshevMertensCoprimeBounded q B) : ChebyshevMertensCoprime q :=
  ⟨⟨B, h.cheb2a⟩, ⟨B, h.cheb2b⟩⟩

end ThmE
end Zeta23
