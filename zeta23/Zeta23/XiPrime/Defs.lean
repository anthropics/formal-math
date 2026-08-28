/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ## 1. Riemann's ξ and its derivative, against Mathlib  [XF′ §0]

Mathlib: completedRiemannZeta s = Λ(s) = π^{-s/2} Γ(s/2) ζ(s) (poles at 0, 1), and the entire
completedRiemannZeta₀ = Λ₀ with Λ(s) = Λ₀(s) − 1/s − 1/(1−s) (completedRiemannZeta_eq).  Riemann's
ξ(s) := ½ s(s−1) Λ(s) = ½ s(s−1) Λ₀(s) + ½, entire by construction.  The body below is verbatim that
of Zeta23.WeilEF.xi, so XiPrime.xi = WeilEF.xi holds by rfl. -/

/-- ξ(s) := s(s−1)/2 · Λ₀(s) + 1/2  (= ½ s(s−1) π^{-s/2} Γ(s/2) ζ(s) for s ∉ {0,1}; entire). -/
def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

/-- ξ′ := the complex derivative of ξ (an entire function; [XF′ §0] writes F := (ξ′)′/ξ′). -/
def xiDeriv : ℂ → ℂ := deriv xi

/-- ρ₁ is a zero of ξ′:  ξ′(ρ₁) = 0 — all zeros, no real-part condition (the
denominator of every headline proportion counts every zero of ξ′ in the height window, exactly as
[XF′ Thm 8.2] does).  The classical fact (F2) of [XF′ §1], "all zeros of ξ′ lie in 0 < Re s < 1"
(Re ξ′/ξ = Σ_ρ Re 1/(s−ρ) > 0 for Re s ≥ 1 via the Hadamard product for ξ, then ξ′(1−s) = −ξ′(s);
Conrey, J. Number Theory 16 (1983) §2), is not built into this predicate: it is the named proposition
XiPrime.XiDerivZerosInStrip of Statement.lean. -/
def IsXiDerivZero (ρ : ℂ) : Prop := xiDeriv ρ = 0

/-- m_{ρ₁} := multiplicity of ρ₁ as a zero of ξ′ = analytic order of ξ′ at ρ₁ (ℕ∞ → ℕ via toNat; as for
Zeta23.zeroMult, 1 ≤ xiDerivMult ρ encodes "ξ′ not locally ≡ 0 at ρ AND ξ′(ρ) = 0"). -/
def xiDerivMult (ρ : ℂ) : ℕ := (analyticOrderAt xiDeriv ρ).toNat

/-- {ρ₁ : ξ′(ρ₁) = 0, T₁ < Im ρ₁ ≤ T₂}  (ALL zeros in the height window; positive ordinates, NOT |Im|). -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsXiDerivZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N_{ξ′}(T₁,T₂) := number of zeros of ξ′ with T₁ < Im ≤ T₂ (any real part), COUNTED WITH MULTIPLICITY
([XF′ (F3)]: N_{ξ′}(T) = N(T) + O(log T)).  This is the DENOMINATOR of every headline proportion. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, xiDerivMult ρ

/-- N_{d,ξ′}(T₁,T₂) := number of DISTINCT zeros of ξ′ with T₁ < Im ≤ T₂ (any real part). -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N^{s}_{0,ξ′}(T₁,T₂) := #{ρ₁ : T₁ < Im ρ₁ ≤ T₂, Re ρ₁ = 1/2, m_{ρ₁} = 1}: SIMPLE zeros of ξ′ ON the
critical line (each such point counted once — it is simple).  Numerator of [XF′ Thm 8.2, first line]. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | xiDerivMult ρ = 1}).ncard

/-- N_{0,ξ′}(T₁,T₂) := zeros of ξ′ on the critical line, with multiplicity (for the trivial chain only). -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, xiDerivMult ρ

/-! ## 2. The coefficient system C(N; Λ⋆)  [XF′ Def. 2.3]

[XF′ Def 2.3], verbatim: "C(N;Λ⋆) := −Λ(N) + Σ_{j=0}^{Ω(N)−1} Λ⋆^{−(j+1)} [(Λ·log) ∗ Λ^{∗j}](N)",
where ∗ is Dirichlet convolution, Λ^{∗0} = δ, Ω(N) = number of prime factors with multiplicity (the
j-sum is genuinely finite: Λ^{∗j} is supported on N with Ω(N) ≥ j, so (Λ log) ∗ Λ^{∗j} needs Ω(N) ≥ j+1).
Lean: Λ = ArithmeticFunction.vonMangoldt (ℝ-valued), log = ArithmeticFunction.log, pointwise product =
pmul, Dirichlet convolution = the ring multiplication of ArithmeticFunction ℝ, so Λ ^ j is the j-fold
DIRICHLET power (Λ ^ 0 = 1 = δ), Ω = ArithmeticFunction.cardFactors.  Λ⋆ is a COMPLEX parameter
([XF′] uses Λ⋆ = L⋆ = ½ log(τ⋆/2π) + iπ/4 for ξ′ and the REAL value ½ log(τ⋆/2π) for Z′). -/

/-- the real arithmetic function (Λ·log) ∗ Λ^{∗j}. -/
def lamLogConv (j : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.pmul (Λ : ArithmeticFunction ℝ) ArithmeticFunction.log) * (Λ : ArithmeticFunction ℝ) ^ j

/-- C(N; Λ⋆) ∈ ℂ  [XF′ Def 2.3].  (For Λ⋆ = 0 Lean reads 0⁻¹ = 0; irrelevant, |Λ⋆| > A(σ₁) always.) -/
def xiCoeff (Λs : ℂ) (N : ℕ) : ℂ :=
  -((Λ N : ℝ) : ℂ) +
    ∑ j ∈ Finset.range (ArithmeticFunction.cardFactors N),
      (Λs⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)

/-- L_T := ½ l + iπ/4,  l = log(T/2π)  [XF′ §6]: the frozen parameter ("b_N := C(N; L_T)"). -/
def LT (T : ℝ) : ℂ := ((l T / 2 : ℝ) : ℂ) + Complex.I * (Real.pi / 4 : ℝ)

/-- L⋆(τ⋆) := ½ log(τ⋆/2π) + iπ/4  [XF′ Def 2.3 / Thm 4.2]: the entry-dependent frozen parameter,
τ⋆ = ½(τ_k + τ_l). -/
def Lstar (τs : ℝ) : ℂ := ((Real.log (τs / (2 * Real.pi)) / 2 : ℝ) : ℂ) + Complex.I * (Real.pi / 4 : ℝ)

/-- L_{2⋆}(τ⋆) := ½ log(τ⋆/2π) ∈ ℝ  [XF′ Thm 9.2]: the Z′ frozen parameter (no phase). -/
def L2star (τs : ℝ) : ℝ := Real.log (τs / (2 * Real.pi)) / 2

/-! ## 3. Prime-side densities with general complex coefficients  [XF′ Thm 4.2, §6] -/

/-- P_c(X; τ) := (1/π) Re Σ_{N ≤ X} c_N N^{−1/2−iτ}
            = (1/π) Σ_{N ≤ X} (Re c_N · cos(τ log N) + Im c_N · sin(τ log N)) / √N
for an arbitrary coefficient sequence c : ℕ → ℂ (the real-part form of [XF′ Thm 4.2]; for
c = −Λ this is the paper's P_X = Zeta23.PX, for c = Λ·χ it is ThmE's twisted density).  Indexing
Finset.Ioc 0 ⌊X⌋₊ as Zeta23.PX. -/
def Pc (X : ℝ) (c : ℕ → ℂ) (τ : ℝ) : ℝ :=
  (1 / Real.pi) * ∑ N ∈ Finset.Ioc 0 ⌊X⌋₊,
    ((c N).re * Real.cos (τ * Real.log N) + (c N).im * Real.sin (τ * Real.log N)) / Real.sqrt N

/-- P^{(1)}_X(τ; Λ⋆) := P_c(X; τ) with c = C(·; Λ⋆)  [XF′ Thm 4.2]. -/
def P1X (X : ℝ) (Λs : ℂ) (τ : ℝ) : ℝ := Pc X (xiCoeff Λs) τ

/-- ν_{c,ϖ}(X) := μ + ϖ·Π_X + P_c(X): density with general coefficients c and POLE WEIGHT ϖ (so that ξ′ and
Z′ are one prime-side theorem).  ξ′: ϖ = 1 [XF′ Thm 4.2(a)];  Z′: ϖ = 2 [Thm 9.2(a)]. -/
def nucW (cPi X : ℝ) (c : ℕ → ℂ) (τ : ℝ) : ℝ := mu τ + cPi * PiX X τ + Pc X c τ

/-- ν_c(X) := μ + Π_X + P_c(X)  (pole weight 1; the ξ′ density). -/
def nuc (X : ℝ) (c : ℕ → ℂ) (τ : ℝ) : ℝ := nucW 1 X c τ

/-- ν^{𝒵}_c(X) := μ + 2·Π_X + P_c(X)  (pole weight 2; the Z′ density). -/
def nucZ (X : ℝ) (c : ℕ → ℂ) (τ : ℝ) : ℝ := nucW 2 X c τ

end XiPrime

namespace Params

variable (P : Params) (T : ℝ)

/-- M^{c,ϖ}_{kl} := ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_{c,ϖ}(X;τ) dτ, X = e^L: the prime-side Gram entry for FIXED
coefficients c and pole weight ϖ.  The integrand is parenthesised as ONE product (binder-swallow guard). -/
def GentryCW (cPi : ℝ) (c : ℕ → ℂ) (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, (P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * XiPrime.nucW cPi (P.X T) c τ)

/-- M^{c}_{kl} := the pole-weight-1 (ξ′) entry  ([XF′ §6] "M^T" is c = C(·;L_T); Zeta23.Params.Gentry is
c = −Λ up to nuc 1 = nuX by rfl-unfolding). -/
def GentryC (c : ℕ → ℂ) (k l : ℤ) : ℝ := P.GentryCW T 1 c k l

/-- the d×d matrix (M^{c}_{kl})_{0≤k,l<d} as a complex matrix (entries real), same typing as P.Gp. -/
def GpC (c : ℕ → ℂ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.GentryC T c (k : ℤ) (l : ℤ) : ℂ)

/-- τ⋆_{kl} := ½(τ_k + τ_l). -/
def tauStar (k l : ℤ) : ℝ := (P.tau T k + P.tau T l) / 2

/-- M_{kl} := ∫ φ̂(τ−τ_k) φ̂(τ−τ_l) [μ + Π_X + P^{(1)}_X(τ; L⋆^{kl})] dτ — the ENTRY-DEPENDENT main term
of [XF′ Thm 4.2] (coefficients frozen at L⋆ = L⋆(τ⋆_{kl})). -/
def Gentry1 (k l : ℤ) : ℝ := P.GentryC T (XiPrime.xiCoeff (XiPrime.Lstar (P.tauStar T k l))) k l

/-- the d×d matrix M of entry-dependent main terms. -/
def Gp1 : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.Gentry1 T (k : ℤ) (l : ℤ) : ℂ)

end Params

namespace XiPrime

/-! ## 4. The diagonal density D₁ and the window functional  [XF′ Lemma 7.1, Thm 8.1] -/

/-- d_k := 2·4^k (k−1)!/(2k)!  (k ≥ 1), the coefficient of s^{2k+1} in D₁; d₁ = 4, d₂ = 4/3, d₃ = 16/45, …
Stated for the shifted index: D1coeff k = d_{k+1} = 2·4^{k+1}·k!/(2k+2)!. -/
def D1coeff (k : ℕ) : ℝ := 2 * (4 : ℝ) ^ (k + 1) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

/-- D₁(s) := s − 4s² + Σ_{k≥1} d_k s^{2k+1}  [XF′ Lemma 7.1]  (= Σ_k D_{1,k}: D_{1,1} = s(2s−1)²,
D_{1,k} = 4^k(k−1)!/(k(2k−1)!) s^{2k+1} for k ≥ 2; Farmer–Gonek's F₁ minus its T^{-2α} log T term).
The series has infinite radius of convergence (tsum form). -/
def D1 (s : ℝ) : ℝ := s - 4 * s ^ 2 + ∑' k : ℕ, D1coeff k * s ^ (2 * k + 3)

/-- truncation of D₁ keeping k ≤ K (K ≥ 1 terms of the series), a polynomial; the certificate works with
D1trunc 9 and the tail bound ε₉ ≤ 3.43·10⁻⁷ on [0,1]  [XF′ Thm 8.2 "Certified constants"]. -/
def D1trunc (K : ℕ) (s : ℝ) : ℝ := s - 4 * s ^ 2 + ∑ k ∈ Finset.range K, D1coeff k * s ^ (2 * k + 3)

/-- (v⋆v)(r) := ∫_{−1/2}^{1/2−r} v(s)·v(s+r) ds — the autocorrelation of the profile on the unit window, for
lags 0 ≤ r ≤ 1 (both s and s+r range over [−1/2,1/2]; = L⁻¹·(autocorrelation of the sharp window
u ↦ v(u/L)·1_{[−L/2,L/2]} at lag rL)).  ONE parenthesised product.  (This is the form the prime side's
J_T converges to with no Fubini step.) -/
def vConv (v : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2 - r), (v s * v (s + r))

/-- 𝒥_D(λ; v) := 2 ∫₀¹ D(λr)·(v⋆v)(r) dr   [XF′ Thm 8.1, proof: "J_{D₁} = (2/λ)∫₀¹(v⋆v)(r)D₁(λr)dr
= (1/λ)∬_{[−1/2,1/2]²} D₁(λ|s−s′|)v(s)v(s′) ds ds′" — we take the FIRST displayed form as the definition;
λ·𝒥_D = λ²·J_D].  ζ check: D(s) = s, v ≡ 1: vConv 1 r = 1 − r, jWin = 2λ∫₀¹ r(1−r)dr = λ/3. -/
def jWin (D : ℝ → ℝ) (lam : ℝ) (v : ℝ → ℝ) : ℝ := 2 * ∫ r in (0:ℝ)..1, (D (lam * r) * vConv v r)

/-- The generalised window functional  c_λ(v; D) := λ(∫v)² / (∫v² + λ·𝒥_D(λ;v)),  ∫ over [−1/2, 1/2]
[XF′ Thm 8.1: c^{(1)}_λ(v) = c_λ(v; D₁) = λ(∫v)²/(∫v² + λ∬D₁(λ|s−s′|)vv′)].  For D(s) = s this equals
Zeta23.ThmD.cFun (λ²∬|s−s′|vv′). -/
def cWin (D : ℝ → ℝ) (lam : ℝ) (v : ℝ → ℝ) : ℝ :=
  lam * (∫ s in (-(1:ℝ)/2)..(1/2), v s) ^ 2 /
    ((∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + lam * jWin D lam v)

/-- κ₁(λ, v) := 1/c_λ(v; D₁) — the ξ′ second-moment constant ("‖Ĝ^{(1)}‖_F² = κ₁ N (1+o(1))").
For the flat window v ≡ 1 (vConv 1 r = 1 − r): κ₁(λ,1) = 1/λ + 2∫₀¹(1−r)D₁(λr)dr (ζ analogue, D(s) = s:
1/λ + λ/3 = Zeta23.kfun). -/
def kappaXi (lam : ℝ) (v : ℝ → ℝ) : ℝ := 1 / cWin D1 lam v

/-- the flat window profile v ≡ 1 on [−1/2,1/2] (realised by the tree's ramp taper P.phi, φ² = v(u/L)
up to the width-w ramps). -/
def vFlat : ℝ → ℝ := fun _ => 1

/-- the explicit quartic window v(s) = 1 − (7/100)(2s)² − (51/200)(2s)⁴  [XF′ Thm 8.2 "Certified
constants"]: positive on [−1/2,1/2] (min 27/40 at s = ±1/2), even, polynomial; it saturates the
numerically optimal window to 10⁻⁶. -/
def vQuartic (s : ℝ) : ℝ := 1 - 7 / 100 * (2 * s) ^ 2 - 51 / 200 * (2 * s) ^ 4

/-- the window with profile v realised on the tree's taper: φ_v(u) := √(v(u/L)) · φ(u), so that
φ_v² = v(u/L)·φ² (ThmD's phiD pattern with cos(√2λ·) ↦ v).  max 0 guards the sqrt off [−L/2,L/2]. -/
def _root_.Zeta23.Params.phiV (P : Params) (v : ℝ → ℝ) (T : ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (max 0 (v (u / P.L T))) * P.phi T u

/-- the per-height parameter set realising φ_v at height T (ThmD's Params.atD trick, Zeta23/ThmD/ParamsD.lean:
(P.atV v T).phi T = P.phiV v T, while λ, w, L, X, d, τ_k, … are P's, definitionally). -/
def _root_.Zeta23.Params.atV (P : Params) (v : ℝ → ℝ) (T : ℝ) : Params :=
  ⟨fun x => P.phiV v T (P.L T / 2 - P.w * x), P.lam, P.w⟩

/-! ## 5. Hardy-side objects for the Z′ theorem  [XF′ §9.0] -/

/-- χ(s) := Λ(1−s)/Λ(s)·(Γ-part) — concretely the factor with ζ(s) = χ(s) ζ(1−s); we take the Mathlib-native
form χ := Gammaℝ(1−s)/Gammaℝ(s) (Gammaℝ s = π^{-s/2}Γ(s/2)), meromorphic. -/
def chiFE (s : ℂ) : ℂ := Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s

/-- L₂(s) := −½ χ′/χ (s)  [XF′ §9.0]  (= ½(L(s)+L(1−s)); real on Re s = 1/2, = ϑ′(t) there). -/
def L2 (s : ℂ) : ℂ := -(1 / 2) * logDeriv chiFE s

/-- W(s) := ζ′(s) − ½ (χ′/χ)(s) ζ(s) = ζ′(s) + L₂(s) ζ(s)  [XF′ §9.0]; meromorphic on ℂ (poles at 0, 1,
3, 5, …), real on ℝ, and  Z′(t) = i e^{iϑ(t)} W(½+it)  [XF′ (Z3)], so the zeros of W on Re s = 1/2 are
exactly the stationary points of Hardy's Z, with multiplicity. -/
def hardyW (s : ℂ) : ℂ := deriv riemannZeta s + L2 s * riemannZeta s

/-- ρ is a non-real zero of W:  W ρ = 0 ∧ Im ρ ≠ 0 — no real-part condition (as for ξ′).
W is meromorphic with poles only on ℝ (at 0, 1, 3, 5, …) and has infinitely many real zeros [XF′ (Z6)];
"Im ρ ≠ 0" removes both (at a pole Mathlib's deriv/values are junk and analyticOrderAt = 0, so poles must
not be admitted as "zeros"), and the height window T < Im ρ ≤ 2T, T > 0, never sees them anyway.  The
classical fact (Z6)(iii) "every zero of W with |Im| ≥ t₀ lies in 0 < Re < 1" (Littlewood's gap theorem +
de la Vallée Poussin) is the named proposition XiPrime.WZerosInStrip of Statement.lean. -/
def IsWZero (ρ : ℂ) : Prop := hardyW ρ = 0 ∧ ρ.im ≠ 0

/-- multiplicity of a zero of W := analytic order of W (W is analytic off its real poles). -/
def wMult (ρ : ℂ) : ℕ := (analyticOrderAt hardyW ρ).toNat

/-- zeros of W with T₁ < Im ≤ T₂ (any real part; non-real automatically when T₁ ≥ 0). -/
def zerosInW (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsWZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N_W(T₁,T₂), with multiplicity  [XF′ (Z7)]: = N(T₁,T₂) + O(log T₂). -/
def NcountW (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosInW T₁ T₂, wMult ρ

/-- N_{d,W}(T₁,T₂): distinct zeros of W with T₁ < Im ≤ T₂. -/
def NdistW (T₁ T₂ : ℝ) : ℕ := (zerosInW T₁ T₂).ncard

/-- #{ρ : T₁ < Im ρ ≤ T₂, Re ρ = 1/2, W(ρ) = 0 simple} = #{t ∈ (T₁,T₂] : Z′(t) = 0 ≠ Z″(t)}  [XF′ (Z3)]. -/
def N0simpleW (T₁ T₂ : ℝ) : ℕ :=
  (zerosInW T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | wMult ρ = 1}).ncard

end XiPrime
end Zeta23
