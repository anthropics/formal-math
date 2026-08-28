/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side (paper §5 [sec:prime]) — ABSTRACT LAYER & SHARED DEFINITIONS
for PrimeSideA.lean / PrimeSideB.lean.

Bracketed labels and section numbers (§5.2, …) are as in the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".

SEAM between PrimeSideA.lean and PrimeSideB.lean:
  * The seam object is the symmetric bilinear form
        𝓜[u₁,u₂] := ∬_{I×I} Φ(τ−τ')² u₁(τ) u₂(τ') dτ dτ',   I = [T,2T]          (§5.4)
    spelled here LITERALLY as `Mform Φ T u₁ u₂` below, and 𝓜 := 𝓜[ν_X,ν_X] = `MtotalA`.
  * PrimeSideA.lean : [prop:trace] tr G̃ = aL·N(T,2T)+O(L√X);
      [eq:trG2int]+[eq:Kbounds]+[lem:ends] tr G̃² = 𝓜 + O(L·l·log l·(l²+X));
      [eq:Msplit] (6-term expansion of 𝓜); [prop:mumu]; [prop:cross] (four bounds).
  * PrimeSideB.lean : [prop:PP] incl. 𝒟/𝒪₁/𝒪₂ and the g-sandwich via H-cheb [eq:cheb2];
      [thm:traces] = [eq:tr1],[eq:tr2],[eq:ratio] assembling A's five results + prop:PP + H-Γ [eq:muints] + H-RvM.
  * Error-term shape everywhere: ∃ C T₀ (allowed to depend on the profile constants and on λ),
      ∀ T ≥ T₀, |lhs − main| ≤ C·(error expression).  No filters / IsBigO until the final liminf wrapper.

ABSTRACT LAYER.  §5 is a computation about the functions φ̂, Φ, μ, Π_X, P_X on the REAL line
using only a short list of facts about them ([eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
[lem:poisson], [eq:mufacts], [eq:PiPfacts], [lem:cheb]).  We therefore prove §5 for ABSTRACT data
(`Setting` = the scalars T, λ, w;  `LocalFun` = the taper data φ̂, Φ, A_φ, g, a, b) subject
to exactly those facts (hypothesis structures in PrimeSideA.lean), and a thin bridge
(Zeta23/PrimeSideA/Bridge.lean) instantiates it with the
concrete objects of Zeta23/Defs.lean: `Zeta23.Params.phiHatR`, `.PhiR`, `.a`, `.b`, `.g`, `.Aphi`,
so that `trGtA` below becomes `Zeta23.Params.trGtilde` etc.  Names in this
layer carry a trailing `A` (abstract) where they would otherwise clash with Zeta23/Defs.lean.
The closed-form, ζ-free objects `Zeta23.l`, `Zeta23.ell1`, `Zeta23.mu` [eq:mudef], `Zeta23.PiX` [eq:Pidef],
`Zeta23.PX` [eq:Pdef], `Zeta23.nuX` [eq:nudef] are used DIRECTLY from Zeta23/Defs.lean, and the analytic
inputs H-Γ / H-cheb are Zeta23/Hypotheses.lean's `GammaFacts` / `ChebyshevMertens` verbatim, so the
statements here are literally about the official objects of Zeta23/Defs.lean; only the taper enters
abstractly.

The prime side is ζ-free: N(T,2T) enters only as an abstract real together
with [eq:RvM].

FOURIER CONVENTION: paper f̂(τ) := ∫ f(u) e^{iτu} du (§1.4) = `Zeta23.paperFT`.  On
this side we only meet φ̂ and Φ := (φ²)^ on ℝ, where they are real and even; we carry them as
functions ℝ → ℝ (= `phiHatR`, `PhiR` of Defs.lean).
-/
import Mathlib
import Zeta23.Hypotheses


noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Scalars of the abstract setting  [§1 Notation, §1.4; eq:wrange; eq:fk] -/

/-- The free scalar parameters: height `T`, bandwidth ratio `λ` (`0<λ≤1`), ramp width `w`
([eq:wrange] `1 ≤ w ≤ L/8`; §6 takes `w = 1`).  (Zeta23/Defs.lean's `Params` = (ϱ, λ, w) with `T`
separate; the bridge is `fun (P : Zeta23.Params) T => ⟨T, P.lam, P.w⟩` and then `L, X, d, tau, h`
below agree with `P.L T, P.X T, P.d T, P.tau T, P.hgrid T` by `rfl`.) -/
structure Setting where
  T : ℝ
  lam : ℝ
  w : ℝ

namespace Setting
variable (p : Setting)

/-- `l := log(T/2π)` [Notation] — this IS `Zeta23.l p.T`. -/
abbrev l : ℝ := Zeta23.l p.T
/-- `ℓ₁ := l + 2 log 2 − 1` [Notation] — this IS `Zeta23.ell1 p.T`.  NOTE ℓ₁ ≠ l. -/
abbrev ell1 : ℝ := Zeta23.ell1 p.T
/-- `L := λ l` [Notation] (same body as `Zeta23.Params.L`). -/
def L : ℝ := p.lam * Zeta23.l p.T
/-- `X := e^L = (T/2π)^λ` [Notation] (same body as `Zeta23.Params.X`). -/
def X : ℝ := Real.exp p.L
/-- Grid spacing `h := 2π/L` [§2.2] (= `Zeta23.Params.hgrid`). -/
def h : ℝ := 2 * Real.pi / p.L
/-- `d := ⌊T/h⌋ = ⌊LT/2π⌋` [§2.2] (= `Zeta23.Params.d`). -/
def d : ℕ := ⌊p.L * p.T / (2 * Real.pi)⌋₊
/-- Grid points `τ_k := T + k h  (k ∈ ℤ)` [eq:fk] (= `Zeta23.Params.tau`). -/
def tau (k : ℤ) : ℝ := p.T + k * p.h
/-- The window `I := [T, 2T]` [Notation] (= `Zeta23.Iwin p.T`). -/
abbrev I : Set ℝ := Zeta23.Iwin p.T

end Setting

/-! ## The prime-power sum: notation of §5 for `Zeta23.PX` [eq:Pdef, §2.1] -/

/-- `a_n := Λ(n) n^{-1/2}` [Notation, §1.4]. -/
def acoef (n : ℕ) : ℝ := (Λ n : ℝ) / Real.sqrt n
/-- `y_n := log n` [Notation, §1.4]. -/
def ycoef (n : ℕ) : ℝ := Real.log n
/-- The index set "prime powers `n ≤ X`": all `0 < n ≤ ⌊X⌋` weighted by Λ (zero off prime powers);
spelled `Finset.Ioc 0 ⌊X⌋₊` as in Zeta23/Defs.lean's `PX` and Mathlib's `Chebyshev.psi`. -/
def primeRange (X : ℝ) : Finset ℕ := Finset.Ioc 0 ⌊X⌋₊

/-- `Zeta23.PX` in the `a_n, y_n` notation of §5: `P_X(τ) = −(1/π) Σ_{n≤X} a_n cos(τ y_n)`. -/
lemma PX_eq (X τ : ℝ) :
    Zeta23.PX X τ = -(1 / Real.pi) * ∑ n ∈ primeRange X, acoef n * Real.cos (τ * ycoef n) := rfl

/-! ## Abstract functional data

In the concrete instantiation `phiHat, Phi, Aphi, g, a, b` are Zeta23/Defs.lean's `P.phiHatR T`,
`P.PhiR T`, `P.Aphi T`, `P.g T`, `P.a T`, `P.b T` ([eq:phidef], [eq:abdef], [eq:PhigA]). -/

/-- The T-dependent taper data [eq:PhigA, eq:abdef] (abstract; see the bridge). -/
structure LocalFun where
  /-- `φ̂` restricted to ℝ (real-valued: φ is real and even) [§2.2]. -/
  phiHat : ℝ → ℝ
  /-- `Φ := (φ²)^` restricted to ℝ (real, even, entire) [eq:PhigA]. -/
  Phi : ℝ → ℝ
  /-- `A_φ := φ ⋆ φ`, `(v⋆v)(y) := ∫ v(u)v(u+y)du` [eq:PhigA]. -/
  Aphi : ℝ → ℝ
  /-- `g := φ² ⋆ φ²` [eq:PhigA]. -/
  g : ℝ → ℝ
  /-- `a := L⁻¹ ∫ φ²` [eq:abdef]. -/
  a : ℝ
  /-- `b := L⁻¹ ∫ φ⁴` [eq:abdef]. -/
  b : ℝ

variable (p : Setting) (F : LocalFun)

/-- The prime-side matrix entry (second expression in [eq:Gdef], §2.2):
`G_{kl} = ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ) dτ`, with `ν_X = Zeta23.nuX X` [eq:nudef] CONCRETE
(same shape as `Zeta23.Params.Gentry`, which is the case `F.phiHat := P.phiHatR T`). -/
def GentryA (k l : ℤ) : ℝ :=
  ∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * Zeta23.nuX p.X τ

/-- `G̃ := G/L` as a `d × d` real matrix, indices `0 ≤ k,l < d` [eq:Gdef]. -/
def GtildeA : Matrix (Fin p.d) (Fin p.d) ℝ :=
  fun k l => GentryA p F (k : ℤ) (l : ℤ) / p.L

/-- `tr G̃ = L⁻¹ Σ_{k<d} G_{kk}` [§5.2 "L tr G̃ = Σ_{k<d} G_kk"] (same shape as
`Zeta23.Params.trGtilde`: `L⁻¹ * Σ_{k : Fin d}`). -/
def trGtA : ℝ := (p.L)⁻¹ * ∑ k : Fin p.d, GentryA p F k k

/-- `tr G̃² = Σ_{k,l<d} G̃_{kl}² = L⁻² Σ_{k,l<d} G_{kl}²` [§5; eq:trG2int] (same shape as
`Zeta23.Params.trGtildeSq`). -/
def trGt2A : ℝ := (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryA p F k l ^ 2

/-! ## The seam: the bilinear form 𝓜[·,·]  [§5 "Evaluation of 𝓜", §5.4] -/

/-- `𝓜[u₁,u₂] := ∬_{I×I} Φ(τ−τ')² u₁(τ) u₂(τ') dτ dτ'`, `I = [T,2T]` (§5.4).
This literal spelling is shared between PrimeSideA.lean and PrimeSideB.lean. -/
def Mform (Φ : ℝ → ℝ) (T : ℝ) (u₁ u₂ : ℝ → ℝ) : ℝ :=
  ∫ q in (Set.Icc T (2 * T)) ×ˢ (Set.Icc T (2 * T)), (Φ (q.1 - q.2)) ^ 2 * u₁ q.1 * u₂ q.2

/-- `𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'` [lem:ends statement, §5.3]. -/
def MtotalA : ℝ := Mform F.Phi p.T (Zeta23.nuX p.X) (Zeta23.nuX p.X)

end PrimeSide
end Zeta23
