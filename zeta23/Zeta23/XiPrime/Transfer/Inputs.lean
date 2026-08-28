/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.XiPrime.Statement
import Zeta23.XiPrime.PrimeSide.Density
import Zeta23.PrimeSideB.Concrete

noncomputable section

open Finset Filter RHLinalg MeasureTheory Real
open scoped BigOperators

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)

/-- Q_{kl}(e) := ∫ φ̂(τ−τ_k) φ̂(τ−τ_l) P_e(X; τ) dτ — the P-part Gram entry for an arbitrary coefficient
sequence e : ℕ → ℂ ([XF′ Lemma 6.1]: "Q^{(r)} = the PP-part of the paper's Gram matrix for
coefficients e_r").  ONE parenthesised product under the binder.  Equals
PrimeSide.GentryNu (XiPrime.Pc p.X e) p F k l at p = P.toSetting T, F = P.localFun T, by rfl
(QpEntry_eq_GentryNu below). -/
def QpEntry (e : ℕ → ℂ) (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, (P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * XiPrime.Pc (P.X T) e τ)

/-- the d×d matrix (Q_{kl}(e))_{0≤k,l<d} as a complex matrix (real entries), same typing as GpC. -/
def QpMat (e : ℕ → ℂ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.QpEntry T e (k : ℤ) (l : ℤ) : ℂ)

/-- δ_{kl} := ½ log(τ⋆_{kl}/T)  [XF′ Lemma 6.1]: L⋆^{kl} = L_T + δ_{kl}, δ_{kl} ∈ [0, ½ log 2]. -/
def deltaKL (k l : ℤ) : ℝ := Real.log (P.tauStar T k l / T) / 2

lemma QpEntry_eq_GentryNu (e : ℕ → ℂ) (k l : ℤ) :
    P.QpEntry T e k l
      = PrimeSide.GentryNu (XiPrime.Pc (P.toSetting T).X e) (P.toSetting T) (P.localFun T) k l := rfl

lemma GentryC_eq_GentryW (c : ℕ → ℂ) (k l : ℤ) :
    P.GentryC T c k l = XiPrime.GentryW 1 c (P.toSetting T) (P.localFun T) k l := rfl

end Params

namespace XiPrime
open PrimeSide

/-- **The re-expansion input** [XF′ §6], for
F = xiCoeffFamily with e T r N = e_r(N) = Σ_{j<Ω(N)} binom(−(j+1), r) L_T^{−(j+1)−r} [(Λ·log)∗Λ^{∗j}](N)
(supplied by theorem xiReexpansion).
Constants are T-uniform; the δ-range [0, 1/2] ⊇ [0, ½ log 2] ∋ δ_{kl}; sums over N ∈ Finset.Ioc 0 ⌊x⌋₊
(tree convention) for 2 ≤ x ≤ e^{l(T)} ⊇ the only point used downstream, x = X = e^{λl}.
BASE POINT: the expansion is about L_T = ½l + iπ/4 (XiPrime.LT), the ξ′ base —
so this is the right sentence for F = xiCoeffFamily (F.c T N = xiCoeff (LT T) N by rfl) and for nothing else; the
Z′ analogue (real base ½l, Defs.L2star) needs its own structure/consumer (the Z′ Gp1 differs too).  One should not
read 0 ≤ A into this structure: it is derivable from H3 but not carried. -/
structure Reexpansion (F : CoeffFamily) (e : ℝ → ℕ → ℕ → ℂ) (ρ₀ A T₀ : ℝ) : Prop where
  /-- C(N; L_T + δ) − c^{(T)}_N = Σ_{r≥1} e_r(N) δ^r  (absolutely convergent: |δ/L_T| < 1). -/
  expand : ∀ T : ℝ, T₀ ≤ T → ∀ δ : ℝ, δ ∈ Set.Icc (0:ℝ) (1 / 2) → ∀ N : ℕ,
    HasSum (fun r : ℕ => e T (r + 1) N * (δ : ℂ) ^ (r + 1)) (xiCoeff (LT T + δ) N - F.c T N)
  /-- e_r(1) = 0 (the N = 1 frequency does not oscillate; C(1; ·) ≡ 0). -/
  e_one : ∀ T : ℝ, ∀ r : ℕ, e T r 1 = 0
  /-- (H1)_r: Σ_{N≤x} |e_r(N)| N^{−1/2} ≤ A (ρ₀/l)^r √x · l. -/
  H1 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ / Real.sqrt N) ≤ A * (ρ₀ / l T) ^ r * Real.sqrt x * l T
  /-- (H2)_r: Σ_{N≤x} |e_r(N)|² ≤ A (ρ₀/l)^{2r} x l². -/
  H2 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ ^ 2) ≤ A * (ρ₀ / l T) ^ (2 * r) * x * l T ^ 2
  /-- (H3)_r: Σ_{N≤x} |e_r(N)|²/N ≤ A (ρ₀/l)^{2r} l² (1 + log x)   ([XF′ §6]: "≤ (c/l)^{2r} c l² L"). -/
  H3 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ ^ 2 / N) ≤ A * (ρ₀ / l T) ^ (2 * r) * l T ^ 2 * (1 + Real.log x)

/-- **The prop:PP upper bound for general coefficients** (frobSq_Ppart_le; [XF′ Lemma 6.1]):
"Σ_{kl} (Q_{kl})² is bounded by the paper's Prop. PP in its upper-bound form (diagonal +
Montgomery–Vaughan)", through lem_ends_nu for ν = P_e: main T·L·Σ|e|²/N (g ≤ L), then L·Σ|e|²,
the 𝒪₂ term L·S₁², and the r-INDEPENDENT end-effect term L·l·log l·(l + S₁)².  Over abstract taper
data; k,l-sums over Fin p.d (shape of PrimeSide.trGt2A); N-sums over Finset.Ioc 0 ⌊X⌋₊, literally
sumSqDivW / sumSqW / S1 (defeq).  The theorem:
frobSq_Ppart_le (hPP : PPInput) (hMV : MVHilbert C) (hC : 0 < C) (cϱ lam) (hlam : 0 < lam ∧ lam ≤ 1) : PPUpper cϱ lam
(Zeta23/XiPrime/PrimeSide/PPUpper.lean). -/
def PPUpper (cϱ lam : ℝ) : Prop :=
  ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (e : ℕ → ℂ), p.lam = lam → T₀ ≤ p.T →
    LocalHypsCore cϱ p F → e 1 = 0 →
    (∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Pc p.X e) p F k l ^ 2)
      ≤ C * p.L ^ 2 *
        (p.T * p.L * (∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖e N‖ ^ 2 / N)
          + p.L * (∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖e N‖ ^ 2)
          + p.L * S1 e p.X ^ 2
          + p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2)

end XiPrime
end Zeta23
