/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/StatementW.lean — the interface for the Z′ (Hardy W) development.

Statement.lean §6 fixes the W objects and counts (Defs.hardyW, IsWZero, wMult,
NcountW/NdistW/N0simpleW; WZerosInStrip, WSeam, wZeros + seam lemmas, HeadlineW) and Final.lean proves
HeadlineW 0.85838 0.92919.  This file adds (i) the W explicit-formula
main term and Prop (pole weight 2, real fixed parameter) and (ii) the exact target statements for the W seam /
W-RvM / W-transfer results.  As in Statement.lean: definitions and named Props only.

  §W1  the entry-dependent W main term  M^𝒵_{kl} = ∫ φ̂(τ−τ_k)φ̂(τ−τ_l)[μ + 2·Π_X + P¹_X(τ; L_{2⋆}^{kl})]dτ
       (Params.GentryW1 / GpW1; the weight-ϖ fixed-coefficient matrix is Params.GpCW) — coefficients
       C(N; L_{2⋆}), L_{2⋆} = ½log(τ⋆/2π) real (Defs.L2star), pole weight 2 (Defs.nucW 2 = nucZ).
  §W2  WEF Z Pf            — [XF′ Thm 9.2] entrywise, same error shape as XiEF (a named Prop; proved in
       XiPrime/Hardy/EFFinal.lean).
  §W3  targets (documentation + Prop abbreviations):
         wSeam_of_strip    : 0 < t₀ → WZerosInStrip t₀ → WSeam t₀
         WRvM hZ hs        := RiemannVonMangoldt (wZeros hZ hs)  [XF′ (Z7)]
         XiTraceTransfer (wZeros hZ hs) Pf wCoeffFamily  from WEF + PPUpper + Π-part o(N)
         wCoeffFamily.Hyps                                       (proved: wCoeffFamily_hyps, Coeff.lean)
       and how Final.hardyW_simple_on_line_flat consumes them.
-/
import Zeta23.XiPrime.Statement

open scoped BigOperators
open Complex MeasureTheory Set Filter RHLinalg

noncomputable section

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)

/-- **M^𝒵_{kl}** [XF′ Thm 9.2]: the ENTRY-DEPENDENT W main term
∫ φ̂(τ−τ_k) φ̂(τ−τ_l) [μ(τ) + 2·Π_X(τ) + P¹_X(τ; L_{2⋆}^{kl})] dτ  with the coefficients C(N; L_{2⋆}) frozen at the
REAL parameter L_{2⋆} = L2star(τ⋆_{kl}) = ½ log(τ⋆/2π) (no iπ/4 phase: [XF′ §9.3(ii)]) and POLE WEIGHT 2 (the ½
from shifting L₂ past s = 1 plus 3/2 from the poles of F_𝒵 = L₂ + W′/W at s = 0, 1: [XF′ Prop 9.1, Thm 9.2(a)]).
Built from Defs.GentryCW (one parenthesised integrand), so it shares every lemma about GentryCW. -/
def GentryW1 (k l : ℤ) : ℝ :=
  P.GentryCW T 2 (XiPrime.xiCoeff ((XiPrime.L2star (P.tauStar T k l) : ℝ) : ℂ)) k l

/-- the d×d matrix of W main terms, typed like P.Gp / P.Gp1. -/
def GpW1 : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.GentryW1 T (k : ℤ) (l : ℤ) : ℂ)

/- The fixed-coefficient, pole-weight-ϖ prime-side matrix (M^{c,ϖ}_{kl})_{k,l<d} is `Zeta23.Params.GpCW`
(Zeta23/XiPrime/PrimeSide/Moments.lean; GpC_eq_GpCW : GpC = GpCW 1, by rfl).  The W-transfer compares Ĝ^𝒵 with
GpCW 2 (F.c T) and then drops to GpC (F.c T) (ϖ = 1, the matrix in XiTraceTransfer / CoeffMoments) at o(N) cost in
both traces. -/

end Params

namespace XiPrime

/-! ## §W2. The W explicit formula  [XF′ Thm 9.2] -/

/-- **WEF — the explicit formula for W = ζ′ + L₂ζ, entrywise, frozen coefficients, pole weight 2**
[XF′ Prop 9.1 + Thm 9.2] (pattern = XiEF with F = (ξ′)′/ξ′ ↦ F_𝒵 := L₂ + W′/W,
L ↦ L₂, L⋆ ↦ L_{2⋆} real).  For all large T and all 0 ≤ k,l < d: the zero-side Gram entry of the configuration Z
(instantiated at wZeros hZ hs: ALL zeros of W with |Im| ≥ t₀, with multiplicity — the poles of W and the finitely
many low zeros E₀ with |Im| < t₀ are NOT in Z; E₀'s residues, ≪ X^{1/2}T⁻⁶ by [XF′ Prop 9.1], and the polar terms
are inside the error) equals M^𝒵_{kl} = (Pf T).GentryW1 T k l up to
|𝓔| ≤ C·T^{−δ}·(1/max(1, (τ_k−τ_l)²) + 1/T) for some δ > 0 — exactly XiEF's error shape (contour on the fixed line
Re s = 5/4, power saving only; the "+1/T" floor; 1/max 1 Δ² for min(1,Δ⁻²)), with the Summable conjunct (R2). -/
def WEF (Z : ZeroConfig) (Pf : ℝ → Params) : Prop :=
  ∃ C δ T₀ : ℝ, 0 < δ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ k l : Fin ((Pf T).d T),
    Summable (fun ρ : Z.carrier => Z.Gsummand (Pf T) T k l ρ) ∧
    ‖Z.Gz (Pf T) T k l - ((Pf T).GentryW1 T k l : ℂ)‖
      ≤ C * T ^ (-δ) * (1 / max 1 (((Pf T).tau T k - (Pf T).tau T l) ^ 2) + 1 / T)

/-! ## §W3. The W inputs of the Z′ headline

  • W-seam      wSeam_of_strip {t₀ : ℝ} (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) : WSeam t₀
                (W analytic off ℝ and ≢ 0 ⇒ one_le_mult via analyticOrderAt;
                [XF′ (Z2)] W(s) = −χ(s)W(1−s), conj W(conj s) = W(s) ⇒ reflect_zero / mult_reflect at the
                analyticOrderAt level (χ ≠ 0, ∞ off ℝ); finite_window from hZ (bounded strip) + isolated zeros).
  • W-RvM       RiemannVonMangoldt (wZeros hZ hs)   [XF′ (Z7): N_W(T) = N(T) + O(log T), local
                count ≪ log t — argument principle for F_𝒵 on Re s = 2 where Re(L₂ − A) > 0, Jensen;
                with Y := ξ′/Γℝ ↦ W and the two real poles 0, 1 excised by t₀ > 0].
  • W-EF        WEF (wZeros hZ hs) Pf.
  • W-transfer  WEF (wZeros hZ hs) Pf → … → XiTraceTransfer (wZeros hZ hs) Pf wCoeffFamily
                — xiTraceTransfer_of with XiEF ↦ WEF plus ONE extra step: M^𝒵 has pole weight 2
                and the comparison matrix GpC (wCoeffFamily.c T) has weight 1; the difference is the Π-part
                matrix (∫ φ̂φ̂ Π_X)_{kl}, whose hat-trace is ≪ d·L·√X/(T·aL²) ≍ √X = o(N) and whose hat-Frobenius
                norm is ≪ d·√X/(T·L) ≍ √X = o(√N) ([XF′ §9.3(i)]: |Π_X(τ)| ≤ 3√X/(1+|τ|)),
                then ‖A+B‖_F² ≤ (1+η)‖A‖_F² + (1+1/η)‖B‖_F².  The coefficient re-expansion input is the
                Reexpansion for the REAL parameter family L_{2⋆}(τ⋆) vs L2star-at-T = ½ l (no phase).
  • (Z6)(iii)   WZerosInStrip t₀ is a named Prop (Littlewood's gap theorem + de la Vallée Poussin), like (F2) for ξ′.
  • wCoeffFamily.Hyps.    -/

/-- **(Z7)** H-RvM + local count for the zeros of W at heights ≥ t₀, as the tree's structure. -/
def WRvM {t₀ : ℝ} (hZ : WZerosInStrip t₀) (hs : WSeam t₀) : Prop := RiemannVonMangoldt (wZeros hZ hs)

end XiPrime
end Zeta23

end
