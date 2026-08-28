/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/
import Zeta23.LinAlg
import Zeta23.Defs

/-!
# Interfaces consumed by `Zeta23/Assembly.lean` from `ZeroSide.lean` (prop:block) and `Tail.lean` (prop:tail)
This small file exists so that `ZeroSide.lean` / `Tail.lean` can *prove*
`∀ᶠ T, BlockInputs Z P T` / `TailInputs Z P T (θ₀ T)` without importing all of `Assembly.lean`, and
`Main.lean`  can plug those proofs into `Assembly.thmA_abstract`.
Every field is a statement announced by the producing file; docstrings quote the paper labels.
-/

noncomputable section

open Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace Assembly

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- `N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)` (the paper prop:zeroside), as a natural number. -/
def NII : ℕ := Z.N (T - D0 T) T + Z.N (2 * T) (2 * T + D0 T)

/-- **Inputs from prop:block + [eq:Ncount] at height `T`** (the paper `prop:block`:
"(i) `n₊(Ã) ≤ s₁+s₂+p` and `rank(Ã) ≤ s₁+s₂+2p = #𝒵(I′)`.
 (ii) `Â = P+Q` with `P,Q` real symmetric, `P ⪰ 0`, `rank P ≤ s₁+s₂`, `tr P ≤ N_on(I′)`, and `n₊(Q) ≤ p`";
[eq:Ncount]: "`N(I′) ≥ s₁+2s₂+2p`" and "`N(I′) ≥ N_on(I′)+2p`"), produced by `ZeroSide.lean`.
Units: `Ã = P.tilde T (Z.Az P T)` [eq:AE], `Â = P.hat T (Z.Az P T)` [eq:hatunits].
`p` (number of off-line pairs in `𝒵(I′)`) is existentially quantified since only the displayed
inequalities involving it are consumed downstream. -/
structure BlockInputs : Prop where
  /-- prop:block(ii) in hat units + "`N_on(I′) + 2p ≤ N(I′)`" -/
  hat : ∃ (Pm Qm : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ) (p : ℕ)
      (_ : Pm.PosSemidef) (hQm : Qm.IsHermitian),
      P.hat T (Z.Az P T) = Pm + Qm ∧ Pm.rank ≤ Z.s1 T + Z.s2 T ∧
      rtrace Pm ≤ (Z.NonIprime T : ℝ) ∧ posIndex hQm ≤ p ∧
      (Z.NonIprime T : ℝ) + 2 * p ≤ Z.NIprime T
  /-- prop:block(i) in tilde units + "`N(I′) ≥ s₁ + 2s₂ + 2p`" [eq:Ncount] -/
  tilde : ∃ (p : ℕ) (hAt : (P.tilde T (Z.Az P T)).IsHermitian),
      posIndex hAt ≤ Z.s1 T + Z.s2 T + p ∧ (P.tilde T (Z.Az P T)).rank ≤ (Z.ZIprime T).ncard ∧
      (Z.s1 T : ℝ) + 2 * Z.s2 T + 2 * p ≤ Z.NIprime T

/-- **Inputs from prop:tail at height `T`** (the paper `prop:tail`: "`‖Ẽ‖ ≤ θ₀ := 4A₀C₁²X^{1/2}
log(4T)/D₀²` … Moreover the trace norm satisfies `‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L`"), produced by
`Tail.lean` with `B = traceNorm Ê`.  Units: `Ẽ = P.tilde T (Z.Ez P T)`, `Ê = P.hat T (Z.Ez P T)`. -/
structure TailInputs (θ₀ : ℝ) : Prop where
  theta_nonneg : 0 ≤ θ₀
  /-- lem:weyl's hypothesis: every eigenvalue of `Ẽ` is at most `θ₀` in absolute value
  (this is `‖Ẽ‖ ≤ θ₀` for the operator norm of a Hermitian matrix) -/
  tilde : ∃ hEt : (P.tilde T (Z.Ez P T)).IsHermitian, ∀ i, |hEt.eigenvalues i| ≤ θ₀
  /-- `|tr Ê| ≤ ‖Ê‖₁`, `‖Ê‖_F ≤ ‖Ê‖₁`, `‖Ê‖₁ ≤ θ₀/(aL)` -/
  hat : ∃ B : ℝ, 0 ≤ B ∧ |rtrace (P.hat T (Z.Ez P T))| ≤ B ∧
      frobSq (P.hat T (Z.Ez P T)) ≤ B ^ 2 ∧ B ≤ θ₀ / (P.a T * P.L T)

end Assembly
end Zeta23

end
