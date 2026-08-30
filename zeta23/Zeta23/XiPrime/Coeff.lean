/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff.lean — the ξ′ coefficient development, assembled.

The two coefficient families of [XF′]:
  theorem xiCoeffFamily_hyps : xiCoeffFamily.Hyps      (b_N = C(N; L_T), L_T = l/2 + iπ/4  — ξ′)
  theorem wCoeffFamily_hyps  : wCoeffFamily.Hyps       (b_N = C(N; l/2)                    — Z′)
from
  Coeff/Basic      pointwise algebra of C(N;Λ⋆), majorant ‖C‖ ≤ Λ + log·F;
  Coeff/Abel       Mertens/Abel step (the one analytic input: Cheb.mertensFirst);
  Coeff/PowerSums  Σ_{N≤e^u}Λ^{∗m}(N)/N ≤ (u+mK)^m/m!;
  Coeff/Upper      S(u) ≤ C(1+u)²  ⇒ (H1), (H2);
  Coeff/DiagLaw    (H3): S(y) = l²∫₀^{y/l}D₁ + o(l²)   [XF′ Lemma 7.1]  (uses Coeff/NonSquarefree, Coeff/MainTerm);
  Certificate/D1   continuity / nonnegativity / truncation of D₁.
  Also here: Coeff/LSeries (L(C_J,s) = B/(Λ⋆−A), for the explicit-formula modules).
-/
import Zeta23.XiPrime.Statement
import Zeta23.XiPrime.Coeff.Upper
import Zeta23.XiPrime.Coeff.H3
import Zeta23.XiPrime.Coeff.LSeries
import Zeta23.XiPrime.Coeff.LT
import Zeta23.XiPrime.Certificate.D1

open scoped BigOperators ArithmeticFunction
open Complex

noncomputable section

namespace Zeta23
namespace XiPrime

/-- ‖(l/2 : ℂ)‖ ≥ l/2. -/
lemma norm_real_half_l_ge (T : ℝ) : l T / 2 ≤ ‖(((l T / 2 : ℝ)) : ℂ)‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _

/-- **[XF′ Lemma 7.1 + Remark 7.2] for the ξ′ family b_N = C(N; L_T).** -/
theorem xiCoeffFamily_hyps : xiCoeffFamily.Hyps where
  c_one := fun _ => xiCoeff_one _
  H1 := coeff_H1 (fun T => LT T) (fun T _ => norm_LT_ge T)
  H2 := coeff_H2 (fun T => LT T) (fun T _ => norm_LT_ge T)
  H3 := coeff_H3 (fun T => LT T) (fun T => re_LT T) (fun T => abs_im_LT_le T)
  D_cont := continuous_D1
  D_nonneg := fun _ hs => D1_nonneg hs.1

/-- **the same for the Z′ family b_N = C(N; l/2) (real parameter).** -/
theorem wCoeffFamily_hyps : wCoeffFamily.Hyps where
  c_one := fun _ => xiCoeff_one _
  H1 := coeff_H1 (fun T => ((l T / 2 : ℝ) : ℂ)) (fun T _ => norm_real_half_l_ge T)
  H2 := coeff_H2 (fun T => ((l T / 2 : ℝ) : ℂ)) (fun T _ => norm_real_half_l_ge T)
  H3 := coeff_H3 (fun T => ((l T / 2 : ℝ) : ℂ)) (fun T => by simp) (fun T => by simp)
  D_cont := continuous_D1
  D_nonneg := fun _ hs => D1_nonneg hs.1

end XiPrime
end Zeta23
