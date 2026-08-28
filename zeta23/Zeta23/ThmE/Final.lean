/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Final.lean — **Theorem E**.

The four target statements of Zeta23/ThmE/Statement.lean, proved here as theorems (same names,
same signatures — placed downstream so they can consume SeamL, GzGpChi, RvMChi, TracesChi and
EFLitChi/MainChi), plus the zero-hypothesis headlines thmE_A₀/thmE_B₀/thmE_C₀ for
Mathlib's DirichletCharacter.LFunction: nothing is assumed (the χ-explicit formula is the
theorem EF_lit_chi_L; every other input is proved elsewhere in the repository).

Faithfulness caveat: EF_lit_chi's statement is a transcription of [IK04, Thm 5.12] for L(s,χ),
which is not displayed in the paper; the Lean proofs are unconditional regardless.
-/
import Zeta23.ThmE.Main
import Zeta23.ThmE.MainChi

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Theorem E, first bound, at fixed λ ∈ (0,1)** [thm:E]. -/
theorem thmE_A_lam (hs : LSeam χ) (hprim : χ.IsPrimitive) (hq : 1 < q)
    (H : PaperInputsChi (parity χ) q (coeff χ) (LZeros hs))
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmE_A_lam_of_traces hs (by omega) taperProfile_stdProfile h0 h1 H.RvM
    (thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim) H
      (PrimeSide.localHypsEventually hP))
    (eventually_GzGpChi _ hP H.EF)
    (Assembly.calE_tendsto_zero _ hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w))

/-- **Theorem E, first bound** [thm:E]. -/
theorem thmE_A (hs : LSeam χ) (hprim : χ.IsPrimitive) (hq : 1 < q)
    (H : PaperInputsChi (parity χ) q (coeff χ) (LZeros hs)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  Assembly.eps_form_twoThirds (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (N0starL χ T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun lam hl1 hl2 => thmE_A_lam hs hprim hq H (by linarith) hl2)

/-- **Theorem E, second bound** [thm:E]. -/
theorem thmE_B (hs : LSeam χ) (hprim : χ.IsPrimitive) (hq : 1 < q)
    (H : PaperInputsChi (parity χ) q (coeff χ) (LZeros hs)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 / 2 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  refine Assembly.eps_form_half (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (N0simpleL χ T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _) ?_
  intro lam hl1 hl2
  have hP := paramsOf_valid taperProfile_stdProfile (show (0:ℝ) < lam by linarith) hl2.le
  exact thmE_B_lam_of_traces hs (by omega) taperProfile_stdProfile (by linarith) hl2 H.RvM
    (thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim) H
      (PrimeSide.localHypsEventually hP))
    (eventually_GzGpChi _ hP H.EF)
    (Assembly.calE_tendsto_zero _ hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w))

/-- **Theorem E, third bound** [thm:E]. -/
theorem thmE_C (hs : LSeam χ) (hprim : χ.IsPrimitive) (hq : 1 < q)
    (H : PaperInputsChi (parity χ) q (coeff χ) (LZeros hs)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  refine Assembly.eps_form_threeQuarters (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (NdistL χ T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _) ?_
  intro lam hl1 hl2
  have hP := paramsOf_valid taperProfile_stdProfile (show (0:ℝ) < lam by linarith) hl2.le
  exact thmE_C_lam_of_traces hs (by omega) taperProfile_stdProfile (by linarith) hl2 H.RvM
    (thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim) H
      (PrimeSide.localHypsEventually hP))
    (eventually_GzGpChi _ hP H.EF)
    (Assembly.calE_tendsto_zero _ hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w))

/-! ## Zero hypotheses -/

/-- the full input package, from theorems alone. -/
theorem paperInputsChi_L (hq : 1 < q) (hprim : χ.IsPrimitive) :
    PaperInputsChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)) :=
  PaperInputsChi.of_EF hq hprim
    (explicitFormulaPaperChi_of_lit (EF_lit_chi_L hq hprim)
      (GammaChi.gammaFactsChi parity_le_one (by omega)) (by omega)
      (coeffUnimodular_of_primitive hq hprim).toCoeffOK)

/-- **Theorem E, bound 1, no hypotheses**: for every primitive Dirichlet character mod q > 1,
at least (2/3 − ε)·N_χ(T,2T) of the zeros of Mathlib's `DirichletCharacter.LFunction χ` with
ordinate in (T,2T], counted with multiplicity, are matched by distinct critical-line zeros. -/
theorem thmE_A₀ (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  thmE_A (LSeam_of hq hprim) hprim hq (paperInputsChi_L hq hprim)

/-- **Theorem E, bound 2, no hypotheses** (1/2 simple-and-on-line). -/
theorem thmE_B₀ (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 / 2 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  thmE_B (LSeam_of hq hprim) hprim hq (paperInputsChi_L hq hprim)

/-- **Theorem E, bound 3, no hypotheses** (3/4 distinct). -/
theorem thmE_C₀ (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  thmE_C (LSeam_of hq hprim) hprim hq (paperInputsChi_L hq hprim)

end ThmE
end Zeta23
