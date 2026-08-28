/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFJTermW.lean — the W correction functional JcorrW c k on the line Re s = c, 1 < c ≤ 5/4, as the
W INSTANCE of the generic J-term theorem ExplicitFormula/JTerm.JcorrG_estimate.
[XF′ Thm 9.2 (b)–(e)]: E ↦ E₂, freezing parameter the REAL number L_{2⋆}(τ⋆) (so the mirrored weight freezes to the SAME
Dirichlet object — (G1) is vacuous).  Inputs: E2LineFacts c (EFLitCorrW) and FreezeFactsW c (below; corresponding to
EFExpansion X5, X6, X7-conj).  JcorrW_estimate is consumed by Hardy/EFMain.
-/
import Zeta23.XiPrime.Hardy.EFLitCorrW
import Zeta23.XiPrime.ExplicitFormula.JTerm

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn)

/-- The frozen Dirichlet object on the line c with real parameter L_{2⋆}(τ):
D_c(τ; t) := B(c+it)/(L2star τ − A(c+it))  (= DfroG c (L2star τ)). -/
def DfroC (c τ : ℝ) (t : ℝ) : ℂ :=
  Bfn ((c:ℂ) + t * I) / (((L2star τ : ℝ) : ℂ) - Afn ((c:ℂ) + t * I))

theorem DfroC_eq (c τ : ℝ) : DfroC c τ = DfroG c ((L2star τ : ℝ) : ℂ) := rfl

/-- The freezing facts for E₂ on the line c. -/
structure FreezeFactsW (c : ℝ) : Prop where
  freeze : ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ → T / 4 ≤ t →
      ‖dE2 c t - DfroC c τ t‖ ≤ C * (|t - τ| + 1) / (T * Real.log T)
  unif : ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ →
      ‖DfroC c τ t‖ ≤ C / Real.log T
  conj_symm : ∀ t : ℝ, t ≠ 0 → conj (dE2 c (-t)) = dE2 c t

/-- **the W J-term estimate** — instance of JcorrG_estimate at (c, dE2 c, τ ↦ (L2star τ : ℂ)). -/
theorem JcorrW_estimate {c : ℝ} (_hc1 : 1 < c) (_hc2 : c ≤ 5/4) (hE2 : E2LineFacts c) (hF : FreezeFactsW c) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ 8 ≤ T₀ ∧
    ∀ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
      {T a b W W' : ℝ} (hT : T₀ ≤ T) (ha : T ≤ a) (hb : T ≤ b) (hW : 0 ≤ W) (hW' : 0 ≤ W')
      (hw1 : ∀ t : ℝ, ‖Hfn k ((c:ℂ) + t * I)‖ ≤ W * (cauchyK a t * cauchyK b t))
      (hw2 : ∀ t : ℝ, (|t - a| + |t - b|) * ‖Hfn k ((c:ℂ) + t * I)‖ ≤ W' * (cauchyK a t * cauchyK b t))
      (hw1' : ∀ t : ℝ, ‖Hfn k (1 - (c:ℂ) - t * I)‖ ≤ W * (cauchyK (-a) t * cauchyK (-b) t))
      (hw2' : ∀ t : ℝ, (|t + a| + |t + b|) * ‖Hfn k (1 - (c:ℂ) - t * I)‖ ≤ W' * (cauchyK (-a) t * cauchyK (-b) t))
      {cJ : ℕ → ℂ} (hcs : Summable (fun N : ℕ => ‖cJ N‖ * (N : ℝ) ^ (-c)))
      (hC1 : ∀ t : ℝ, LSeries cJ ((c:ℂ) + t * I) = DfroC c ((a + b) / 2) t)
      (hC1' : ∀ t : ℝ, LSeries (fun N => conj (cJ N)) ((c:ℂ) + t * I) = DfroC c ((a + b) / 2) t),
      ‖JcorrW c k - ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N))
          + ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N))‖
        ≤ K * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2) := by
  obtain ⟨K, T₀, hK, hT₀, h⟩ := JcorrG_estimate (c := c) (dE := dE2 c) (Lpar := fun τ => ((L2star τ : ℝ) : ℂ))
    hE2.cont hE2.bound hF.conj_symm hF.freeze hF.unif
  refine ⟨K, T₀, hK, hT₀, ?_⟩
  intro k hk hkc T a b W W' hT ha hb hW hW' hw1 hw2 hw1' hw2' cJ hcs hC1 hC1'
  have hC1'' : ∀ t : ℝ, LSeries (fun N => conj (cJ N)) ((c:ℂ) + t * I)
      = DfroG c (conj (((L2star ((a + b) / 2) : ℝ) : ℂ))) t := fun t => by
    rw [Complex.conj_ofReal]; exact hC1' t
  exact h hk hkc hT ha hb hW hW' hw1 hw2 hw1' hw2' hcs hC1 hC1''

end XiPrime
end Zeta23
