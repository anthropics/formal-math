/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Corollary31.Limit

/-!
# Corollary 40, "General τ": the choice of the parameters

Proof of Corollary 40: "Let 0 < τ < ε*, and fix ε with τ < ε < ε*.  By Corollary 31, with c and θ
chosen as in the proof of Theorem 24 for q := 1/2, there is, after absorbing the logarithmic
factors, a γ > 0 such that [...]".  Here this choice of c > 10 and of θ in (0, 0.9) is made for a
given τ (`exists_genParams`), together with a number γ ≤ 1 below the γ of Corollary 31, which leaves
room for the logarithmic factors.  What the three hinted problems use about the four numbers is the
structure `GenParams`.
-/

@[expose] public section

namespace ThreeSumApsp

/-- Numbers c, θ, ε to which Corollary 31 applies with D ≤ N^ε and whose q, the exponent of the
query time D^q in Corollary 31, is below 1/2; and a number 0 < γ ≤ 1 below the γ of Corollary 31 for
c and θ. -/
structure GenParams (c θ ε γ : ℝ) : Prop extends Admissible c θ ε where
  q_lt : qOf θ < 1 / 2
  γ_pos : 0 < γ
  γ_lt : γ < gammaOf c θ
  γ_le : γ ≤ 1

/-- ε is below ε*. -/
theorem GenParams.ε_lt_epsStar {c θ ε γ : ℝ} (p : GenParams c θ ε γ) : ε < epsStar :=
  p.thin.trans (sec4_Rc_lt_epsStar c _ p.c_gt (p.γ_pos.trans p.γ_lt).le)

/-- For τ < ε* there are numbers c, θ, ε, γ as in `GenParams` with τ < ε. -/
theorem exists_genParams {τ : ℝ} (h1 : τ < epsStar) : ∃ c θ ε γ : ℝ, GenParams c θ ε γ ∧ τ < ε := by
  obtain ⟨c, θ, hadm, hq⟩ :=
    exists_admissible (ε := (τ + epsStar) / 2) (q := 1 / 2) (by linarith) (by norm_num)
  have hg := hadm.gamma_pos
  exact ⟨c, θ, (τ + epsStar) / 2, min (gammaOf c θ / 2) 1,
    ⟨hadm, hq, lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩, by linarith⟩

/-- For τ₁ < ε* τ₂ there are numbers c, θ, ε, γ as in `GenParams` with τ₁ < ε τ₂ (proof of
Corollary 40: "τ₁ ≤ ετ₂ for some ε < ε*"). -/
theorem exists_genParams_mul {τ₁ τ₂ : ℝ} (h2 : 0 < τ₂) (h1 : τ₁ < epsStar * τ₂) :
    ∃ c θ ε γ : ℝ, GenParams c θ ε γ ∧ τ₁ < ε * τ₂ := by
  obtain ⟨c, θ, ε, γ, p, hτ⟩ := exists_genParams (τ := τ₁ / τ₂) ((div_lt_iff₀ h2).2 h1)
  exact ⟨c, θ, ε, γ, p, (div_lt_iff₀ h2).1 hτ⟩

end ThreeSumApsp
