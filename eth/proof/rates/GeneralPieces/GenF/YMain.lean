/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Y
public import GeneralPieces.GenF.Y2
public import GeneralPieces.GenF.YY

/-! # Lemma 9 (Appendix B), on the operators Q_s: f₊ = ⟨Y(a, ω₁)·Y(b, ω₂)⟩ as a coefficient of ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩

The expansions e^{B⁺}e^{B⁻} = Σ_ν x'^ν·Y(t^ν, ω₂)/ν! and e^{A⁺}e^{A⁻} = Σ_μ x^μ·Y(t^μ, ω₁)/μ! are
put into the form of the interface statements `StY1`, `StY1'`, `StOp0`, `StY2` and `StXo`, and
composed by `stY_of`. -/

public section

namespace GeneralPieces.GenF

theorem stY1 : StY1 := fun rd b hb τ σ' => Y1 rd b hb τ σ'

theorem stY1' : StY1' := fun rd n σ' => pderiv_xi_outer rd n σ'

theorem stOp0 : StOp0 := fun b r _ _ h h' => op_eq_zero_of_zero_mem b r h h'

theorem stY2 : StY2 := fun rd E a σ ha hE => ⟨y0 a σ, y0_monomial a σ, fun w hw => Y2 rd E a ha σ w hE hw⟩

theorem stXo : StXo := fun rd E σ b w => pdL_GG_xo rd E σ b w

/-- μ!·ν! times the coefficient of x^μ·x'^ν in ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩ is f₊ = ⟨Y(a, ω₁)·Y(b,
ω₂)⟩. -/
theorem stY : StY := stY_of stY1 stY1' stOp0 stY2 stXo

end GeneralPieces.GenF
