/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Commute
public import GeneralPieces.GenF.Normal
public import GeneralPieces.GenF.YMain
public import GeneralPieces.GenF.Assemble
public import GeneralPieces.Series.LemmaQ

/-! # Proof of Lemma 9, the close of the paragraph «Generating functions»: the expansion of f₊ and f₋

The paragraph "Generating functions" ends with the display on the two orders (`stTwoOrders`).
Comparing the coefficients of x^μ·x'^ν in it gives the expansion of f₊ and f₋ (`stExpansion`): the
left sides are f₊ and f₋
(`stY`), the coefficients of e^κ and e^κ' are numbers times powers of ε₊ and ε₋
(`coeff_expW_kap_false`, `coeff_expW_kap_true`), and the coefficients of ⟨𝒩⟩ lie in 𝓛 (`stN1`,
`stN2`, `stN3`). -/

public section

namespace GeneralPieces.GenF

/-- f₊ and f₋ are the same combination of powers of ε₊, or ε₋, times elements of 𝓛. -/
theorem stExpansion : GeneralPieces.Series.StExpansion := GeneralPieces.stExpansion_of stTwoOrders (stN1 stNeq) stN2 (stN3 stNeq) stY

end GeneralPieces.GenF

namespace GeneralPieces.Series

open ClauseBound.Boson Finset

variable {A : FA} {b : List ℕ}

end GeneralPieces.Series
