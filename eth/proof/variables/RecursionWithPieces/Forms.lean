/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
import RecursionWithPieces.Main
import VariableBound.Paper.Forms
import VariableBound.Paper.Decide
import VariableBound.Paper.MainTheorem
import UniformInK.Top.Defs

/-! # Theorem D (b) and the joint bound of Theorem 1, Theorem D (b) and Corollary 11, through the function for Theorem 1 on the recursion of Appendix A with the pieces of Appendix B

This file holds two theorems. The step `together_of` to the paper's form, applied to
`SatM.targetUniform_all`, gives `togetherAllOccur`: one machine and one constant C satisfy the
bounds of Theorem 1, of Theorem D (b) and of Corollary 11
for formulas over x₀ … xₙ₋₁ that all occur. `thmVariablesB`, Theorem D (b), is read off from it.

Each of the two statements says that some machine exists and names none of the objects of
proof/variables/RecursionWithPieces. Their proofs go through `RecursionWithPieces.tiedAllCal`, of
which
`SatM.targetUniform_all` is a corollary; this is seen in the proofs, not in the statements. -/

public section

namespace RecursionWithPieces.Forms

open MainTheoremForms VariableBound.Paper RecursionWithPieces

/-- Through `RecursionWithPieces.tiedAllCal`: ONE machine and ONE constant C satisfy the bound of
Theorem 1, the bound of Theorem D (b) and the bound of Corollary 11, for formulas over x₀ … xₙ₋₁.
Names none of the objects of proof/variables/RecursionWithPieces. -/
theorem togetherAllOccur : TogetherAllOccur := together_of SatM.targetUniform_all

/-- Through `RecursionWithPieces.tiedAllCal`: Theorem D (b), the conclusion. Names none of the
objects of proof/variables/RecursionWithPieces. -/
theorem thmVariablesB : ThmVariablesB :=
  let ⟨M, C, hfin, _, h, _⟩ := togetherAllOccur
  ⟨M, C, hfin, h⟩

end RecursionWithPieces.Forms
