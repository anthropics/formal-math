/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
public import VariableBound.Paper.Arith
import UniformInKStatement
import UniformInK.Top.Defs
import WidthK.Decode

/-! # The statements of `MainTheoremFormsStatement.lean` for formulas over x₀ … xₙ₋₁

**What is proved.** `together_of`: every proof of `SatM.TargetUniform` gives ONE Turing machine and
ONE constant C for `MainTheoremForms.TogetherAllOccur`, that is, the bound of Theorem 1 (k ≥ 1, m ≥
2, n ≥ 4, all variables occur), the bound of Theorem D (b)
(k ≥ 1, n ≥ 4, any number of clauses, variables need not occur) and the bound of Corollary 11, all
with log m and log n themselves and with no factor in front. Its steps are `mainTheoremFor_of` and
`thmVariablesBFor_of`; also
`corMinIsMainTheorem` (the bounds of Corollary 11 and of Theorem 1 are the same) and `clauseCount`
(a k-CNF on n variables has at most (2n+1)^k clauses).

**How.** No new mathematics. `together_of` keeps the machine of the given proof
(`UniformInKStatement.lean`: log₂(m+2), log₂(n+4), a factor C in front), its constant C becomes 3C,
and the rest is the
arithmetic of proof/variables/VariableBound/Paper/Arith.lean. -/

public section

namespace VariableBound.Paper

open MainTheoremForms Turing
open Sat3 (CNF)

/-! ### More time is allowed -/

/-- A machine that counts within t steps counts within t' ≥ t steps. -/
theorem countsWithin_mono {M : TM2ComputableAux Bool Bool} {k n : ℕ} {φ : CNF n} {t t' : ℕ} (h : CountsWithin M k φ t) (ht : t ≤ t') : CountsWithin M k φ t' := by
  obtain ⟨ev⟩ := h
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ht⟩⟩

/-! ### Counting -/

/-- After Corollary 11: «This is the Main Theorem.» For every machine and every constant the bound
of Corollary 11 and the bound of Theorem 1 are the same. -/
theorem corMinIsMainTheorem : CorMinIsMainTheoremStmt := by
  intro M C
  unfold CorMinFor MainTheoremFor
  simp only [timeCor_eq]

/-- From the bound in n of `UniformInKStatement.lean` with the constant C to the bound of Theorem D (b)
with the constant 3C, for the same machine. -/
theorem thmVariablesBFor_of {M : TM2ComputableAux Bool Bool} {C : ℕ} (h : SatM.CountsTMN M (SatM.boundNK (SatK.rN 1 (1 / 2)) C)) : ThmVariablesBFor M (3 * C) :=
  fun k n φ hk hn hφ => countsWithin_mono (h k n φ hk (by omega) hφ) (boundNK_le C hk hn)

/-- From the bound with the minimum of `UniformInKStatement.lean` (for k ≥ 1, n ≥ 1, all variables
occurring) with the constant C to the bound of Theorem 1 with the constant 3C, for the same machine. -/
theorem mainTheoremFor_of {M : TM2ComputableAux Bool Bool} {C : ℕ}
    (h : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → SatM.AllOccur φ →
      CountsWithin M k φ (SatM.boundBothK (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) C k n φ.length)) : MainTheoremFor M (3 * C) :=
  fun k n φ hk hφ hm hn hocc => countsWithin_mono (h k n φ hk (by omega) hφ hocc) (boundBothK_le C hk hm hn)

/-- Every proof of `SatM.TargetUniform` gives one machine and one constant for Theorem 1, Theorem D (b)
and Corollary 11 in the paper's wording. -/
theorem together_of (h : SatM.TargetUniform) : TogetherAllOccur := by
  obtain ⟨M, C, hfin, hN, -, hB⟩ := h
  have h2 : MainTheoremFor M (3 * C) := mainTheoremFor_of hB
  exact ⟨M, 3 * C, hfin, h2, thmVariablesBFor_of hN, (corMinIsMainTheorem M (3 * C)).2 h2⟩

/-- A k-CNF on n variables has at most (2n+1)^k clauses. -/
theorem clauseCount : ClauseCountStmt := fun _ _ _ h => Groundwork.DecodeK.IsKCNF.length_le h

end VariableBound.Paper
