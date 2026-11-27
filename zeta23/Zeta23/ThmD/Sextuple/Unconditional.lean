/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Base
import Zeta23.ThmD.Sextuple.Certificate
import Zeta23.ThmD.Sextuple.Final
import Zeta23.ThmD.Sextuple.Ledger

/-!
# Unconditional sextuple improvement

The kernel-checked concrete certificate `Certificate.sextuple_affine` instantiates
the zeta sextuple ledger interface; combined with the unconditional base interface
this yields the exact-constant dyadic and cumulative improvements.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple

/-- Concrete geometric/certificate ledger for the zeta sextuple argument. -/
theorem zetaSextupleLedgerInterface :
    ZetaSextupleLedgerInterface A6 B6 zetaSextuplePenalty
      zetaSextupleLedgerError :=
  zetaSextupleLedgerInterface_of_certificate
    Certificate.sextuple_affine

/-- The same concrete ledger with the rational constants unfolded for `Final`. -/
theorem zetaSextupleLedgerInterface_exactConstants :
    ZetaSextupleLedgerInterface
      (1 / 80) (1094977 / 5000000000)
      zetaSextuplePenalty zetaSextupleLedgerError := by
  simpa only [A6, B6] using zetaSextupleLedgerInterface

/-- Unconditional exact-constant dyadic sextuple improvement. -/
theorem thmD₀_sextuple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  thmD₀_sextuple_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional exact-constant cumulative sextuple improvement. -/
theorem thmD₀_sextuple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T :=
  thmD₀_sextuple_cumulative_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end Sextuple
end ThmD
end Zeta23

end
