import Zeta23.ThmD.Sextuple.Base
import Zeta23.ThmD.Sextuple.A1275.Certificate
import Zeta23.ThmD.Sextuple.A1275.Assembly

/-!
# Unconditional sextuple improvement at `A = 51/4000`

The kernel-checked concrete certificate `A1275.Certificate.sextuple_affine` instantiates
the conditional ledger adapter of `A1275.Assembly`; combined with the unconditional base
interface this yields the exact-constant dyadic and cumulative improvements
`liminf N₀ˢ/N ≥ (6·B_MT − 10π·B₆)/(6 − 51/4000)`.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace A1275

/-- Concrete geometric/certificate ledger for the zeta sextuple argument at `A = 51/4000`. -/
theorem zetaSextupleLedgerInterface :
    ZetaSextupleLedgerInterface (51 / 4000) B6 zetaSextuplePenalty
      ImprovedAssembly.A1275.zetaSextupleLedgerError :=
  ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate
    Certificate.sextuple_affine

/-- The same concrete ledger with the rational constants unfolded for `Final`. -/
theorem zetaSextupleLedgerInterface_exactConstants :
    ZetaSextupleLedgerInterface (51 / 4000) (1094977 / 5000000000)
      zetaSextuplePenalty ImprovedAssembly.A1275.zetaSextupleLedgerError := by
  simpa only [B6] using zetaSextupleLedgerInterface

/-- Unconditional exact-constant dyadic sextuple improvement at `A = 51/4000`. -/
theorem thmD₀_sextuple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.A1275.sextupleLowerConstant - ε) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  ImprovedAssembly.A1275.sextupleDyadic_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional exact-constant cumulative sextuple improvement at `A = 51/4000`. -/
theorem thmD₀_sextuple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.A1275.sextupleLowerConstant - ε) *
          (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.A1275.sextupleCumulative_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end A1275
end Sextuple
end ThmD
end Zeta23

end
