import Zeta23.ThmD.Sextuple.Base
import Zeta23.ThmD.Sextuple.A1285.Certificate
import Zeta23.ThmD.Sextuple.A1285.Assembly

/-! # Unconditional sextuple improvement at `A = 257 / 20000` -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace A1285

theorem zetaSextupleLedgerInterface :
    ZetaSextupleLedgerInterface (257 / 20000) B6 zetaSextuplePenalty
      ImprovedAssembly.A1285.zetaSextupleLedgerError :=
  ImprovedAssembly.A1285.zetaSextupleLedgerInterface_of_certificate
    Certificate.sextuple_affine

theorem zetaSextupleLedgerInterface_exactConstants :
    ZetaSextupleLedgerInterface (257 / 20000) (1094977 / 5000000000)
      zetaSextuplePenalty ImprovedAssembly.A1285.zetaSextupleLedgerError := by
  simpa only [B6] using zetaSextupleLedgerInterface

/-- Unconditional exact-constant dyadic sextuple improvement at `A = 257 / 20000`. -/
theorem thmD₀_sextuple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.A1285.sextupleLowerConstant - ε) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  ImprovedAssembly.A1285.sextupleDyadic_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional exact-constant cumulative sextuple improvement at `A = 257 / 20000`. -/
theorem thmD₀_sextuple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.A1285.sextupleLowerConstant - ε) *
          (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.A1285.sextupleCumulative_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end A1285
end Sextuple
end ThmD
end Zeta23

end
