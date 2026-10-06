import Zeta23.ThmD.Sextuple.Base
import Zeta23.ThmD.Sextuple.A1290.Certificate
import Zeta23.ThmD.Sextuple.A1290.Assembly

/-! # Unconditional sextuple improvement at `A = 129 / 10000` -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace A1290

theorem zetaSextupleLedgerInterface :
    ZetaSextupleLedgerInterface (129 / 10000) B6 zetaSextuplePenalty
      ImprovedAssembly.A1290.zetaSextupleLedgerError :=
  ImprovedAssembly.A1290.zetaSextupleLedgerInterface_of_certificate
    Certificate.sextuple_affine

theorem zetaSextupleLedgerInterface_exactConstants :
    ZetaSextupleLedgerInterface (129 / 10000) (1094977 / 5000000000)
      zetaSextuplePenalty ImprovedAssembly.A1290.zetaSextupleLedgerError := by
  simpa only [B6] using zetaSextupleLedgerInterface

/-- Unconditional exact-constant dyadic sextuple improvement at `A = 129 / 10000`. -/
theorem thmD₀_sextuple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.A1290.sextupleLowerConstant - ε) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  ImprovedAssembly.A1290.sextupleDyadic_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional exact-constant cumulative sextuple improvement at `A = 129 / 10000`. -/
theorem thmD₀_sextuple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.A1290.sextupleLowerConstant - ε) *
          (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.A1290.sextupleCumulative_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end A1290
end Sextuple
end ThmD
end Zeta23

end
