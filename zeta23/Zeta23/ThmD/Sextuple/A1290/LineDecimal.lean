import Zeta23.ThmD.Sextuple.A1290.Unconditional

/-! # Fixed decimal headline `6728005676/10^10` for the `A = 129 / 10000` sextuple improvement -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace A1290

/-- Unconditional fixed `0.6728005676` dyadic headline. -/
theorem thmD₀_sextuple_6728005676 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6728005676 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  ImprovedAssembly.A1290.sextupleDyadic_6728005676_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional fixed `0.6728005676` cumulative headline. -/
theorem thmD₀_sextuple_cumulative_6728005676 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6728005676 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.A1290.sextupleCumulative_6728005676_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end A1290
end Sextuple
end ThmD
end Zeta23

end
