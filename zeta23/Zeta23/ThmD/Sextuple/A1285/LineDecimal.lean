import Zeta23.ThmD.Sextuple.A1285.Unconditional

/-! # Fixed decimal headline `6727949489/10^10` for the `A = 257 / 20000` sextuple improvement -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace A1285

/-- Unconditional fixed `0.6727949489` dyadic headline. -/
theorem thmD₀_sextuple_6727949489 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727949489 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  ImprovedAssembly.A1285.sextupleDyadic_6727949489_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional fixed `0.6727949489` cumulative headline. -/
theorem thmD₀_sextuple_cumulative_6727949489 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727949489 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.A1285.sextupleCumulative_6727949489_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end A1285
end Sextuple
end ThmD
end Zeta23

end
