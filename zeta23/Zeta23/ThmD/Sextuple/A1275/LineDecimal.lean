import Zeta23.ThmD.Sextuple.A1275.Unconditional

/-!
# Fixed decimal headline for the `A = 51/4000` sextuple improvement

Public unconditional statements with the fixed rational constant `6727837118 / 10^10`.
The exact endpoint `(6·B_MT − 10π·B₆)/(6 − 51/4000) = 0.67278371…` exceeds it by the
exact positive margin `10067520896911983481 / 299362500000000000000000000000`
(`ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118`, from `HD_one_decimal.1`
and `Real.pi_lt_d20` only).
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace A1275

/-- Unconditional fixed `0.6727837118` dyadic headline. -/
theorem thmD₀_sextuple_6727837118 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727837118 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  ImprovedAssembly.A1275.sextupleDyadic_6727837118_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional fixed `0.6727837118` cumulative headline. -/
theorem thmD₀_sextuple_cumulative_6727837118 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727837118 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.A1275.sextupleCumulative_6727837118_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end A1275
end Sextuple
end ThmD
end Zeta23

end
