/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Zeta23.ThmD.LineDecimal
import Zeta23.ThmD.Sextuple.Feedback

/-!
# Final abstract assembly for the sextuple improvement

The theorems in this file specialize the scalar feedback ledger to the zeta
counts.  They remain conditional only on the two named interfaces from
`Feedback.lean`: the strengthened Montgomery--Taylor bound retaining its
spectral penalty, and the sextuple pinching/span lower bound for that penalty.
The numerical sextuple certificate is deliberately not imported here.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple

/-- Zeta specialization of the strengthened Montgomery--Taylor base interface. -/
abbrev ZetaBasePenaltyInterface (penalty baseError : ℝ → ℝ) : Prop :=
  BasePenaltyInterface (HD 1)
    (fun T => (Ncount T (2 * T) : ℝ))
    (fun T => (N0simple T (2 * T) : ℝ)) penalty baseError

/-- Zeta specialization of the sextuple certificate and span-ledger interface. -/
abbrev ZetaSextupleLedgerInterface (A B : ℝ)
    (penalty ledgerError : ℝ → ℝ) : Prop :=
  SextupleLedgerInterface A B
    (fun T => (Ncount T (2 * T) : ℝ))
    (fun T => (N0simple T (2 * T) : ℝ)) penalty ledgerError

/-- Dyadic zeta epsilon form obtained by connecting the two abstract interfaces. -/
theorem sextuple_zeta_dyadic_of_interfaces
    {A B : ℝ} {penalty baseError ledgerError : ℝ → ℝ}
    (hA : A < 6)
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface A B penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (feedbackConstant (HD 1) A B - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  sextuple_feedback_eps hA (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    hbase hledger

/-- Cumulative zeta epsilon form, using interval additivity and the existing
Riemann--von Mangoldt dyadic wrapper. -/
theorem sextuple_zeta_cumulative_of_interfaces
    {A B : ℝ} {penalty baseError ledgerError : ℝ → ℝ}
    (hA : A < 6)
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface A B penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (feedbackConstant (HD 1) A B - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => N0simple_add' zetaSeam)
    (sextuple_zeta_dyadic_of_interfaces hA hbase hledger)

/-- The exact feedback endpoint for the certified rational sextuple constants
`A = 1/80` and `B = 1094977/5000000000`. -/
def sextupleLowerConstant : ℝ :=
  feedbackConstant (HD 1) (1 / 80) (1094977 / 5000000000)

/-- Kernel-checked strict comparison with the printed `0.6727556` headline.
It combines the existing rational enclosure of `HD 1` with Mathlib's certified
20-decimal upper bound for `π`; no floating-point evaluation is used. -/
theorem sextupleLowerConstant_gt_6727556 :
    (6727556 / 10 ^ 7 : ℝ) < sextupleLowerConstant := by
  rw [sextupleLowerConstant, feedbackConstant]
  have hBMT := HD_one_decimal.1
  have hpi := Real.pi_lt_d20
  have hden : (0 : ℝ) < 6 - 1 / 80 := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num at hBMT hpi ⊢
  linarith

/-- Exact-constant dyadic assembly for the certified rational sextuple inputs. -/
theorem thmD₀_sextuple_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (1 / 80) (1094977 / 5000000000) penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_dyadic_of_interfaces (A := (1 / 80 : ℝ))
      (B := (1094977 / 5000000000 : ℝ)) (by norm_num) hbase hledger)

/-- Exact-constant cumulative assembly for the certified rational sextuple inputs. -/
theorem thmD₀_sextuple_cumulative_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (1 / 80) (1094977 / 5000000000) penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_cumulative_of_interfaces (A := (1 / 80 : ℝ))
      (B := (1094977 / 5000000000 : ℝ)) (by norm_num) hbase hledger)

private theorem fixed_lower_of_eps_form {c q : ℝ} {N lower : ℝ → ℝ}
    (hq : q < c)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * N T ≤ lower T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ lower T := by
  obtain ⟨T₀, hT₀⟩ := h (c - q) (sub_pos.mpr hq)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Fixed rational dyadic headline, still with the two analytic interfaces
shown explicitly in the type. -/
theorem thmD₀_sextuple_6727556_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (1 / 80) (1094977 / 5000000000) penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727556 / 10 ^ 7 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  fixed_lower_of_eps_form sextupleLowerConstant_gt_6727556
    (thmD₀_sextuple_of_interfaces hbase hledger)

/-- Fixed rational cumulative headline, with the same explicit interfaces. -/
theorem thmD₀_sextuple_cumulative_6727556_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (1 / 80) (1094977 / 5000000000) penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727556 / 10 ^ 7 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  fixed_lower_of_eps_form sextupleLowerConstant_gt_6727556
    (thmD₀_sextuple_cumulative_of_interfaces hbase hledger)

end Sextuple
end ThmD
end Zeta23

end
