/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly

/-!
# The scalar sextuple-feedback ledger

This file isolates the final scalar argument from the analytic construction of
the penalty and from the finite sextuple certificate.  The two interfaces below
are the exact inputs to the feedback step:

* `BasePenaltyInterface` is the strengthened Montgomery--Taylor zero-side bound
  with the nonnegative spectral penalty retained;
* `SextupleLedgerInterface` is the pinching, six-shift span ledger, and affine
  sextuple certificate after all transfer errors have been collected.

Both interfaces expose their transfer remainder explicitly and require it to be
`o(N)`.  No analytic or numerical statement is assumed elsewhere in this file.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple

/-- The analytic base interface.  It retains `penalty` in the
Montgomery--Taylor lower bound for the simple critical-line count. -/
structure BasePenaltyInterface (BMT : ℝ)
    (N simple penalty error : ℝ → ℝ) : Prop where
  lower_bound : ∀ᶠ T in atTop,
    BMT * N T + penalty T - error T ≤ simple T
  error_isLittleO : error =o[atTop] N

/-- The geometric/certificate interface.  Its coefficient `A / 6` comes from
one complete sextuple per six simple zeros.  The loss `5 * π * B / 3` is the
six-shift consecutive-span ledger together with `L*T = 2*π*N + o(N)`. -/
structure SextupleLedgerInterface (A B : ℝ)
    (N simple penalty error : ℝ → ℝ) : Prop where
  lower_bound : ∀ᶠ T in atTop,
    A / 6 * simple T - 5 * Real.pi * B / 3 * N T - error T ≤ penalty T
  error_isLittleO : error =o[atTop] N

/-- The proportion obtained after solving the scalar feedback inequality. -/
def feedbackConstant (BMT A B : ℝ) : ℝ :=
  (6 * BMT - 10 * Real.pi * B) / (6 - A)

/-- Fixed-scale feedback algebra, with both transfer errors still visible. -/
theorem sextuple_feedback_pointwise
    {BMT A B N simple penalty baseError ledgerError : ℝ}
    (hbase : BMT * N + penalty - baseError ≤ simple)
    (hledger : A / 6 * simple - 5 * Real.pi * B / 3 * N - ledgerError ≤ penalty) :
    (6 * BMT - 10 * Real.pi * B) * N - 6 * (baseError + ledgerError)
      ≤ (6 - A) * simple := by
  nlinarith [hbase, hledger]

/-- Error-free specialization of `sextuple_feedback_pointwise`:
`(6-A)s ≥ (6 BMT - 10πB)N`. -/
theorem sextuple_feedback_pointwise_no_error
    {BMT A B N simple penalty : ℝ}
    (hbase : BMT * N + penalty ≤ simple)
    (hledger : A / 6 * simple - 5 * Real.pi * B / 3 * N ≤ penalty) :
    (6 * BMT - 10 * Real.pi * B) * N ≤ (6 - A) * simple := by
  nlinarith [hbase, hledger]

/-- Combine the two named interfaces before discarding the `o(N)` remainder. -/
theorem sextuple_feedback_eventually
    {BMT A B : ℝ} {N simple penalty baseError ledgerError : ℝ → ℝ}
    (hbase : BasePenaltyInterface BMT N simple penalty baseError)
    (hledger : SextupleLedgerInterface A B N simple penalty ledgerError) :
    ∀ᶠ T in atTop,
      (6 * BMT - 10 * Real.pi * B) * N T
          - 6 * (baseError T + ledgerError T) ≤ (6 - A) * simple T := by
  filter_upwards [hbase.lower_bound, hledger.lower_bound] with T hb hl
  exact sextuple_feedback_pointwise hb hl

/-- Cleared-denominator epsilon form of the feedback bound. -/
theorem sextuple_feedback_cleared_eps
    {BMT A B : ℝ} {N simple penalty baseError ledgerError : ℝ → ℝ}
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (hbase : BasePenaltyInterface BMT N simple penalty baseError)
    (hledger : SextupleLedgerInterface A B N simple penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6 * BMT - 10 * Real.pi * B - ε) * N T ≤ (6 - A) * simple T := by
  have herr : (fun T => 6 * (baseError T + ledgerError T)) =o[atTop] N := by
    simpa only [Pi.add_apply] using
      (hbase.error_isLittleO.add hledger.error_isLittleO).const_mul_left 6
  exact Assembly.eps_form_of_isLittleO
    (H₀ := 6 * BMT - 10 * Real.pi * B)
    (N := N) (lower := fun T => (6 - A) * simple T)
    (err := fun T => 6 * (baseError T + ledgerError T))
    (sextuple_feedback_eventually hbase hledger) hN herr

/-- Solved epsilon form.  The only scalar side condition is `A < 6`, which is
what makes the feedback denominator positive. -/
theorem sextuple_feedback_eps
    {BMT A B : ℝ} {N simple penalty baseError ledgerError : ℝ → ℝ}
    (hA : A < 6) (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (hbase : BasePenaltyInterface BMT N simple penalty baseError)
    (hledger : SextupleLedgerInterface A B N simple penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (feedbackConstant BMT A B - ε) * N T ≤ simple T := by
  intro ε hε
  have hd : 0 < 6 - A := sub_pos.mpr hA
  obtain ⟨T₀, hT₀⟩ := sextuple_feedback_cleared_eps hN hbase hledger
    (ε * (6 - A)) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => (mul_le_mul_iff_right₀ hd).mp ?_⟩
  calc
    (6 - A) * ((feedbackConstant BMT A B - ε) * N T) =
        (6 * BMT - 10 * Real.pi * B - ε * (6 - A)) * N T := by
          rw [feedbackConstant]
          field_simp
    _ ≤ (6 - A) * simple T := hT₀ T hT

end Sextuple
end ThmD
end Zeta23

end
