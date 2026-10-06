import Zeta23.ThmD.Sextuple.Ledger
import Zeta23.ThmD.Sextuple.Final

/-!
# Conditional sextuple assembly at `A = 129 / 10000`, `B = B₆`

Specializes the existing general ledger and final-assembly theorems to the exact constants.
The affine certificate is an explicit theorem hypothesis throughout; the concrete certificate
is supplied by `Zeta23.ThmD.Sextuple.A1290.Certificate`.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace ImprovedAssembly
namespace A1290

/-- The affine-energy coefficient. -/
def A : ℝ := 129 / 10000

/-- The span coefficient retained from the baseline certificate. -/
def B : ℝ := B6

/-- The transferred zeta-ledger error. -/
def zetaSextupleLedgerError : ℝ → ℝ :=
  zetaLedgerError (129 / 10000) (fun T => 10 * gramTransferError T)

theorem zetaSextupleLedgerInterface_of_certificate
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      (129 / 10000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g) :
    ZetaSextupleLedgerInterface
      (129 / 10000) B6 zetaSextuplePenalty zetaSextupleLedgerError := by
  change ZetaSextupleLedgerInterface
    (129 / 10000) B6 zetaSextuplePenalty
    (zetaLedgerError (129 / 10000) (fun T => 10 * gramTransferError T))
  exact zetaSextupleLedgerInterface_of_ordered_entry_close
    (A := (129 / 10000 : ℝ)) (B := B6) (entryError := gramTransferError)
    (by norm_num) (by norm_num) (by norm_num [B6])
    gramTransferError_eventually_nonneg gramTransferError_tendsto_zero
    hcertificate eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le

theorem zetaSextupleLedgerError_isLittleO :
    zetaSextupleLedgerError =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  change zetaLedgerError (129 / 10000) (fun T => 10 * gramTransferError T)
    =o[atTop] (fun T => (Ncount T (2 * T) : ℝ))
  apply Zeta23.ThmD.Sextuple.zetaLedgerError_isLittleO
  simpa using gramTransferError_tendsto_zero.const_mul 10

/-- The exact feedback constant at `A = 129 / 10000` and `B = B₆`. -/
def sextupleLowerConstant : ℝ :=
  feedbackConstant (HD 1) (129 / 10000) B6

theorem sextupleLowerConstant_exact :
    sextupleLowerConstant =
      (3000000000 * HD 1 - 1094977 * Real.pi) / 2993550000 := by
  rw [sextupleLowerConstant, feedbackConstant, B6]
  ring

/-- Strict fixed-rational comparison from the two directed analytic bounds. -/
theorem sextupleLowerConstant_gt_6728005676 :
    (6728005676 / 10 ^ 10 : ℝ) < sextupleLowerConstant := by
  rw [sextupleLowerConstant, feedbackConstant, B6]
  have hBMT := HD_one_decimal.1
  have hpi := Real.pi_lt_d20
  have hden : (0 : ℝ) < 6 - 129 / 10000 := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num at hBMT hpi ⊢
  linarith

theorem sextupleDyadic_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (129 / 10000) B6 penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_dyadic_of_interfaces (A := (129 / 10000 : ℝ))
      (B := B6) (by norm_num) hbase hledger)

theorem sextupleCumulative_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (129 / 10000) B6 penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_cumulative_of_interfaces (A := (129 / 10000 : ℝ))
      (B := B6) (by norm_num) hbase hledger)

private theorem fixedLowerOfEpsForm {c q : ℝ} {N lower : ℝ → ℝ}
    (hq : q < c)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * N T ≤ lower T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ lower T := by
  obtain ⟨T₀, hT₀⟩ := h (c - q) (sub_pos.mpr hq)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

theorem sextupleDyadic_6728005676_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (129 / 10000) B6 penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6728005676 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  fixedLowerOfEpsForm sextupleLowerConstant_gt_6728005676
    (sextupleDyadic_of_interfaces hbase hledger)

theorem sextupleCumulative_6728005676_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (129 / 10000) B6 penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6728005676 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  fixedLowerOfEpsForm sextupleLowerConstant_gt_6728005676
    (sextupleCumulative_of_interfaces hbase hledger)

end A1290
end ImprovedAssembly
end Sextuple
end ThmD
end Zeta23

end
