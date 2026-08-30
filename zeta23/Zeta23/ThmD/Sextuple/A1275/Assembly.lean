import Zeta23.ThmD.Sextuple.Ledger
import Zeta23.ThmD.Sextuple.Final

/-!
# Improved sextuple assembly

This artifact specializes the existing general ledger and final-assembly theorems
to `A = 63 / 5000` and `A = 51 / 4000`, with
`B = B6 = 1094977 / 5000000000`.  Each ordinary affine certificate remains an
explicit theorem hypothesis.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace ImprovedAssembly

/-- The improved affine-energy coefficient. -/
def improvedA : ℝ := 63 / 5000

/-- The retained affine-span coefficient. -/
def improvedB : ℝ := 1094977 / 5000000000

/-- The transferred zeta-ledger error for the improved coefficient. -/
def improvedZetaSextupleLedgerError : ℝ → ℝ :=
  zetaLedgerError (63 / 5000) (fun T => 10 * gramTransferError T)

/--
Specialize the existing ordered-entry transfer theorem to the improved exact
constants.  The numerical affine certificate is deliberately an argument.
-/
theorem improvedZetaSextupleLedgerInterface_of_certificate
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      (63 / 5000 : ℝ) ≤ sextupleEnergy g +
        (1094977 / 5000000000 : ℝ) * sextupleSpan g) :
    ZetaSextupleLedgerInterface
      (63 / 5000) (1094977 / 5000000000) zetaSextuplePenalty
      improvedZetaSextupleLedgerError := by
  change ZetaSextupleLedgerInterface
    (63 / 5000) (1094977 / 5000000000) zetaSextuplePenalty
    (zetaLedgerError (63 / 5000) (fun T => 10 * gramTransferError T))
  exact zetaSextupleLedgerInterface_of_ordered_entry_close
    (A := (63 / 5000 : ℝ)) (B := (1094977 / 5000000000 : ℝ))
    (entryError := gramTransferError)
    (by norm_num) (by norm_num) (by norm_num)
    gramTransferError_eventually_nonneg gramTransferError_tendsto_zero
    hcertificate eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le

/-- The improved transferred ledger error is negligible independently of the certificate. -/
theorem improvedZetaSextupleLedgerError_isLittleO :
    improvedZetaSextupleLedgerError =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  change zetaLedgerError (63 / 5000) (fun T => 10 * gramTransferError T)
    =o[atTop] (fun T => (Ncount T (2 * T) : ℝ))
  apply zetaLedgerError_isLittleO
  simpa using gramTransferError_tendsto_zero.const_mul 10

/-- The exact feedback constant at the improved rational inputs. -/
def improvedSextupleLowerConstant : ℝ :=
  feedbackConstant (HD 1) (63 / 5000) (1094977 / 5000000000)

/-- A denominator-cleared exact form of the improved feedback constant. -/
theorem improvedSextupleLowerConstant_exact :
    improvedSextupleLowerConstant =
      (3000000000 * HD 1 - 1094977 * Real.pi) / 2993700000 := by
  rw [improvedSextupleLowerConstant, feedbackConstant]
  ring

/--
Certified strict comparison with `6727668568 / 10^10`.  Only the directed
bounds `HD_one_decimal.1` and `Real.pi_lt_d20` enter the arithmetic proof.
-/
theorem improvedSextupleLowerConstant_gt_6727668568 :
    (6727668568 / 10 ^ 10 : ℝ) < improvedSextupleLowerConstant := by
  rw [improvedSextupleLowerConstant, feedbackConstant]
  have hBMT := HD_one_decimal.1
  have hpi := Real.pi_lt_d20
  have hden : (0 : ℝ) < 6 - 63 / 5000 := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num at hBMT hpi ⊢
  linarith

/-- Exact-constant dyadic epsilon assembly, conditional on both interfaces. -/
theorem improvedSextupleDyadic_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (63 / 5000) (1094977 / 5000000000) penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (improvedSextupleLowerConstant - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simpa only [improvedSextupleLowerConstant] using
    (sextuple_zeta_dyadic_of_interfaces (A := (63 / 5000 : ℝ))
      (B := (1094977 / 5000000000 : ℝ)) (by norm_num) hbase hledger)

/-- Exact-constant cumulative epsilon assembly, conditional on both interfaces. -/
theorem improvedSextupleCumulative_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (63 / 5000) (1094977 / 5000000000) penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (improvedSextupleLowerConstant - ε) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T := by
  simpa only [improvedSextupleLowerConstant] using
    (sextuple_zeta_cumulative_of_interfaces (A := (63 / 5000 : ℝ))
      (B := (1094977 / 5000000000 : ℝ)) (by norm_num) hbase hledger)

private theorem fixedLowerOfEpsForm {c q : ℝ} {N lower : ℝ → ℝ}
    (hq : q < c)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * N T ≤ lower T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ lower T := by
  obtain ⟨T₀, hT₀⟩ := h (c - q) (sub_pos.mpr hq)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Fixed-rational dyadic wrapper, with both analytic interfaces explicit. -/
theorem improvedSextupleDyadic_6727668568_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (63 / 5000) (1094977 / 5000000000) penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727668568 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  fixedLowerOfEpsForm improvedSextupleLowerConstant_gt_6727668568
    (improvedSextupleDyadic_of_interfaces hbase hledger)

/-- Fixed-rational cumulative wrapper, with both analytic interfaces explicit. -/
theorem improvedSextupleCumulative_6727668568_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (63 / 5000) (1094977 / 5000000000) penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727668568 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  fixedLowerOfEpsForm improvedSextupleLowerConstant_gt_6727668568
    (improvedSextupleCumulative_of_interfaces hbase hledger)


namespace A1275

/-- The refined affine-energy coefficient `0.01275`. -/
def A : ℝ := 51 / 4000

/-- The span coefficient retained from the baseline certificate. -/
def B : ℝ := B6

/-- The transferred zeta-ledger error at `A = 51 / 4000`. -/
def zetaSextupleLedgerError : ℝ → ℝ :=
  zetaLedgerError (51 / 4000) (fun T => 10 * gramTransferError T)

/--
Specialize the existing ordered-entry transfer theorem to `A = 51 / 4000` and
`B = B6`.  The corresponding ordinary affine certificate remains an argument.
-/
theorem zetaSextupleLedgerInterface_of_certificate
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      (51 / 4000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g) :
    ZetaSextupleLedgerInterface
      (51 / 4000) B6 zetaSextuplePenalty zetaSextupleLedgerError := by
  change ZetaSextupleLedgerInterface
    (51 / 4000) B6 zetaSextuplePenalty
    (zetaLedgerError (51 / 4000) (fun T => 10 * gramTransferError T))
  exact zetaSextupleLedgerInterface_of_ordered_entry_close
    (A := (51 / 4000 : ℝ)) (B := B6) (entryError := gramTransferError)
    (by norm_num) (by norm_num) (by norm_num [B6])
    gramTransferError_eventually_nonneg gramTransferError_tendsto_zero
    hcertificate eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le

/-- The transferred ledger error is negligible independently of the certificate. -/
theorem zetaSextupleLedgerError_isLittleO :
    zetaSextupleLedgerError =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  change zetaLedgerError (51 / 4000) (fun T => 10 * gramTransferError T)
    =o[atTop] (fun T => (Ncount T (2 * T) : ℝ))
  apply Zeta23.ThmD.Sextuple.zetaLedgerError_isLittleO
  simpa using gramTransferError_tendsto_zero.const_mul 10

/-- The exact feedback constant at `A = 51 / 4000` and `B = B6`. -/
def sextupleLowerConstant : ℝ :=
  feedbackConstant (HD 1) (51 / 4000) B6

/-- A denominator-cleared exact form of the refined feedback constant. -/
theorem sextupleLowerConstant_exact :
    sextupleLowerConstant =
      (3000000000 * HD 1 - 1094977 * Real.pi) / 2993625000 := by
  rw [sextupleLowerConstant, feedbackConstant, B6]
  ring

/-- Strict fixed-rational comparison from the two directed analytic bounds. -/
theorem sextupleLowerConstant_gt_6727837118 :
    (6727837118 / 10 ^ 10 : ℝ) < sextupleLowerConstant := by
  rw [sextupleLowerConstant, feedbackConstant, B6]
  have hBMT := HD_one_decimal.1
  have hpi := Real.pi_lt_d20
  have hden : (0 : ℝ) < 6 - 51 / 4000 := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num at hBMT hpi ⊢
  linarith

/-- Exact-constant dyadic epsilon assembly, conditional on both interfaces. -/
theorem sextupleDyadic_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (51 / 4000) B6 penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_dyadic_of_interfaces (A := (51 / 4000 : ℝ))
      (B := B6) (by norm_num) hbase hledger)

/-- Exact-constant cumulative epsilon assembly, conditional on both interfaces. -/
theorem sextupleCumulative_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (51 / 4000) B6 penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_cumulative_of_interfaces (A := (51 / 4000 : ℝ))
      (B := B6) (by norm_num) hbase hledger)

/-- Fixed-rational dyadic wrapper, with both analytic interfaces explicit. -/
theorem sextupleDyadic_6727837118_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (51 / 4000) B6 penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727837118 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  fixedLowerOfEpsForm sextupleLowerConstant_gt_6727837118
    (sextupleDyadic_of_interfaces hbase hledger)

/-- Fixed-rational cumulative wrapper, with both analytic interfaces explicit. -/
theorem sextupleCumulative_6727837118_of_interfaces
    {penalty baseError ledgerError : ℝ → ℝ}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      (51 / 4000) B6 penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727837118 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  fixedLowerOfEpsForm sextupleLowerConstant_gt_6727837118
    (sextupleCumulative_of_interfaces hbase hledger)

end A1275

end ImprovedAssembly
end Sextuple
end ThmD
end Zeta23

-- Endpoint types and trusted dependencies are emitted by the direct native check.
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedA
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedB
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedZetaSextupleLedgerError
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedZetaSextupleLedgerInterface_of_certificate
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedZetaSextupleLedgerError_isLittleO
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleLowerConstant
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleLowerConstant_exact
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleLowerConstant_gt_6727668568
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleDyadic_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleCumulative_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleDyadic_6727668568_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleCumulative_6727668568_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.A
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.B
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerError
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerError_isLittleO
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant_exact
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleDyadic_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleCumulative_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleDyadic_6727837118_of_interfaces
#check Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleCumulative_6727837118_of_interfaces

#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedA
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedB
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedZetaSextupleLedgerError
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedZetaSextupleLedgerInterface_of_certificate
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedZetaSextupleLedgerError_isLittleO
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleLowerConstant
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleLowerConstant_exact
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleLowerConstant_gt_6727668568
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleDyadic_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleCumulative_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleDyadic_6727668568_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.improvedSextupleCumulative_6727668568_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.A
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.B
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerError
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerError_isLittleO
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant_exact
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleDyadic_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleCumulative_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleDyadic_6727837118_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleCumulative_6727837118_of_interfaces

end
