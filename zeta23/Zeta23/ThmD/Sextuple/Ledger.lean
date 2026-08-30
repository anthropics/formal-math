/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Packing
import Zeta23.ThmD.Sextuple.SpanAsymptotic
import Zeta23.ThmD.Sextuple.Transfer

/-!
# Asymptotic assembly of the sextuple packing ledger

This file converts a finite packing inequality on the ordered interior simple
zeros into the zeta-specialized sextuple ledger interface.  The finite theorem
is supplied as an argument, so this assembly does not assume a packing or
certificate structure.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple

open Assembly

/-- The number of interior simple zeros, viewed as a real-valued function. -/
def zetaInteriorSimpleCount (T : ℝ) : ℝ :=
  (sInterior zetaZeroConfig T montgomeryTaylorParams : ℝ)

/-- The simple Gram columns omitted from the unit-trimmed interior, viewed as
an error function. -/
def zetaOmittedSimpleCount (T : ℝ) : ℝ :=
  (omittedSimpleCount zetaZeroConfig T montgomeryTaylorParams : ℝ)

/-- The explicit remainder produced by finite sextuple packing.  Its three
terms are the omitted simple columns, the at-most-ten unpacked points, and the
per-interior-point transfer error. -/
def zetaLedgerError (A : ℝ) (ε : ℝ → ℝ) (T : ℝ) : ℝ :=
  A / 6 * zetaOmittedSimpleCount T +
    A / 6 * tenPointLoss T + ε T * zetaInteriorSimpleCount T

private theorem sInterior_le_s1 (T : ℝ) :
    sInterior zetaZeroConfig T montgomeryTaylorParams ≤ zetaZeroConfig.s1 T := by
  calc
    sInterior zetaZeroConfig T montgomeryTaylorParams =
        (interiorSimpleIndices zetaZeroConfig T montgomeryTaylorParams).card := rfl
    _ ≤ (Finset.univ : Finset
        (GlobalSimpleIndex zetaZeroConfig T montgomeryTaylorParams)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = zetaZeroConfig.s1 T := by
      simpa only [Finset.card_univ] using
        globalSimpleIndex_card zetaZeroConfig T montgomeryTaylorParams

private theorem N0simple_le_s1 (T : ℝ) (hT : 0 ≤ T) :
    N0simple T (2 * T) ≤ zetaZeroConfig.s1 T := by
  have hD := D0_nonneg T
  have hleft : T - D0 T ≤ T := by linarith
  have hmiddle : T ≤ 2 * T := by linarith
  have hright : 2 * T ≤ 2 * T + D0 T := by linarith
  change zetaZeroConfig.N0s T (2 * T) ≤ zetaZeroConfig.s1 T
  rw [show zetaZeroConfig.s1 T =
      zetaZeroConfig.N0s (T - D0 T) (2 * T + D0 T) from rfl,
    N0s_add zetaZeroConfig hleft (hmiddle.trans hright),
    N0s_add zetaZeroConfig hmiddle hright]
  omega

/-- The dyadic simple count is covered by the interior count and the actual
complement of the interior inside the global simple Gram index. -/
theorem eventually_N0simple_le_interior_add_omitted :
    ∀ᶠ T in atTop,
      (N0simple T (2 * T) : ℝ) ≤
        zetaInteriorSimpleCount T + zetaOmittedSimpleCount T := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hinterior := sInterior_le_s1 T
  have hsimple := N0simple_le_s1 T hT
  have hpartition :
      sInterior zetaZeroConfig T montgomeryTaylorParams +
          omittedSimpleCount zetaZeroConfig T montgomeryTaylorParams =
        zetaZeroConfig.s1 T := by
    rw [omittedSimpleCount, Nat.add_sub_of_le hinterior]
  have hnat : N0simple T (2 * T) ≤
      sInterior zetaZeroConfig T montgomeryTaylorParams +
        omittedSimpleCount zetaZeroConfig T montgomeryTaylorParams := by
    rwa [hpartition]
  change (N0simple T (2 * T) : ℝ) ≤
    (sInterior zetaZeroConfig T montgomeryTaylorParams : ℝ) +
      (omittedSimpleCount zetaZeroConfig T montgomeryTaylorParams : ℝ)
  exact_mod_cast hnat

/-- The ordered interior count is bounded by the full dyadic zero count. -/
theorem eventually_zetaInteriorSimpleCount_le_Ncount :
    ∀ᶠ T in atTop,
      zetaInteriorSimpleCount T ≤ (Ncount T (2 * T) : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have h₁ : T ≤ T + 1 := by linarith
  have h₂ : T + 1 ≤ 2 * T - 1 := by linarith
  have h₃ : 2 * T - 1 ≤ 2 * T := by linarith
  have hsplit₁ := N0s_add zetaZeroConfig h₁ (h₂.trans h₃)
  have hsplit₂ := N0s_add zetaZeroConfig h₂ h₃
  have hinterior :
      sInterior zetaZeroConfig T montgomeryTaylorParams ≤
        zetaZeroConfig.N0s T (2 * T) := by
    rw [sInterior_eq_N0s]
    omega
  have hsimpleN : zetaZeroConfig.N0s T (2 * T) ≤
      zetaZeroConfig.N T (2 * T) :=
    ((zetaZeroConfig.trivial_chain T (2 * T)).1.trans
      (zetaZeroConfig.trivial_chain T (2 * T)).2.1).trans
        (zetaZeroConfig.trivial_chain T (2 * T)).2.2.1
  change (sInterior zetaZeroConfig T montgomeryTaylorParams : ℝ) ≤
    (zetaZeroConfig.N T (2 * T) : ℝ)
  exact_mod_cast hinterior.trans hsimpleN

/-- The interior simple count is `O(N(T,2T))`. -/
theorem zetaInteriorSimpleCount_isBigO :
    zetaInteriorSimpleCount =O[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_zetaInteriorSimpleCount_le_Ncount] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  simpa using hT

/-- The omitted simple Gram columns are negligible relative to the dyadic zero
count. -/
theorem zetaOmittedSimpleCount_isLittleO :
    zetaOmittedSimpleCount =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  have h := omittedSimpleCount_isLittleO zetaZeroConfig
    montgomeryTaylorParams paperInputs_zeta
  exact (h.congr_left fun _ => rfl).congr_right fun T => by
    simp only [zetaZeroConfig_N]

/-- If the pointwise transfer error tends to zero, the complete explicit
packing remainder is `o(N(T,2T))`. -/
theorem zetaLedgerError_isLittleO {A : ℝ} {ε : ℝ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    zetaLedgerError A ε =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  have homitted := zetaOmittedSimpleCount_isLittleO.const_mul_left (A / 6)
  have hten := tenPointLoss_isLittleO.const_mul_left (A / 6)
  have htransfer :
      (fun T => ε T * zetaInteriorSimpleCount T) =o[atTop]
        (fun T => (Ncount T (2 * T) : ℝ)) := by
    simpa only [one_mul] using
      ((isLittleO_one_iff ℝ).2 hε).mul_isBigO
        zetaInteriorSimpleCount_isBigO
  exact (homitted.add hten).add htransfer |>.congr_left fun T => by
    simp only [zetaLedgerError]

/-- Convert any proved finite interior-packing inequality into the exact zeta
sextuple ledger interface.  No packing or numerical certificate is bundled as
an assumption: the concrete finite lower bound is the theorem argument
`hpacking`.

The error `ε T` is the already-collected transfer loss per interior point. -/
theorem zetaSextupleLedgerInterface_of_finite_packing
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hpacking : ∀ᶠ T in atTop,
      A / 6 * (zetaInteriorSimpleCount T - tenPointLoss T) -
          5 * B / 6 * (montgomeryTaylorParams.L T * T) -
          ε T * zetaInteriorSimpleCount T ≤ zetaSextuplePenalty T) :
    ZetaSextupleLedgerInterface A B zetaSextuplePenalty
      (zetaLedgerError A ε) := by
  refine ⟨?_, zetaLedgerError_isLittleO hε⟩
  filter_upwards [hpacking, eventually_N0simple_le_interior_add_omitted,
    eventually_montgomeryTaylor_span_le] with T hpack hcount hspan
  have hA6 : 0 ≤ A / 6 := div_nonneg hA (by norm_num)
  have hB56 : 0 ≤ 5 * B / 6 := by positivity
  have hcount' := mul_le_mul_of_nonneg_left hcount hA6
  have hspan' := mul_le_mul_of_nonneg_left hspan hB56
  simp only [zetaLedgerError]
  calc
    A / 6 * (N0simple T (2 * T) : ℝ) -
          5 * Real.pi * B / 3 * (Ncount T (2 * T) : ℝ) -
          (A / 6 * zetaOmittedSimpleCount T +
            A / 6 * tenPointLoss T + ε T * zetaInteriorSimpleCount T)
        ≤ A / 6 *
              (zetaInteriorSimpleCount T + zetaOmittedSimpleCount T) -
            5 * Real.pi * B / 3 * (Ncount T (2 * T) : ℝ) -
            (A / 6 * zetaOmittedSimpleCount T +
              A / 6 * tenPointLoss T + ε T * zetaInteriorSimpleCount T) := by
          linarith
    _ = A / 6 * (zetaInteriorSimpleCount T - tenPointLoss T) -
          5 * B / 6 * (2 * Real.pi * (Ncount T (2 * T) : ℝ)) -
          ε T * zetaInteriorSimpleCount T := by ring
    _ ≤ A / 6 * (zetaInteriorSimpleCount T - tenPointLoss T) -
          5 * B / 6 * (montgomeryTaylorParams.L T * T) -
          ε T * zetaInteriorSimpleCount T := by linarith
    _ ≤ zetaSextuplePenalty T := hpack

/-- Assemble the zeta ledger directly from an eventual ordered-entry transfer
bound and an affine sextuple certificate.  The finite six-offset packing,
Poisson normalization, ideal-kernel bound, physical-span bound, and all
asymptotic bookkeeping are discharged here. -/
theorem zetaSextupleLedgerInterface_of_ordered_entry_close
    {A B : ℝ} (hA : 0 ≤ A) (hA6 : A ≤ 6 / 5) (hB : 0 ≤ B)
    {entryError : ℝ → ℝ}
    (hentry_nonneg : ∀ᶠ T in atTop, 0 ≤ entryError T)
    (hentry_zero : Tendsto entryError atTop (𝓝 0))
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      A ≤ sextupleEnergy g + B * sextupleSpan g)
    (hclose : ∀ᶠ T in atTop,
      ∀ i j : Fin (sInterior zetaZeroConfig T
        (montgomeryTaylorParams.atD T)),
        ‖ZeroSide.simpleZeroGram zetaZeroConfig T
              (montgomeryTaylorParams.atD T)
              (interiorGramEmbedding zetaZeroConfig T
                (montgomeryTaylorParams.atD T) i)
              (interiorGramEmbedding zetaZeroConfig T
                (montgomeryTaylorParams.atD T) j) -
            (mtKernel ((montgomeryTaylorParams.atD T).L T *
              (orderedOrdinate zetaZeroConfig T
                  (montgomeryTaylorParams.atD T) i -
                orderedOrdinate zetaZeroConfig T
                  (montgomeryTaylorParams.atD T) j)) : ℂ)‖ ≤ entryError T) :
    ZetaSextupleLedgerInterface A B zetaSextuplePenalty
      (zetaLedgerError A (fun T => 10 * entryError T)) := by
  let P : Params := montgomeryTaylorParams
  have hP : P.Valid := by
    dsimp [P, montgomeryTaylorParams]
    exact paramsOf_valid taperProfile_stdProfile (by norm_num) (by norm_num)
  have hentry10 : Tendsto (fun T => 10 * entryError T) atTop (𝓝 0) := by
    simpa using hentry_zero.const_mul 10
  apply zetaSextupleLedgerInterface_of_finite_packing hA hB hentry10
  filter_upwards [hentry_nonneg, hclose, eventually_w8 hP,
    eventually_w4pi hP, eventually_ge_atTop (0 : ℝ)]
      with T hentry hcloseT h8 h4pi hT
  have hLpos : 0 < P.L T := by linarith [hP.one_le_w]
  have hLDpos : 0 < (P.atD T).L T := by
    simpa only [Params.atD_L] using hLpos
  have haD := (aD_range_of hP h8 h4pi).1
  have hcD : 0 < (P.atD T).a T * (P.atD T).L T ^ 2 :=
    mul_pos (by linarith) (sq_pos_of_pos hLDpos)
  have hfinite := simpleSextuplePenalty_packing_of_ordered_entry_close_poisson
    zetaZeroConfig T (P.atD T) hLDpos.le (poissonSqD hP h8) hcD
      hentry hA hA6 hB hcertificate (by
        simpa only [P] using hcloseT) abs_mtKernel_le_one
  have htotal :
      BlockLedger.totalGap
          (adjacentGap zetaZeroConfig T (P.atD T)) ≤ P.L T * T := by
    simpa only [BlockLedger.totalGap, Params.atD_L] using
      (sum_adjacentGap_le zetaZeroConfig T (P.atD T) hLDpos.le hT)
  have hspan := mul_le_mul_of_nonneg_left htotal
    (show 0 ≤ 5 * B / 6 by positivity)
  have hcount :
      (sInterior zetaZeroConfig T (P.atD T) : ℝ) =
        zetaInteriorSimpleCount T := by
    simp only [zetaInteriorSimpleCount, sInterior_eq_N0s]
  rw [hcount] at hfinite
  change A / 6 * (zetaInteriorSimpleCount T - 10) -
      5 * B / 6 *
        BlockLedger.totalGap (adjacentGap zetaZeroConfig T (P.atD T)) -
      10 * zetaInteriorSimpleCount T * entryError T ≤
        zetaSextuplePenalty T at hfinite
  calc
    A / 6 * (zetaInteriorSimpleCount T - tenPointLoss T) -
          5 * B / 6 * (montgomeryTaylorParams.L T * T) -
          (10 * entryError T) * zetaInteriorSimpleCount T =
        A / 6 * (zetaInteriorSimpleCount T - 10) -
          5 * B / 6 * (P.L T * T) -
          10 * zetaInteriorSimpleCount T * entryError T := by
            simp only [tenPointLoss, P]
            ring
    _ ≤ A / 6 * (zetaInteriorSimpleCount T - 10) -
          5 * B / 6 *
            BlockLedger.totalGap (adjacentGap zetaZeroConfig T (P.atD T)) -
          10 * zetaInteriorSimpleCount T * entryError T := by linarith
    _ ≤ zetaSextuplePenalty T := hfinite

/-- The concrete zeta ledger remainder after inserting the proved transfer
error and the exact packing factor ten. -/
def zetaSextupleLedgerError : ℝ → ℝ :=
  zetaLedgerError A6 (fun T => 10 * gramTransferError T)

/-- Instantiate every analytic and packing input of the zeta ledger, leaving
only the ordinary affine certificate theorem as an argument.  This theorem is
an adapter, not a conditional interface assumption. -/
theorem zetaSextupleLedgerInterface_of_certificate
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      A6 ≤ sextupleEnergy g + B6 * sextupleSpan g) :
    ZetaSextupleLedgerInterface A6 B6 zetaSextuplePenalty
      zetaSextupleLedgerError := by
  change ZetaSextupleLedgerInterface A6 B6 zetaSextuplePenalty
    (zetaLedgerError A6 (fun T => 10 * gramTransferError T))
  exact zetaSextupleLedgerInterface_of_ordered_entry_close
    (A := A6) (B := B6) (entryError := gramTransferError)
    (by norm_num [A6]) (by norm_num [A6]) (by norm_num [B6])
    gramTransferError_eventually_nonneg gramTransferError_tendsto_zero
    hcertificate eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le

/-- The fully concrete ledger remainder is negligible relative to the dyadic
zero count, independently of the numerical certificate. -/
theorem zetaSextupleLedgerError_isLittleO :
    zetaSextupleLedgerError =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  apply zetaLedgerError_isLittleO
  simpa using gramTransferError_tendsto_zero.const_mul 10

end Sextuple
end ThmD
end Zeta23

end
