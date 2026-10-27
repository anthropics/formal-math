/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Interior
import Zeta23.ThmD.Sextuple.BlockLedger
import Zeta23.ThmD.Sextuple.BlockPenalty

/-!
# Finite packing of interior simple-zero sextuples

This file compresses the ordered interior simple-zero Gram matrix into the six
families of disjoint principal sextuple blocks.  The first theorem is a purely
finite ledger with an explicit per-block error.  The later theorems instantiate
it with the actual normalized simple-zero Gram matrix.
-/

noncomputable section

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace Zeta23
namespace ThmD
namespace Sextuple

open BlockLedger

/-- Purely finite six-offset packing with a `60 * ε` error on each complete
block.  Since an offset contains at most `(n+1)/6` complete blocks, the total
entry-transfer loss is exactly bounded by `10 * (n+1) * ε`. -/
theorem finite_packing_with_entry_error {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) {A B ε globalPenalty : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    {blockPenalty : (r : Offset) → Fin (offsetBlockCount n r) → ℝ}
    (hpinch : GlobalPenaltyDominatesBlocks blockPenalty globalPenalty)
    (hblock : ∀ r q,
      A ≤ blockPenalty r q + B * blockSpan g r q + 60 * ε) :
    A / 6 * (((n + 1 : ℕ) : ℝ) - 10)
        - 5 * B / 6 * totalGap g
        - 10 * ((n + 1 : ℕ) : ℝ) * ε ≤ globalPenalty := by
  obtain ⟨r, hspan⟩ := exists_offsetSpan_le_five_sixths g hg
  have hsum := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset
      (Fin (offsetBlockCount n r)))) => hblock r q
  simp only [sum_add_distrib, ← Finset.mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← offsetSpan_eq_sum_blockSpan] at hsum
  have hpinch_r := hpinch r
  have hcountLowerNat := pointCount_le_six_mul_blockCount_add_ten n r
  have hcountLowerCast : ((n + 1 : ℕ) : ℝ) ≤
      6 * (offsetBlockCount n r : ℝ) + 10 := by
    exact_mod_cast hcountLowerNat
  have hcountLower : ((n + 1 : ℕ) : ℝ) - 10 ≤
      6 * (offsetBlockCount n r : ℝ) := by
    linarith
  have hcountUpperNat : 6 * offsetBlockCount n r ≤ n + 1 := by
    have hr := r.isLt
    simp only [offsetBlockCount]
    omega
  have hcountUpper : 6 * (offsetBlockCount n r : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcountUpperNat
  have hAcount : A / 6 * (((n + 1 : ℕ) : ℝ) - 10) ≤
      A * (offsetBlockCount n r : ℝ) := by
    nlinarith
  have hBspan : B * offsetSpan g r ≤
      5 * B / 6 * totalGap g := by
    nlinarith
  have herror : 60 * ε * (offsetBlockCount n r : ℝ) ≤
      10 * ((n + 1 : ℕ) : ℝ) * ε := by
    nlinarith
  nlinarith


/-! ## The actual interior principal blocks -/

/-- Transport the ordered interior embedding from `Fin s` to `Fin (n+1)` once
`n+1=s`.  This equality-based form keeps all later block definitions free of
casts in their ambient Gram indices. -/
def interiorCoreEmbedding (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) :
    Fin (n + 1) ↪ GlobalSimpleIndex Z T P where
  toFun i := interiorGramEmbedding Z T P (Fin.cast hn i)
  inj' := by
    intro i j hij
    have hcast := (interiorGramEmbedding Z T P).injective hij
    exact (Fin.castOrderIso hn).injective hcast

/-- The actual six-by-six principal block of the global normalized simple-zero
Gram matrix selected by offset `r` and block number `q`. -/
def interiorPrincipalBlock (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) : Matrix (Fin 6) (Fin 6) ℂ :=
  corePrincipalBlock (ZeroSide.simpleZeroGram Z T P)
    (interiorCoreEmbedding Z T P hn) r q

/-- Poisson normalization gives the exact squared-norm bound for every
global simple-zero column. -/
theorem simpleZeroColumns_normSq_le_one
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (z : GlobalSimpleIndex Z T P) :
    (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) ≤ 1 := by
  let hconj : ZeroSide.PhiHatConj T P := fun w => GzGp.phiHat_conj P T w
  let hreal : ZeroSide.PhiHatReal T P := fun x => GzGp.phiHat_ofReal P T x
  have hzOnS : z.1 ∈ (ZeroSide.sextupleBlockData Z T P).onLine :=
    ZeroSide.ZeroBlockData.mem_onLine_of_mem_S₁
      (ZeroSide.sextupleBlockData Z T P) z.2
  have hzOn : z.1 ∈ (ZeroSide.blockData Z T P hconj).onLine := by
    rw [ZeroSide.blockData_eq_sextupleBlockData Z T P hconj]
    exact hzOnS
  have hraw := ZeroSide.sum_normSq_v_le Z T P hconj hreal hPois z.1 hzOn
  change (∑ k, ‖ZeroSide.evalVec Z T P z.1 k‖ ^ 2) ≤
    P.a T * P.L T ^ 2 at hraw
  calc
    (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) =
        (∑ k, ‖ZeroSide.evalVec Z T P z.1 k‖ ^ 2) /
          (P.a T * P.L T ^ 2) := by
      simp_rw [ZeroSide.simpleZeroColumns_apply, norm_div,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.sqrt_pos.mpr hc), div_pow, Real.sq_sqrt hc.le]
      rw [← Finset.sum_div]
    _ ≤ 1 := (div_le_one hc).mpr hraw

/-- Exact Cauchy--Schwarz consequence of normalized simple-zero column
norms.  This statement is finite and does not depend on how the column bound
was obtained. -/
theorem simpleZeroGram_entry_norm_le_one
    (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hcolumn : ∀ z : GlobalSimpleIndex Z T P,
      (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) ≤ 1)
    (z w : GlobalSimpleIndex Z T P) :
    ‖ZeroSide.simpleZeroGram Z T P z w‖ ≤ 1 := by
  let W := ZeroSide.simpleZeroColumns Z T P
  have hnormSum : ‖∑ k, star (W k z) * W k w‖ ≤
      ∑ k, ‖W k z‖ * ‖W k w‖ := by
    calc
      ‖∑ k, star (W k z) * W k w‖ ≤
          ∑ k, ‖star (W k z) * W k w‖ := norm_sum_le _ _
      _ = ∑ k, ‖W k z‖ * ‖W k w‖ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_mul, norm_star]
  have hCS : (∑ k, ‖W k z‖ * ‖W k w‖) ≤
      Real.sqrt (∑ k, ‖W k z‖ ^ 2) *
        Real.sqrt (∑ k, ‖W k w‖ ^ 2) := by
    simpa only [Finset.sum_apply, Finset.sum_const_zero, add_zero] using
      (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun k => ‖W k z‖) (fun k => ‖W k w‖))
  have hzsqrt : Real.sqrt (∑ k, ‖W k z‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hcolumn z
  have hwsqrt : Real.sqrt (∑ k, ‖W k w‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hcolumn w
  have hprod : Real.sqrt (∑ k, ‖W k z‖ ^ 2) *
      Real.sqrt (∑ k, ‖W k w‖ ^ 2) ≤ 1 :=
    mul_le_one₀ hzsqrt (Real.sqrt_nonneg _) hwsqrt
  rw [ZeroSide.simpleZeroGram, Matrix.mul_apply]
  exact hnormSum.trans (hCS.trans hprod)

@[simp] theorem interiorPrincipalBlock_apply
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) (i j : Fin 6) :
    interiorPrincipalBlock Z T P hn r q i j =
      ZeroSide.simpleZeroGram Z T P
        (interiorGramEmbedding Z T P (Fin.cast hn (blockPointIndex r q i)))
        (interiorGramEmbedding Z T P (Fin.cast hn (blockPointIndex r q j))) := by
  rfl

/-- Every actual interior principal block is positive semidefinite. -/
theorem interiorPrincipalBlock_posSemidef
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) :
    (interiorPrincipalBlock Z T P hn r q).PosSemidef := by
  let e : Fin 6 → GlobalSimpleIndex Z T P := fun j =>
    coreBlockPointEmbedding (interiorCoreEmbedding Z T P hn) r (q, j)
  have hsub := (ZeroSide.simpleZeroGram_posSemidef Z T P).submatrix e
  change ((ZeroSide.simpleZeroGram Z T P).submatrix e e).PosSemidef
  exact hsub

/-- Every entry of an actual interior principal block has norm at most
one when all normalized global columns have squared norm at most one. -/
theorem interiorPrincipalBlock_entry_norm_le_one
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P)
    (hcolumn : ∀ z : GlobalSimpleIndex Z T P,
      (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) ≤ 1)
    (r : Offset) (q : Fin (offsetBlockCount n r)) (i j : Fin 6) :
    ‖interiorPrincipalBlock Z T P hn r q i j‖ ≤ 1 := by
  exact simpleZeroGram_entry_norm_le_one Z T P hcolumn _ _

/-- The trace of every actual six-point principal block is at most six.  The
bound uses the exact normalized column-norm budget, not a global trace loss. -/
theorem interiorPrincipalBlock_rtrace_le_six
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P)
    (hcolumn : ∀ z : GlobalSimpleIndex Z T P,
      (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) ≤ 1)
    (r : Offset) (q : Fin (offsetBlockCount n r)) :
    RHLinalg.rtrace (interiorPrincipalBlock Z T P hn r q) ≤ 6 := by
  unfold RHLinalg.rtrace Matrix.trace
  calc
    (∑ i : Fin 6, (interiorPrincipalBlock Z T P hn r q i i).re) ≤
        ∑ _i : Fin 6, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ =>
        (Complex.re_le_norm _).trans
          (interiorPrincipalBlock_entry_norm_le_one Z T P hn hcolumn r q i i)
    _ = 6 := by norm_num [Fintype.card_fin]

/-- The spectral penalty attached by the automatic pinching theorem to an
actual interior principal block. -/
def interiorPrincipalBlockPenalty
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) : ℝ :=
  corePrincipalBlockPenalty
    (ZeroSide.simpleZeroGram_posSemidef Z T P).isHermitian
    (interiorCoreEmbedding Z T P hn) r q

/-- The pinching penalty is exactly the block spectral penalty of the actual
positive-semidefinite principal matrix. -/
theorem interiorPrincipalBlockPenalty_eq_blockSpectralPenalty
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) :
    interiorPrincipalBlockPenalty Z T P hn r q =
      blockSpectralPenalty
        (interiorPrincipalBlock_posSemidef Z T P hn r q).isHermitian := by
  rfl

/-- Automatic principal-block pinching inside the global simple-zero Gram
matrix, with the global spectral sum identified with the proof-free scalar
`simpleSextuplePenalty`. -/
theorem simpleSextuplePenalty_dominates_interiorPrincipalBlocks
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) :
    GlobalPenaltyDominatesBlocks
      (interiorPrincipalBlockPenalty Z T P hn)
      (ZeroSide.simpleSextuplePenalty Z T P) := by
  unfold interiorPrincipalBlockPenalty
  rw [ZeroSide.simpleSextuplePenalty_eq_gram]
  exact globalPenaltyDominatesBlocks_of_coreEmbedding
    (ZeroSide.simpleZeroGram_posSemidef Z T P).isHermitian
    (interiorCoreEmbedding Z T P hn)

/-! ## Error-stable packing of the concrete global Gram matrix -/

/-- The adjacent interior gaps transported to `Fin n` from an equality
`n+1=sInterior`. -/
def interiorGaps (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) : Fin n → ℝ :=
  fun i => adjacentGap Z T P ⟨i, by
    have hi := i.isLt
    omega⟩

/-- The five adjacent gaps internal to one complete packed sextuple. -/
def packedBlockGaps {n : ℕ} (g : Fin n → ℝ) (r : Offset)
    (q : Fin (offsetBlockCount n r)) : Fin 5 → ℝ :=
  fun j => g (blockGapIndex r q j)

@[simp] theorem sextupleSpan_packedBlockGaps {n : ℕ} (g : Fin n → ℝ)
    (r : Offset) (q : Fin (offsetBlockCount n r)) :
    sextupleSpan (packedBlockGaps g r q) = blockSpan g r q := by
  rfl

/-- The local translate position is the normalized ordinate displacement
from the first point of the packed block. -/
theorem sextuplePosition_packedInteriorGaps
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) (i : Fin 6) :
    sextuplePosition (packedBlockGaps (interiorGaps Z T P hn) r q) i =
      P.L T *
        (orderedOrdinate Z T P (Fin.cast hn (blockPointIndex r q i)) -
          orderedOrdinate Z T P
            (Fin.cast hn (blockPointIndex r q (0 : Fin 6)))) := by
  fin_cases i <;>
    simp [sextuplePosition, packedBlockGaps, interiorGaps, adjacentGap,
      gapLeftIndex, gapRightIndex, blockGapIndex, blockPointIndex,
      blockStart] <;> ring

/-- Consequently, the ideal matrix of a packed block is the normalized kernel
at the corresponding pair of ordered interior ordinates. -/
theorem sextupleGram_packedInteriorGaps
    (Z : ZeroConfig) (T : ℝ) (P : Params) {n : ℕ}
    (hn : n + 1 = sInterior Z T P) (r : Offset)
    (q : Fin (offsetBlockCount n r)) (i j : Fin 6) :
    sextupleGram (packedBlockGaps (interiorGaps Z T P hn) r q) i j =
      mtKernel (P.L T *
        (orderedOrdinate Z T P (Fin.cast hn (blockPointIndex r q i)) -
          orderedOrdinate Z T P (Fin.cast hn (blockPointIndex r q j)))) := by
  rw [sextupleGram, sextuplePosition_packedInteriorGaps,
    sextuplePosition_packedInteriorGaps]
  congr 1
  ring

/-- Pointwise packing theorem for the actual global simple-zero Gram.  All
analytic and numerical inputs occur as ordinary theorem arguments: normalized
column norms, uniform block-entry closeness, and the ideal affine certificate.
No interface proposition is assumed. -/
theorem simpleSextuplePenalty_packing_of_column_bound
    (Z : ZeroConfig) (T : ℝ) (P : Params) {A B ε : ℝ}
    (hL : 0 ≤ P.L T) (hε : 0 ≤ ε) (hA0 : 0 ≤ A)
    (hA6 : A ≤ 6 / 5) (hB : 0 ≤ B)
    (hcolumn : ∀ z : GlobalSimpleIndex Z T P,
      (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) ≤ 1)
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      A ≤ sextupleEnergy g + B * sextupleSpan g)
    (hclose : ∀ {n : ℕ} (hn : n + 1 = sInterior Z T P)
      (r : Offset) (q : Fin (offsetBlockCount n r)) (i j : Fin 6), i < j →
      ‖interiorPrincipalBlock Z T P hn r q i j -
          (sextupleGram
            (packedBlockGaps (interiorGaps Z T P hn) r q) i j : ℂ)‖ ≤ ε)
    (hideal : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      ∀ i j : Fin 6, i < j → |sextupleGram g i j| ≤ 1) :
    A / 6 * ((sInterior Z T P : ℝ) - 10)
        - 5 * B / 6 * totalGap (adjacentGap Z T P)
        - 10 * (sInterior Z T P : ℝ) * ε ≤
      ZeroSide.simpleSextuplePenalty Z T P := by
  let s := sInterior Z T P
  have hgap : ∀ i : Fin (s - 1), 0 ≤ adjacentGap Z T P i :=
    adjacentGap_nonneg Z T P hL
  have htotal : 0 ≤ totalGap (adjacentGap Z T P) := by
    exact Finset.sum_nonneg fun i _ => hgap i
  by_cases hs : s ≤ 10
  · have hsR : (s : ℝ) ≤ 10 := by exact_mod_cast hs
    have hfirst : A / 6 * ((s : ℝ) - 10) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hA0 (by norm_num))
        (sub_nonpos.mpr hsR)
    have hspanTerm : 0 ≤ 5 * B / 6 * totalGap (adjacentGap Z T P) := by
      positivity
    have herrorTerm : 0 ≤ 10 * (s : ℝ) * ε := by positivity
    have hpenalty := ZeroSide.simpleSextuplePenalty_nonneg Z T P
    change A / 6 * ((s : ℝ) - 10)
        - 5 * B / 6 * totalGap (adjacentGap Z T P)
        - 10 * (s : ℝ) * ε ≤ ZeroSide.simpleSextuplePenalty Z T P
    linarith
  · have hs10 : 10 < s := by omega
    let n := s - 1
    have hn : n + 1 = sInterior Z T P := by
      dsimp [n, s]
      omega
    have hgapn : ∀ i : Fin n, 0 ≤ interiorGaps Z T P hn i := by
      intro i
      exact adjacentGap_nonneg Z T P hL _
    have hpinch :=
      simpleSextuplePenalty_dominates_interiorPrincipalBlocks Z T P hn
    have hblock : ∀ r q,
        A ≤ interiorPrincipalBlockPenalty Z T P hn r q
          + B * blockSpan (interiorGaps Z T P hn) r q + 60 * ε := by
      intro r q
      let gb : Fin 5 → ℝ := packedBlockGaps (interiorGaps Z T P hn) r q
      have hgb : ∀ i, 0 ≤ gb i := fun i => hgapn (blockGapIndex r q i)
      have hpsd := interiorPrincipalBlock_posSemidef Z T P hn r q
      have htrace := interiorPrincipalBlock_rtrace_le_six
        Z T P hn hcolumn r q
      have hactual : ∀ i j : Fin 6, i < j →
          ‖interiorPrincipalBlock Z T P hn r q i j‖ ≤ 1 := by
        intro i j _
        exact interiorPrincipalBlock_entry_norm_le_one
          Z T P hn hcolumn r q i j
      have haffine := blockAffine_of_entrywise_close hpsd htrace gb
        hε hB hgb hA6 (hcertificate gb hgb)
        (fun i j hij => hclose hn r q i j hij) hactual
        (hideal gb hgb)
      rw [← interiorPrincipalBlockPenalty_eq_blockSpectralPenalty
        Z T P hn r q] at haffine
      simpa only [gb, sextupleSpan_packedBlockGaps] using haffine
    have hfinite := finite_packing_with_entry_error
      (g := interiorGaps Z T P hn) hgapn hA0 hB hε hpinch hblock
    have hgapEq : interiorGaps Z T P hn = adjacentGap Z T P := by
      funext i
      rfl
    rw [hgapEq] at hfinite
    have hn' : n + 1 = s := hn
    have hnR : ((n + 1 : ℕ) : ℝ) = (s : ℝ) := by exact_mod_cast hn'
    rw [hnR] at hfinite
    change A / 6 * ((s : ℝ) - 10)
        - 5 * B / 6 * totalGap (adjacentGap Z T P)
        - 10 * (s : ℝ) * ε ≤ ZeroSide.simpleSextuplePenalty Z T P
    exact hfinite

/-- Ordered-entry form of the pointwise packing theorem.  A single
uniform approximation for every pair of ordered interior columns is
transported automatically to every complete principal sextuple block. -/
theorem simpleSextuplePenalty_packing_of_ordered_entry_close
    (Z : ZeroConfig) (T : ℝ) (P : Params) {A B ε : ℝ}
    (hL : 0 ≤ P.L T) (hε : 0 ≤ ε) (hA0 : 0 ≤ A)
    (hA6 : A ≤ 6 / 5) (hB : 0 ≤ B)
    (hcolumn : ∀ z : GlobalSimpleIndex Z T P,
      (∑ k, ‖ZeroSide.simpleZeroColumns Z T P k z‖ ^ 2) ≤ 1)
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      A ≤ sextupleEnergy g + B * sextupleSpan g)
    (hclose : ∀ i j : Fin (sInterior Z T P),
      ‖ZeroSide.simpleZeroGram Z T P
          (interiorGramEmbedding Z T P i)
          (interiorGramEmbedding Z T P j) -
        (mtKernel (P.L T *
          (orderedOrdinate Z T P i - orderedOrdinate Z T P j)) : ℂ)‖ ≤ ε)
    (hkernel : ∀ x : ℝ, |mtKernel x| ≤ 1) :
    A / 6 * ((sInterior Z T P : ℝ) - 10)
        - 5 * B / 6 * totalGap (adjacentGap Z T P)
        - 10 * (sInterior Z T P : ℝ) * ε ≤
      ZeroSide.simpleSextuplePenalty Z T P := by
  apply simpleSextuplePenalty_packing_of_column_bound Z T P hL hε hA0 hA6 hB
    hcolumn hcertificate
  · intro n hn r q i j _
    rw [interiorPrincipalBlock_apply, sextupleGram_packedInteriorGaps]
    exact hclose _ _
  · intro g _ i j _
    exact hkernel (sextuplePosition g i - sextuplePosition g j)

/-- Concrete Poisson-normalized specialization of
`simpleSextuplePenalty_packing_of_column_bound`. -/
theorem simpleSextuplePenalty_packing
    (Z : ZeroConfig) (T : ℝ) (P : Params) {A B ε : ℝ}
    (hL : 0 ≤ P.L T) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hε : 0 ≤ ε) (hA0 : 0 ≤ A) (hA6 : A ≤ 6 / 5) (hB : 0 ≤ B)
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      A ≤ sextupleEnergy g + B * sextupleSpan g)
    (hclose : ∀ {n : ℕ} (hn : n + 1 = sInterior Z T P)
      (r : Offset) (q : Fin (offsetBlockCount n r)) (i j : Fin 6), i < j →
      ‖interiorPrincipalBlock Z T P hn r q i j -
          (sextupleGram
            (packedBlockGaps (interiorGaps Z T P hn) r q) i j : ℂ)‖ ≤ ε)
    (hideal : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      ∀ i j : Fin 6, i < j → |sextupleGram g i j| ≤ 1) :
    A / 6 * ((sInterior Z T P : ℝ) - 10)
        - 5 * B / 6 * totalGap (adjacentGap Z T P)
        - 10 * (sInterior Z T P : ℝ) * ε ≤
      ZeroSide.simpleSextuplePenalty Z T P := by
  apply simpleSextuplePenalty_packing_of_column_bound Z T P hL hε hA0 hA6 hB
    (simpleZeroColumns_normSq_le_one Z T P hPois hc)
    hcertificate hclose hideal

/-- Poisson-normalized ordered-entry specialization. -/
theorem simpleSextuplePenalty_packing_of_ordered_entry_close_poisson
    (Z : ZeroConfig) (T : ℝ) (P : Params) {A B ε : ℝ}
    (hL : 0 ≤ P.L T) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hε : 0 ≤ ε) (hA0 : 0 ≤ A) (hA6 : A ≤ 6 / 5) (hB : 0 ≤ B)
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      A ≤ sextupleEnergy g + B * sextupleSpan g)
    (hclose : ∀ i j : Fin (sInterior Z T P),
      ‖ZeroSide.simpleZeroGram Z T P
          (interiorGramEmbedding Z T P i)
          (interiorGramEmbedding Z T P j) -
        (mtKernel (P.L T *
          (orderedOrdinate Z T P i - orderedOrdinate Z T P j)) : ℂ)‖ ≤ ε)
    (hkernel : ∀ x : ℝ, |mtKernel x| ≤ 1) :
    A / 6 * ((sInterior Z T P : ℝ) - 10)
        - 5 * B / 6 * totalGap (adjacentGap Z T P)
        - 10 * (sInterior Z T P : ℝ) * ε ≤
      ZeroSide.simpleSextuplePenalty Z T P := by
  exact simpleSextuplePenalty_packing_of_ordered_entry_close
    Z T P hL hε hA0 hA6 hB
    (simpleZeroColumns_normSq_le_one Z T P hPois hc)
    hcertificate hclose hkernel

end Sextuple
end ThmD
end Zeta23

end
