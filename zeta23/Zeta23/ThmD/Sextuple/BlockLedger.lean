/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Combinatorics.Pigeonhole
import Zeta23.LinAlg.SextupleBlockPinching

/-!
# The finite six-offset sextuple ledger

A list of `n` consecutive gaps has `n + 1` ordered points.  For each residue
`r : Fin 6`, this file takes the complete six-point blocks beginning at
`r, r+6, r+12, ...`.  Every block contains its five internal adjacent gaps.
Across the six offsets, a fixed adjacent gap is internal at most five times.
This gives an exact finite span bound and an explicit ten-point boundary loss.

The final algebra is independent of how block penalties are constructed.
`GlobalPenaltyDominatesBlocks` names the spectral pinching input.  The theorem
`globalPenaltyDominatesBlocks_of_coreEmbedding` constructs the needed
orthonormal union of principal-block eigenbases inside any ambient coordinate
type.  A lower-level unitary-witness wrapper is also retained.
-/

noncomputable section

open Finset

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace BlockLedger

/-- One of the six translates of the consecutive-sextuple partition. -/
abbrev Offset := Fin 6

/-- Number of complete six-point blocks of offset `r` in a list of `n` gaps. -/
def offsetBlockCount (n : ℕ) (r : Offset) : ℕ :=
  (n + 1 - r) / 6

/-- The first point index in block number `q` of offset `r`. -/
def blockStart (r : Offset) (q : ℕ) : ℕ :=
  r + 6 * q

/-- The `j`-th point of a complete offset block. -/
def blockPointIndex {n : ℕ} (r : Offset)
    (q : Fin (offsetBlockCount n r)) (j : Fin 6) : Fin (n + 1) :=
  ⟨blockStart r q + j, by
    have hq := q.isLt
    have hr := r.isLt
    have hj := j.isLt
    simp only [offsetBlockCount, blockStart] at hq ⊢
    omega⟩

/-- The `j`-th internal adjacent gap of a complete offset block. -/
def blockGapIndex {n : ℕ} (r : Offset)
    (q : Fin (offsetBlockCount n r)) (j : Fin 5) : Fin n :=
  ⟨blockStart r q + j, by
    have hq := q.isLt
    have hr := r.isLt
    have hj := j.isLt
    simp only [offsetBlockCount, blockStart] at hq ⊢
    omega⟩

@[simp] lemma blockPointIndex_val {n : ℕ} (r : Offset)
    (q : Fin (offsetBlockCount n r)) (j : Fin 6) :
    (blockPointIndex r q j).val = blockStart r q + j := rfl

@[simp] lemma blockGapIndex_val {n : ℕ} (r : Offset)
    (q : Fin (offsetBlockCount n r)) (j : Fin 5) :
    (blockGapIndex r q j).val = blockStart r q + j := rfl

/-- Within one offset, the pairs `(block, internal position)` give distinct gaps. -/
lemma blockGapIndex_injective {n : ℕ} (r : Offset) :
    Function.Injective
      (fun x : Fin (offsetBlockCount n r) × Fin 5 => blockGapIndex r x.1 x.2) := by
  rintro ⟨q, j⟩ ⟨q', j'⟩ h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [blockGapIndex_val, blockStart] at hv
  have hqv : q.val = q'.val := by omega
  have hjv : j.val = j'.val := by omega
  exact Prod.ext (Fin.ext hqv) (Fin.ext hjv)

/-- The complete six-point blocks of one offset are pairwise disjoint. -/
lemma blockPointIndex_injective {n : ℕ} (r : Offset) :
    Function.Injective
      (fun x : Fin (offsetBlockCount n r) × Fin 6 => blockPointIndex r x.1 x.2) := by
  rintro ⟨q, j⟩ ⟨q', j'⟩ h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [blockPointIndex_val, blockStart] at hv
  have hqv : q.val = q'.val := by omega
  have hjv : j.val = j'.val := by omega
  exact Prod.ext (Fin.ext hqv) (Fin.ext hjv)

/-- The combined coordinate embedding of all complete blocks of one offset. -/
def blockPointEmbedding {n : ℕ} (r : Offset) :
    (Fin (offsetBlockCount n r) × Fin 6) ↪ Fin (n + 1) where
  toFun x := blockPointIndex r x.1 x.2
  inj' := blockPointIndex_injective r


/-- The complete blocks of offset `r`, embedded through a distinguished core
of an arbitrary ambient coordinate type. -/
def coreBlockPointEmbedding {n : ℕ} {ι : Type*}
    (coreEmbedding : Fin (n + 1) ↪ ι) (r : Offset) :
    (Fin (offsetBlockCount n r) × Fin 6) ↪ ι :=
  (blockPointEmbedding r).trans coreEmbedding

/-- A six-by-six principal block of an ambient matrix, selected through the
canonical offset packing and the distinguished core embedding. -/
def corePrincipalBlock {n : ℕ} {ι 𝕜 : Type*}
    (M : Matrix ι ι 𝕜) (coreEmbedding : Fin (n + 1) ↪ ι)
    (r : Offset) (q : Fin (offsetBlockCount n r)) : Matrix (Fin 6) (Fin 6) 𝕜 :=
  RHLinalg.SextupleBlockPinching.principalBlock M
    (coreBlockPointEmbedding coreEmbedding r) q

lemma corePrincipalBlock_isHermitian {n : ℕ} {ι 𝕜 : Type*}
    [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (coreEmbedding : Fin (n + 1) ↪ ι) (r : Offset)
    (q : Fin (offsetBlockCount n r)) :
    (corePrincipalBlock M coreEmbedding r q).IsHermitian :=
  RHLinalg.SextupleBlockPinching.principalBlock_isHermitian hM
    (coreBlockPointEmbedding coreEmbedding r) q

/-- Sum of the convex sextuple penalty over one embedded principal block. -/
def corePrincipalBlockPenalty {n : ℕ} {ι 𝕜 : Type*}
    [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (coreEmbedding : Fin (n + 1) ↪ ι) (r : Offset)
    (q : Fin (offsetBlockCount n r)) : ℝ :=
  ∑ j : Fin 6, RHLinalg.sextuplePenalty
    ((corePrincipalBlock_isHermitian hM coreEmbedding r q).eigenvalues j)

/-- The set of all adjacent gaps internal to complete blocks of one offset. -/
def offsetGapIndices (n : ℕ) (r : Offset) : Finset (Fin n) :=
  Finset.univ.image
    (fun x : Fin (offsetBlockCount n r) × Fin 5 => blockGapIndex r x.1 x.2)

/-- Span of one complete six-point block. -/
def blockSpan {n : ℕ} (g : Fin n → ℝ) (r : Offset)
    (q : Fin (offsetBlockCount n r)) : ℝ :=
  ∑ j : Fin 5, g (blockGapIndex r q j)

/-- Sum of all complete-block spans in one offset. -/
def offsetSpan {n : ℕ} (g : Fin n → ℝ) (r : Offset) : ℝ :=
  ∑ i ∈ offsetGapIndices n r, g i

/-- Total length of the finite ordered gap list. -/
def totalGap {n : ℕ} (g : Fin n → ℝ) : ℝ :=
  ∑ i, g i

/-- The set-based offset span is exactly the sum of its disjoint block spans. -/
lemma offsetSpan_eq_sum_blockSpan {n : ℕ} (g : Fin n → ℝ) (r : Offset) :
    offsetSpan g r = ∑ q : Fin (offsetBlockCount n r), blockSpan g r q := by
  classical
  rw [offsetSpan, offsetGapIndices, Finset.sum_image]
  · rw [Fintype.sum_prod_type]
    rfl
  · intro x _ y _ hxy
    exact blockGapIndex_injective r hxy

/-- The unique offset in which gap `i` would lie between two consecutive blocks. -/
def excludedOffset {n : ℕ} (i : Fin n) : Offset :=
  ⟨(i + 1) % 6, Nat.mod_lt _ (by norm_num)⟩

/-- An internal gap of an offset block is not assigned that offset as its
between-block residue. -/
lemma excludedOffset_blockGapIndex_ne {n : ℕ} (r : Offset)
    (q : Fin (offsetBlockCount n r)) (j : Fin 5) :
    excludedOffset (blockGapIndex r q j) ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  have hr := r.isLt
  have hj := j.isLt
  simp only [excludedOffset, blockGapIndex_val, blockStart] at hv
  omega

/-- Gaps that can possibly be internal to the offset `r`, after deleting the
one between-block residue. -/
def eligibleGapIndices (n : ℕ) (r : Offset) : Finset (Fin n) :=
  Finset.univ.filter fun i => excludedOffset i ≠ r

lemma offsetGapIndices_subset_eligible (n : ℕ) (r : Offset) :
    offsetGapIndices n r ⊆ eligibleGapIndices n r := by
  classical
  intro i hi
  rw [offsetGapIndices, Finset.mem_image] at hi
  obtain ⟨⟨q, j⟩, -, rfl⟩ := hi
  simp [eligibleGapIndices, excludedOffset_blockGapIndex_ne]

/-- The offsets whose complete blocks contain a fixed adjacent gap. -/
def gapOffsets {n : ℕ} (i : Fin n) : Finset Offset :=
  Finset.univ.filter fun r => i ∈ offsetGapIndices n r

/-- Every adjacent gap is internal to complete blocks in at most five of the
six offsets. -/
theorem card_gapOffsets_le_five {n : ℕ} (i : Fin n) :
    (gapOffsets i).card ≤ 5 := by
  classical
  have hsubset : gapOffsets i ⊆ Finset.univ.erase (excludedOffset i) := by
    intro r hr
    have hri : i ∈ offsetGapIndices n r := by
      simpa [gapOffsets] using hr
    have helig := offsetGapIndices_subset_eligible n r hri
    have hne : excludedOffset i ≠ r := by
      simpa [eligibleGapIndices] using helig
    simp [hne.symm]
  calc
    (gapOffsets i).card ≤ (Finset.univ.erase (excludedOffset i)).card :=
      Finset.card_le_card hsubset
    _ = 5 := by simp

/-- A single offset uses no more than all gaps except its boundary residue. -/
lemma offsetSpan_le_eligible {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) (r : Offset) :
    offsetSpan g r ≤ ∑ i ∈ eligibleGapIndices n r, g i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (offsetGapIndices_subset_eligible n r) fun i _ _ => hg i

private lemma sum_except_one (e : Offset) (x : ℝ) :
    (∑ r : Offset, if e ≠ r then x else 0) = 5 * x := by
  classical
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun r : Offset => e ≠ r) = Finset.univ.erase e := by
    ext r
    simp [eq_comm]
  rw [hfilter]
  simp [mul_comm]

/-- Across all six offsets, every adjacent gap is counted at most five times. -/
theorem sum_offsetSpan_le_five_total {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    (∑ r : Offset, offsetSpan g r) ≤ 5 * totalGap g := by
  calc
    (∑ r : Offset, offsetSpan g r)
        ≤ ∑ r : Offset, ∑ i ∈ eligibleGapIndices n r, g i :=
      Finset.sum_le_sum fun r _ => offsetSpan_le_eligible g hg r
    _ = ∑ r : Offset, ∑ i : Fin n,
          if excludedOffset i ≠ r then g i else 0 := by
      simp [eligibleGapIndices, Finset.sum_filter]
    _ = ∑ i : Fin n, ∑ r : Offset,
          if excludedOffset i ≠ r then g i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, 5 * g i := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_except_one (excludedOffset i) (g i)
    _ = 5 * totalGap g := by
      simp [totalGap, Finset.mul_sum]

/-- Some offset has complete-block span at most five sixths of the total span. -/
theorem exists_offsetSpan_le_five_sixths {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    ∃ r : Offset, offsetSpan g r ≤ (5 / 6 : ℝ) * totalGap g := by
  have hsum := sum_offsetSpan_le_five_total g hg
  have havg : (∑ r : Offset, offsetSpan g r)
      ≤ Fintype.card Offset • ((5 / 6 : ℝ) * totalGap g) := by
    norm_num [Fintype.card_fin, nsmul_eq_mul]
    linarith
  obtain ⟨r, hr⟩ := Fintype.exists_sum_fiber_le_of_sum_le_nsmul
    (f := id) (w := fun r : Offset => offsetSpan g r) havg
  refine ⟨r, ?_⟩
  have hsingle : (∑ x : Offset with id x = r, offsetSpan g x) = offsetSpan g r := by
    rw [Finset.sum_eq_single r]
    · intro b hb hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id_eq] at hb
      exact (hne hb).elim
    · simp
  rw [hsingle] at hr
  exact hr

/-- Every offset loses at most ten boundary points relative to six times its
number of complete blocks.  This is the explicit finite `O(1)` term. -/
lemma pointCount_le_six_mul_blockCount_add_ten (n : ℕ) (r : Offset) :
    n + 1 ≤ 6 * offsetBlockCount n r + 10 := by
  have hr := r.isLt
  simp only [offsetBlockCount]
  omega

/-- Named finite hypothesis for the missing convex spectral pinching step. -/
def GlobalPenaltyDominatesBlocks {n : ℕ}
    (blockPenalty : (r : Offset) → Fin (offsetBlockCount n r) → ℝ)
    (globalPenalty : ℝ) : Prop :=
  ∀ r, (∑ q, blockPenalty r q) ≤ globalPenalty

/-- Automatic spectral pinching for the canonical complete blocks inside a
finite ambient matrix.  The block coordinates are the composites
`coreEmbedding ∘ blockPointEmbedding r`; the block eigenbases, their
zero-extensions, and the ambient orthonormal completion are constructed
internally. -/
theorem globalPenaltyDominatesBlocks_of_coreEmbedding
    {n : ℕ} {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (coreEmbedding : Fin (n + 1) ↪ ι) :
    GlobalPenaltyDominatesBlocks
      (corePrincipalBlockPenalty hM coreEmbedding)
      (∑ i, RHLinalg.sextuplePenalty (hM.eigenvalues i)) := by
  intro r
  simpa only [corePrincipalBlockPenalty, corePrincipalBlock] using
    (RHLinalg.SextupleBlockPinching.sum_sum_sextuplePenalty_principalBlocks_le_spectrum hM
        (coreBlockPointEmbedding coreEmbedding r))

/-- Matrix-functional form of automatic block pinching through a core
embedding. -/
theorem globalPenaltyDominatesBlocks_of_coreEmbedding_specMap
    {n : ℕ} {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    (coreEmbedding : Fin (n + 1) ↪ ι) :
    GlobalPenaltyDominatesBlocks
      (corePrincipalBlockPenalty hM coreEmbedding)
      (RHLinalg.rtrace (RHLinalg.specMap hM RHLinalg.sextuplePenalty)) := by
  intro r
  simpa only [corePrincipalBlockPenalty, corePrincipalBlock] using
    (RHLinalg.SextupleBlockPinching.sum_sum_sextuplePenalty_principalBlocks_le_specMap hM
        (coreBlockPointEmbedding coreEmbedding r))

/-- Specialization to a matrix indexed by the core points themselves. -/
theorem globalPenaltyDominatesCanonicalBlocks
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜} (hM : M.IsHermitian) :
    GlobalPenaltyDominatesBlocks
      (corePrincipalBlockPenalty hM (Function.Embedding.refl (Fin (n + 1))))
      (∑ i, RHLinalg.sextuplePenalty (hM.eigenvalues i)) :=
  globalPenaltyDominatesBlocks_of_coreEmbedding hM
    (Function.Embedding.refl (Fin (n + 1)))

/-- Witness-level convex spectral pinching for the concrete complete blocks.
The columns selected by `blockPointEmbedding r` are intended to be the union
of the six-dimensional principal-block eigenbases; `U r` completes them to an
ambient unitary. -/
theorem globalPenaltyDominatesBlocks_of_unitary_witness
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜} (hM : M.IsHermitian)
    (U : Offset → Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (hU : ∀ r, U r ∈ Matrix.unitaryGroup (Fin (n + 1)) 𝕜)
    (ev : (r : Offset) → Fin (offsetBlockCount n r) × Fin 6 → ℝ)
    (hdiag : ∀ r k, ev r k =
      RCLike.re ((star (U r) * M * U r)
        (blockPointEmbedding r k) (blockPointEmbedding r k))) :
    GlobalPenaltyDominatesBlocks
      (fun r q => ∑ j : Fin 6, RHLinalg.sextuplePenalty (ev r (q, j)))
      (RHLinalg.rtrace (RHLinalg.specMap hM RHLinalg.sextuplePenalty)) := by
  intro r
  have h := RHLinalg.sum_sextuplePenalty_le_specMap_of_unitary_diagonal_embedding
    hM (hU r) (blockPointEmbedding r) (ev r) (hdiag r)
  simpa only [Fintype.sum_prod_type] using h

/-- The pointwise affine certificate on every complete sextuple. -/
def EveryBlockSatisfiesAffineBound {n : ℕ} (g : Fin n → ℝ)
    (A B : ℝ)
    (blockPenalty : (r : Offset) → Fin (offsetBlockCount n r) → ℝ) : Prop :=
  ∀ r q, A ≤ blockPenalty r q + B * blockSpan g r q

/-- Summing the pointwise affine certificate within a fixed offset. -/
lemma sum_block_affine_bound {n : ℕ} (g : Fin n → ℝ) (A B : ℝ)
    (blockPenalty : (r : Offset) → Fin (offsetBlockCount n r) → ℝ)
    (hblock : EveryBlockSatisfiesAffineBound g A B blockPenalty) (r : Offset) :
    A * (offsetBlockCount n r : ℝ)
      ≤ (∑ q, blockPenalty r q) + B * offsetSpan g r := by
  have hsum := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset
      (Fin (offsetBlockCount n r)))) => hblock r q
  simp only [sum_add_distrib, ← Finset.mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← offsetSpan_eq_sum_blockSpan] at hsum
  simpa [mul_comm] using hsum

/-- Exact finite ledger: one offset simultaneously has the five-sixths span
bound and the corresponding global-penalty lower bound. -/
theorem exists_offset_with_penalty_lower {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) {A B globalPenalty : ℝ}
    {blockPenalty : (r : Offset) → Fin (offsetBlockCount n r) → ℝ}
    (hpinch : GlobalPenaltyDominatesBlocks blockPenalty globalPenalty)
    (hblock : EveryBlockSatisfiesAffineBound g A B blockPenalty) :
    ∃ r : Offset,
      offsetSpan g r ≤ (5 / 6 : ℝ) * totalGap g ∧
      A * (offsetBlockCount n r : ℝ) - B * offsetSpan g r ≤ globalPenalty := by
  obtain ⟨r, hr⟩ := exists_offsetSpan_le_five_sixths g hg
  refine ⟨r, hr, ?_⟩
  have haff := sum_block_affine_bound g A B blockPenalty hblock r
  have hp := hpinch r
  linarith

/-- Explicit finite form of the complete-block ledger.  The boundary loss is
exactly `10*A/6`; it is the finite representative of the later `O(1)=o(N)`
leftover. -/
theorem globalPenalty_lower_explicit {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) {A B globalPenalty : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    {blockPenalty : (r : Offset) → Fin (offsetBlockCount n r) → ℝ}
    (hpinch : GlobalPenaltyDominatesBlocks blockPenalty globalPenalty)
    (hblock : EveryBlockSatisfiesAffineBound g A B blockPenalty) :
    A / 6 * (((n + 1 : ℕ) : ℝ) - 10)
        - 5 * B / 6 * totalGap g ≤ globalPenalty := by
  obtain ⟨r, hspan, hglobal⟩ :=
    exists_offset_with_penalty_lower g hg hpinch hblock
  have hcountNat := pointCount_le_six_mul_blockCount_add_ten n r
  have hcountCast : ((n + 1 : ℕ) : ℝ)
      ≤ 6 * (offsetBlockCount n r : ℝ) + 10 := by
    exact_mod_cast hcountNat
  have hcount : ((n + 1 : ℕ) : ℝ) - 10
      ≤ 6 * (offsetBlockCount n r : ℝ) := by
    linarith
  have hAcount : A / 6 * (((n + 1 : ℕ) : ℝ) - 10)
      ≤ A * (offsetBlockCount n r : ℝ) := by
    nlinarith
  have hBspan : B * offsetSpan g r
      ≤ B * ((5 / 6 : ℝ) * totalGap g) :=
    mul_le_mul_of_nonneg_left hspan hB
  norm_num at hAcount ⊢
  nlinarith

end BlockLedger
end Sextuple
end ThmD
end Zeta23

end
