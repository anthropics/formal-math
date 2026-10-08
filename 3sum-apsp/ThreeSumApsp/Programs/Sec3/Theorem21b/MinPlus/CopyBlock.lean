/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Problems

/-!
# Copying a block of a matrix

A routine for the hosts of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
subCopy(s, h, src, r0, c0, dst) copies the h × h block with upper left corner (r0,
c0) of the s × s matrix at src (row major) to dst (row major), one row at a time, with the routine
copy.  The destination lies behind the matrix.

The specification is subCopy_meets: afterwards the list subMat s h r0 c0 L stands at dst, and no
other cell has changed.  The proof is a loop over the rows with the invariant SubCopy.Inv; that
row i of the block is a piece of row r0 + i of the matrix is SubCopy.row_eq.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace SubCopy

/-- The local variables of subCopy: the arguments s (Side), h (Block), src, r0, c0, dst; the row i;
and the result of copy, which is not used. -/
abbrev Side : ℕ := 0
@[inherit_doc Side] abbrev Block : ℕ := 1
@[inherit_doc Side] abbrev Source : ℕ := 2
@[inherit_doc Side] abbrev Row0 : ℕ := 3
@[inherit_doc Side] abbrev Col0 : ℕ := 4
@[inherit_doc Side] abbrev Dest : ℕ := 5
@[inherit_doc Side] abbrev Row : ℕ := 6
@[inherit_doc Side] abbrev Unused : ℕ := 7

end SubCopy

open SubCopy in
/-- subCopy(s, h, src, r0, c0, dst): for i < h, copy the h cells from src + (r0 + i) s + c0 to
dst + i h.  pCopy is the number of the procedure copy. -/
def subCopyBody (pCopy : ℕ) : Stmt :=
  .for Row (v Block) (
    .call pCopy [v Source +' (v Row0 +' v Row) *' v Side +' v Col0, v Dest +' v Row *' v Block,
      v Block] Unused)

/-- The number of steps of subCopy. -/
def subCopyTime (h : ℕ) : ℕ := h * (16 * h + 31) + 6

/-! ## The specification -/

namespace SubCopy

/-- Row i of the block is a piece of row r0 + i of the matrix. -/
theorem row_eq {μ : ℕ → ℤ} {s h src r0 c0 i j : ℕ} {L : List ℤ} (hL : Seg μ src L)
    (hlen : L.length = s * s) (hr : r0 + h ≤ s) (hc : c0 + h ≤ s) (hi : i < h) (hj : j < h) :
    μ (src + ((r0 + i) * s + c0) + j) = entry h (subMat s h r0 c0 L) i j := by
  have hidx : (r0 + i) * s + (c0 + j) < L.length :=
    hlen ▸ Nat.mul_add_lt_mul (by omega : r0 + i < s) (by omega : c0 + j < s)
  rw [entry_subMat hi hj, entry, List.getD_eq_getElem _ _ hidx, ← hL _ hidx]
  congr 1
  omega

/-- The state before row i is copied: the first i rows of the block B stand at dst, and no cell
outside the h² cells from dst has changed. -/
def Inv (μ : ℕ → ℤ) (s h src r0 c0 dst : ℕ) (B : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [s, h, src, r0, c0, dst, i, r], μ'⟩ ∧
    (∀ q < i * h, μ' (dst + q) = B.getD q 0) ∧ SameOutside μ μ' dst (h * h)

end SubCopy

open SubCopy in
/-- **subCopy** writes the block of the matrix L at src to dst and changes nothing else.  The block
lies within the matrix and the destination behind it (hplace); the destination lies within the
memory, and one more level of calls is allowed (hlim). -/
theorem subCopy_meets {pSub pCopy : ℕ} (hSub : P[pSub]? = some (subCopyBody pCopy))
    (hCopy : P[pCopy]? = some copyBody) {μ : ℕ → ℤ} {s src : ℕ} {L : List ℤ} (h r0 c0 dst : ℕ)
    (hL : Seg μ src L) (hlen : L.length = s * s)
    (hplace : r0 + h ≤ s ∧ c0 + h ≤ s ∧ src + s * s ≤ dst)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ dst + h * h ≤ lim.space ∧ d < lim.depth) :
    Meets lim P pSub d [(s : ℤ), h, src, r0, c0, dst] μ (subCopyTime h) fun _ μ' =>
      Seg μ' dst (subMat s h r0 c0 L) ∧ SameOutside μ μ' dst (h * h) := by
  obtain ⟨hr, hc, hsrc⟩ := hplace
  obtain ⟨hw, hdst, hd⟩ := hlim
  have hh : h ≤ h * h := Nat.le_mul_self h
  unfold subCopyTime
  -- for i < h
  refine .of_body hSub (Ends.for (Inv μ s h src r0 c0 dst (subMat s h r0 c0 L)) h (16 * h + 23)
    ?start ?round ?done ?bound)
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl,
      fun q hq => absurd hq (by omega), .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hrows, hrest⟩
    -- Row r0 + i of the matrix and row i of the block lie within their arrays.
    have hrowS : (r0 + i) * s + s ≤ s * s := Nat.mul_add_le_mul (by omega) le_rfl
    have hrowZ : 0 ≤ ((r0 : ℤ) + i) * s ∧ ((r0 : ℤ) + i) * s + s ≤ s * s := by
      exact_mod_cast And.intro (Nat.zero_le _) hrowS
    have hrowD : i * h + h ≤ h * h := Nat.mul_add_le_mul hi le_rfl
    -- copy(src + (r0 + i) s + c0, dst + i h, h)
    light_call (copy_meets hCopy (src := src + ((r0 + i) * s + c0)) (dst := dst + i * h)
      (n := h) hw (by omega) (by omega) (.inl (by omega))) with r' μ'' ⟨hcopy, hout⟩
    refine ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, fun q hq => ?_,
      hrest.trans (hout.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge q (i * h) with hq' | hq'
    · -- The earlier rows lie below dst + i h and have not been touched.
      exact (hout _ (.inl (by omega))).trans (hrows q hq')
    · -- Row i has just been copied from the matrix, which is as at the start.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hq'
      have hj : j < h := by rw [Nat.add_mul, Nat.one_mul] at hq; omega
      rw [← Nat.add_assoc, hcopy j hj, hrest _ (.inl (by omega)), row_eq hL hlen hr hc hi hj]
  case done =>
    rintro _ - ⟨r, μ', rfl, hrows, hrest⟩
    exact ⟨fun q hq => (hrows q (by simpa using hq)).trans (List.getD_eq_getElem _ _ hq), hrest⟩

end Light.Sec3
