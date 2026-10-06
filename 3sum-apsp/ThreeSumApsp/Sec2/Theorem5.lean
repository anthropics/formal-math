/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Theorem5.Equation6

/-!
# Section 2.4.4: the algorithm of Theorem 5, its correctness and its three totals

The algorithm encodes the input arrays of all bands and then runs `Pruned(W_T)` on every tile `T`
with `W_T ≠ ∅`, where `W_T` is the set of the output strings of the wanted positions in `T`.

* Correctness (`Theorem5.correctness`): by Lemmas 10 and 7 the run on a tile returns the output of
  `Full` at the strings of `W_T`, and by Lemma 9, through the tiling, that output is the entry of
  `XY`.
* The encodings have `O(N² / D^{1/18})` entries in all, by equation (6)
  (`encodings_total_le`).
* The runs visit `O(N² / D^{1/18})` leaves in all (`Theorem5.total_leaves`): sum the second
  inequality of Lemma 11 over the tiles (`sum_card_Leaves_le`), with `∑_T |W_T| ≤ |W|`
  (`sum_card_wantedStrings_le`) and `∑_T M ≤ 4N²` (`sum_M_le`).
* The sets passed to the calls have total size at most `L + 1` times that, by Lemma 10
  (`Theorem5.total_sets`; no later proof uses this).
-/

public section

open Finset

namespace ThreeSumApsp

/-- Section 2.4.4: "Each wanted position (I, J) ∈ W lies in one tile T": the tile of a position is
one of the tiles. -/
theorem tile_mem_tiles {L m N : ℕ} (hmL : m ≤ L) (I J : Fin N) :
    (bandOf L m I, bandOf L m J) ∈ tiles L m N :=
  mem_product.mpr ⟨mem_range.mpr (bandOf_lt_numBands hmL N I I.2),
    mem_range.mpr (bandOf_lt_numBands hmL N J J.2)⟩

/-- Section 2.4.4: a wanted position "is indexed by one output string of T": its output string is in
the set `W_T` of its tile. -/
theorem outStrOfPos_mem_wantedStrings {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N))
    {I J : Fin N} (hIJ : (I, J) ∈ W) :
    outStrOfPos lay I J ∈ wantedStrings lay W (bandOf L m I) (bandOf L m J) :=
  mem_image.mpr ⟨(I, J), mem_filter.mpr ⟨hIJ, rfl, rfl⟩, rfl⟩

/-- Section 2.4.3: the sets passed to `Pruned` "consist only of […] output strings of length L whose
inner sets […] have exactly m elements". -/
theorem card_innerSetO_of_mem_wantedStrings {L m N : ℕ} (lay : Layout L m)
    (W : Finset (Fin N × Fin N)) (β β' : ℕ) (w : OutStr L) (hw : w ∈ wantedStrings lay W β β') :
    (innerSetO w).card = m := by
  obtain ⟨IJ, -, rfl⟩ := mem_image.mp hw
  exact card_innerSetO_outStrOfPos lay IJ.1 IJ.2

/-- **Proof of Theorem 5**, correctness of the algorithm.  "for each tile T with W_T ≠ ∅,
we run Pruned(W_T), and report, for each (I, J) ∈ W, the value at its output string. This is correct
by Lemmas 9 and 10." The run on the tile of `(I, J)` reads the encodings of the input arrays of its
row band and its column band.  This holds for all `m ≤ L`. -/
theorem Theorem5.correctness {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (W : Finset (Fin N × Fin N)) (I J : Fin N)
    (hIJ : (I, J) ∈ W) :
    Pruned L (encodingL (bandArrayL lay X (bandOf L m I)))
        (encodingR (bandArrayR lay Y (bandOf L m J)))
        (wantedStrings lay W (bandOf L m I) (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  -- Lemma 10, with Lemma 7: `Pruned` returns the output of `Full` restricted to the set passed to
  -- it.
  rw [Pruned_eq_restrictTo_Full, restrictTo_of_mem (outStrOfPos_mem_wantedStrings lay W hIJ)]
  -- Lemma 9, through the tiling of Section 2.3.4.
  exact Full_bandArray_eq_mul lay X Y I J

/-- Theorem 5 and Section 2.4.4: "|W| ≤ N²/√D = 2^{-m} N²".  In the statements below this
hypothesis is written without a square root, as `|W| · 2^m ≤ N²`. -/
theorem le_sq_div_sqrt_D_iff (m N w : ℕ) :
    (w : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (D m) ↔ w * 2 ^ m ≤ N ^ 2 := by
  rw [← two_pow_eq_sqrt_D, le_div_iff₀ (by positivity)]
  exact_mod_cast Iff.rfl

/-- The number of bands times `N₀` is at most the padded size, because `K₀ ≥ 1`. -/
private theorem numBands_mul_N0_le {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    numBands L m N * N0 L m ≤ padN L m N :=
  Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (K0_pos hmL))

/-- Section 2.4.4: "By (6), the encodings cost (2N/K₀N₀) · O(10^L) = O(2^{-m/9} N²) operations": the
encodings of the input arrays of all row bands and all column bands have at most `4 N² / D^{1/18}`
entries in all.  Here `N` is the size of the input, which the padding at most doubles. -/
theorem encodings_total_le (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    ((2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ)
      ≤ 4 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  have hbands : (numBands (19 * m) m N : ℝ) * N0 (19 * m) m ≤ 2 * N := by
    exact_mod_cast (numBands_mul_N0_le (by omega) N).trans (padN_le_two_mul_of_D_pow_le m N hN)
  have heq6 : (10 : ℝ) ^ (19 * m) ≤ saving m * N * N0 (19 * m) m := eq_6 m N hN
  have hc := saving_pos m
  rw [← saving_eq_D_rpow]
  push_cast
  calc 2 * (numBands (19 * m) m N : ℝ) * 10 ^ (19 * m)
      ≤ 2 * numBands (19 * m) m N * (saving m * N * N0 (19 * m) m) := by gcongr
    _ = 2 * saving m * (N * (numBands (19 * m) m N * N0 (19 * m) m)) := by ring
    _ ≤ 2 * saving m * (N * (2 * N)) := by gcongr
    _ = 4 * saving m * (N : ℝ) ^ 2 := by ring

/-- Section 2.4.4: "Each position of W lands in one set W_T, so ∑_T |W_T| ≤ |W|". -/
theorem sum_card_wantedStrings_le {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N)) :
    ∑ T ∈ tiles L m N, (wantedStrings lay W T.1 T.2).card ≤ W.card := by
  have hmap : ∀ IJ ∈ W, (bandOf L m IJ.1, bandOf L m IJ.2) ∈ tiles L m N := fun IJ _ =>
    tile_mem_tiles lay.hmL IJ.1 IJ.2
  rw [card_eq_sum_card_fiberwise hmap]
  refine sum_le_sum fun T _ => ?_
  refine card_image_le.trans (le_of_eq ?_)
  congr 1
  refine filter_congr fun IJ _ => ?_
  exact (Prod.ext_iff (x := (bandOf L m IJ.1, bandOf L m IJ.2)) (y := T)).symm

/-- Section 2.4.4: "there are at most 4N²/M tiles, so ∑_T M ≤ 4N²", where `N` is the padded size. -/
theorem sum_M_le (L m N : ℕ) : ∑ _T ∈ tiles L m N, M L m ≤ 4 * padN L m N ^ 2 := by
  rw [sum_const, smul_eq_mul]
  exact card_tiles_mul_M_le L m N

/-- Section 2.4.4, the display: "by Lemma 11 summed over the tiles",
`∑_T |Leaves(W_T)| ≤ 2^{-m/9} (2^m |W| + 2 ∑_T M)`. -/
theorem sum_card_Leaves_le {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N)) :
    ((∑ T ∈ tiles (19 * m) m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ saving m * ((2 : ℝ) ^ m * (W.card : ℝ)
          + 2 * ((∑ _T ∈ tiles (19 * m) m N, M (19 * m) m : ℕ) : ℝ)) := by
  have hc := saving_pos m
  have hsum : ((∑ T ∈ tiles (19 * m) m N, (wantedStrings lay W T.1 T.2).card : ℕ) : ℝ)
      ≤ (W.card : ℝ) := by
    exact_mod_cast sum_card_wantedStrings_le lay W
  push_cast at hsum ⊢
  calc ∑ T ∈ tiles (19 * m) m N, ((Leaves (wantedStrings lay W T.1 T.2)).card : ℝ)
      ≤ ∑ T ∈ tiles (19 * m) m N, saving m
          * ((2 : ℝ) ^ m * ((wantedStrings lay W T.1 T.2).card : ℝ) + 2 * (M (19 * m) m : ℝ)) :=
        sum_le_sum fun T _ =>
          Lemma11.second_inequality _ (card_innerSetO_of_mem_wantedStrings lay W T.1 T.2)
    _ = saving m
          * ((2 : ℝ) ^ m * ∑ T ∈ tiles (19 * m) m N, ((wantedStrings lay W T.1 T.2).card : ℝ)
              + 2 * ∑ _T ∈ tiles (19 * m) m N, (M (19 * m) m : ℝ)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := by gcongr

/-- **Proof of Theorem 5**, the number of leaves in terms of the `N` and `D` of the theorem (`N` is
the size of the input, not the padded size).  Since `N ≥ D^18 ≥ K₀ N₀`, the padding at most doubles
`N`, so `2^m |W| + 2 ∑_T M ≤ N² + 32 N²`. -/
theorem Theorem5.total_leaves {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N))
    (hN : D m ^ 18 ≤ N) (hW : W.card * 2 ^ m ≤ N ^ 2) :
    ((∑ T ∈ tiles (19 * m) m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ 33 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  have hc := saving_pos m
  have hWN : (2 : ℝ) ^ m * (W.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    rw [mul_comm]
    exact_mod_cast hW
  have hM : ((∑ _T ∈ tiles (19 * m) m N, M (19 * m) m : ℕ) : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    have hpad := Nat.pow_le_pow_left (padN_le_two_mul_of_D_pow_le m N hN) 2
    exact_mod_cast (sum_M_le (19 * m) m N).trans (by linarith)
  refine (sum_card_Leaves_le lay W).trans ?_
  rw [← saving_eq_D_rpow]
  calc saving m
          * ((2 : ℝ) ^ m * (W.card : ℝ) + 2 * ((∑ _T ∈ tiles (19 * m) m N, M (19 * m) m : ℕ) : ℝ))
      ≤ saving m * ((N : ℝ) ^ 2 + 2 * (16 * (N : ℝ) ^ 2)) := by gcongr
    _ = 33 * saving m * (N : ℝ) ^ 2 := by ring

/-- Lemma 10 summed over the tiles: the total size of the sets handled by the pruned recursions is
at most `L + 1` times the total number of leaves. -/
private theorem sum_totalSize_le {m N : ℕ} (lay : Layout (19 * m) m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (W : Finset (Fin N × Fin N)) :
    ((∑ T ∈ tiles (19 * m) m N,
        Pruned.totalSize (encodingL (bandArrayL lay X T.1)) (encodingR (bandArrayR lay Y T.2))
          (wantedStrings lay W T.1 T.2) : ℕ) : ℝ)
      ≤ ((19 * m + 1 : ℕ) : ℝ)
        * ((∑ T ∈ tiles (19 * m) m N, (Leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ) := by
  have h : ∑ T ∈ tiles (19 * m) m N,
        Pruned.totalSize (encodingL (bandArrayL lay X T.1)) (encodingR (bandArrayR lay Y T.2))
          (wantedStrings lay W T.1 T.2)
      ≤ (19 * m + 1) * ∑ T ∈ tiles (19 * m) m N, (Leaves (wantedStrings lay W T.1 T.2)).card := by
    rw [mul_sum]
    exact sum_le_sum fun T _ => Lemma10.total_size _ _ _
  exact_mod_cast h

/-- **Proof of Theorem 5**, the total size of the sets, in the `N` and `D` of the theorem. -/
theorem Theorem5.total_sets {m N : ℕ} (lay : Layout (19 * m) m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (W : Finset (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    ((∑ T ∈ tiles (19 * m) m N,
        Pruned.totalSize (encodingL (bandArrayL lay X T.1)) (encodingR (bandArrayR lay Y T.2))
          (wantedStrings lay W T.1 T.2) : ℕ) : ℝ)
      ≤ ((19 * m + 1 : ℕ) : ℝ) * (33 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) :=
  (sum_totalSize_le lay X Y W).trans
    (mul_le_mul_of_nonneg_left (Theorem5.total_leaves lay W hN hW) (Nat.cast_nonneg _))

end ThreeSumApsp
