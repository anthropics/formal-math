/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma9
public import ThreeSumApsp.Sec2.Tiling.Definitions

/-!
# The tiling of the `N × D × N` product

Section 2.3.4. One run of `Full` computes `K` products of shape `N₀ × D × N₀` (Lemma 9).
To multiply an `N × D` matrix `X` by a `D × N` matrix `Y`, cut `X` into row blocks and `Y` into
column blocks of size `N₀`, group the blocks into bands of `K₀ = ⌊√K⌋` blocks, and call a row band
together with a column band a tile. Each tile is one run of `Full`, on a `K₀ × K₀` grid of block
products.

* The numbers: `K₀² ≤ K ≤ 4 K₀²` (`K0_sq_le_K`, `K_le_four_mul_K0_sq`), padding `N ≥ K₀ N₀` to
  a multiple of `K₀ N₀` at most doubles it (`le_padN`, `padN_lt_add_bandSize`, `padN_le_two_mul`),
  and there are at most `4N²/M` tiles, where `N` is the padded size (`card_tiles_mul_M_le`).
* A table of `K₀²` distinct subsets of size `m` exists (`nonempty_layout`; no later proof uses
  this).
* One run computes all the block products of a tile (`Full_bandArray_eq_block_mul`, from Lemma 9),
  and the entry `(XY)[I, J]` is the output of the run on the tile of `(I, J)` at the output string
  of `(I, J)` (`Full_bandArray_eq_mul`).
* Different positions of a tile have different output strings (`outStrOfPos_injective`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The numbers -/

/-- Section 2.3.4: "K₀² ≤ K". -/
theorem K0_sq_le_K (L m : ℕ) : K0 L m ^ 2 ≤ K L m :=
  Nat.sqrt_le' _

/-- Section 2.3.4: "K₀ ≥ √K / 2", squared. -/
theorem K_le_four_mul_K0_sq (L m : ℕ) : K L m ≤ 4 * K0 L m ^ 2 := by
  have hlt : K L m < (K0 L m + 1) ^ 2 := Nat.lt_succ_sqrt' _
  rcases Nat.eq_zero_or_pos (K0 L m) with h0 | h0
  · rw [h0] at hlt ⊢
    omega
  · calc K L m ≤ (K0 L m + 1) ^ 2 := hlt.le
      _ ≤ (2 * K0 L m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * K0 L m ^ 2 := by ring

/-- A band has at least one row. -/
theorem bandSize_pos {L m : ℕ} (hmL : m ≤ L) : 0 < bandSize L m :=
  Nat.mul_pos (K0_pos hmL) (N0_pos L m)

/-- Section 2.3.4: "we first pad N to a multiple of K₀ N₀". -/
theorem bandSize_dvd_padN (L m N : ℕ) : bandSize L m ∣ padN L m N :=
  Dvd.intro_left _ rfl

/-- The padded size is at least `N`.

NOTE. `m ≤ L` is left implicit in the paper. For `m > L` there is no subset of size `m` and
`K₀ = 0`. -/
theorem le_padN {L m : ℕ} (hmL : m ≤ L) (N : ℕ) : N ≤ padN L m N := by
  have h := Nat.lt_div_mul_add (a := N + bandSize L m - 1) (bandSize_pos hmL)
  unfold padN numBands
  omega

/-- The padded size is the least multiple of `K₀ N₀` that is at least `N`: it is less than
`N + K₀ N₀`.

NOTE. `m ≤ L` is left implicit in the paper. -/
theorem padN_lt_add_bandSize {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    padN L m N < N + bandSize L m := by
  have h := Nat.div_mul_le_self (N + bandSize L m - 1) (bandSize L m)
  have hb := bandSize_pos hmL
  unfold padN numBands
  omega

/-- Section 2.3.4: the padding "at most doubles N since N ≥ K₀ N₀". -/
theorem padN_le_two_mul (L m N : ℕ) (hN : K0 L m * N0 L m ≤ N) : padN L m N ≤ 2 * N := by
  rcases Nat.lt_or_ge L m with hLm | hmL
  · -- for `m > L` there are no subsets, `K₀ = 0`, and the padded size is 0
    have hK : K0 L m = 0 := by simp [K0, K, Nat.choose_eq_zero_of_lt hLm]
    simp [padN, bandSize, hK]
  · have h := padN_lt_add_bandSize hmL N
    have hN' : bandSize L m ≤ N := hN
    omega

/-- The number of tiles is the square of the number of bands. -/
theorem card_tiles (L m N : ℕ) : (tiles L m N).card = numBands L m N ^ 2 := by
  simp [tiles, sq]

/-- Section 2.3.4: "there are (N / K₀N₀)² ≤ 4N²/M tiles", where `N` is the padded size.  The
inequality is multiplied out. -/
theorem card_tiles_mul_M_le (L m N : ℕ) : (tiles L m N).card * M L m ≤ 4 * padN L m N ^ 2 := by
  rw [card_tiles]
  calc numBands L m N ^ 2 * M L m
      = numBands L m N ^ 2 * N0 L m ^ 2 * K L m := by unfold M; ring
    _ ≤ numBands L m N ^ 2 * N0 L m ^ 2 * (4 * K0 L m ^ 2) :=
        Nat.mul_le_mul_left _ (K_le_four_mul_K0_sq L m)
    _ = 4 * padN L m N ^ 2 := by unfold padN bandSize; ring

/-! ### The table of subsets and the matrices of a tile -/

/-- Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m": this can be done.

NOTE.  `m ≤ L` is left implicit in the paper; it is a field of `Layout`. -/
theorem nonempty_layout {L m : ℕ} (hmL : m ≤ L) : Nonempty (Layout L m) := by
  have hcard : Fintype.card (Fin (K0 L m) × Fin (K0 L m))
      ≤ Fintype.card {Q : Finset (Fin L) // Q.card = m} := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype, card_subsets_eq_K, ← sq]
    exact K0_sq_le_K L m
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨{ hmL := hmL
           rowIdx := (Fintype.equivFinOfCardEq (card_outerStr L m)).symm
           colIdx := (Fintype.equivFinOfCardEq (card_outerStr L m)).symm
           innerIdx := (Fintype.equivFinOfCardEq (card_innerStr m)).symm
           table := fun gh => (e gh).1
           table_card := fun gh => (e gh).2
           table_injective := fun _ _ h => e.injective (Subtype.ext h) }⟩

/-- The subsets in the table are distinct, so a sum over the table that selects the subset of the
block product `gh` has one term. -/
private theorem sum_table_eq {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (∑ gh', if lay.table gh' = lay.table gh then F gh' else 0) = F gh := by
  simp [lay.table_injective.eq_iff]

/-- Section 2.3.4: "In a tile, let X_Q and Y_Q be the row block and the column block of the block
product with subset Q".  For `X_Q`: it is the `g`-th row block of the row band. -/
@[simp]
theorem bandFamilyL_table {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyL lay X β (lay.table (g, h)) = rowBlock lay X (β * K0 L m + g) :=
  sum_table_eq lay _ (g, h)

/-- The matrix `Y_Q` of the block product in position `(g, h)` is the `h`-th column block of the
column band. -/
@[simp]
theorem bandFamilyR_table {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyR lay Y β (lay.table (g, h)) = colBlock lay Y (β * K0 L m + h) :=
  sum_table_eq lay _ (g, h)

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `X_Q`. -/
theorem bandFamilyL_eq_zero {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyL lay X β Q = 0 :=
  sum_eq_zero fun gh _ => if_neg (hQ gh)

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `Y_Q`. -/
theorem bandFamilyR_eq_zero {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyR lay Y β Q = 0 :=
  sum_eq_zero fun gh _ => if_neg (hQ gh)

/-! ### One run of `Full` for each tile -/

/-- Section 2.3.4: "Then one run of Full computes all K₀² block products of the tile (Lemma 9)".
The tile is that of the row band `β` and the column band `β'`; the block product in position `(g,
h)` of its grid is the product of the row block `β K₀ + g` by the column block `β' K₀ + h`. -/
theorem Full_bandArray_eq_block_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β β' : ℕ)
    (g h : Fin (K0 L m)) (r c : OuterStr L m) :
    Full L (bandArrayL lay X β) (bandArrayR lay Y β')
        (outStrOf (lay.table (g, h)) (lay.table_card (g, h)) r c)
      = (rowBlock lay X (β * K0 L m + g) * colBlock lay Y (β' * K0 L m + h)) r c := by
  rw [bandArrayL, bandArrayR, Full_arrays_eq_mul, bandFamilyL_table, bandFamilyR_table]

/-- A row (or column) is recovered from its band, the position of its block in the band and its
position in the block. -/
private theorem position_decomp {L m : ℕ} (lay : Layout L m) (I : ℕ) :
    (bandOf L m I * K0 L m + (blockOf lay I : ℕ)) * N0 L m + (offsetOf L m I : ℕ) = I := by
  have hband : bandOf L m I = I / N0 L m / K0 L m := by
    rw [bandOf, bandSize, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have hblock : bandOf L m I * K0 L m + (blockOf lay I : ℕ) = I / N0 L m := by
    rw [hband]
    exact Nat.div_add_mod' _ _
  rw [hblock]
  exact Nat.div_add_mod' _ _

/-- Section 2.3.4: "and running it on every tile computes all of XY." The entry `(XY)[I, J]` is the
output of the run on the tile of `(I, J)` at the output string of `(I, J)`. -/
theorem Full_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Full L (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  unfold outStrOfPos
  rw [Full_bandArray_eq_block_mul, Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp lay.innerIdx]
  -- Both sides are sums over the `D` inner indices; the summands agree because row `I` is recovered
  -- from its band, block and place in the block, and likewise column `J`.
  refine sum_congr rfl fun k _ => ?_
  simp only [rowBlock, colBlock, Equiv.symm_apply_apply, position_decomp, padRows, padCols,
    I.isLt, J.isLt, dif_pos, Fin.eta]

/-- The entry `(XY)[I, J]` as a value of `Mult`, that is, as a sum over leaves (equation (2)). This
is the form in which Section 4 uses the tiling ("by (2) and Lemma 9, (X_Q Y_Q)[w] is the sum of the
products at the leaves contributing to w"). -/
theorem Mult_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Mult (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma7.returns_Mult]
  exact Full_bandArray_eq_mul lay X Y I J

/-- Every row and every column lies in one of the bands.

NOTE.  `m ≤ L` is left implicit in the paper. -/
theorem bandOf_lt_numBands {L m : ℕ} (hmL : m ≤ L) (N I : ℕ) (hI : I < N) :
    bandOf L m I < numBands L m N := by
  rw [bandOf, Nat.div_lt_iff_lt_mul (bandSize_pos hmL)]
  exact hI.trans_le (le_padN hmL N)

/-! ### The output string of a position -/

/-- Section 2.4.4: the inner set of the output string of a position is "the subset Q of the block
product containing (I, J)". -/
theorem innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    innerSetO (outStrOfPos lay I J) = lay.table (blockOf lay I, blockOf lay J) :=
  innerSetO_outStrOf _ _ _ _

/-- The inner set of the output string of a position has exactly `m` elements. -/
theorem card_innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    (innerSetO (outStrOfPos lay I J)).card = m :=
  innerSetO_outStrOfPos lay I J ▸ lay.table_card _

/-- Used implicitly in Section 2.4.4 ("is indexed by one output string of T", "report […] the value
at its output string"): different positions of the same tile have different output strings. -/
theorem outStrOfPos_injective {L m : ℕ} (lay : Layout L m) (I J I' J' : ℕ)
    (hI : bandOf L m I = bandOf L m I') (hJ : bandOf L m J = bandOf L m J')
    (h : outStrOfPos lay I J = outStrOfPos lay I' J') : I = I' ∧ J = J' := by
  -- The two strings have the same inner set, row and column; so the two positions lie in the same
  -- block product and at the same place in it.
  obtain ⟨hQ, hr, hc⟩ := outStrOf_inj.mp h
  obtain ⟨hblockI, hblockJ⟩ := Prod.mk.inj (lay.table_injective hQ)
  constructor
  · rw [← position_decomp lay I, ← position_decomp lay I', hI, hblockI,
      lay.rowIdx.injective hr]
  · rw [← position_decomp lay J, ← position_decomp lay J', hJ, hblockJ,
      lay.colIdx.injective hc]

end ThreeSumApsp
