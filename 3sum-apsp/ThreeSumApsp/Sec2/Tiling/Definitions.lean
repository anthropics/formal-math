/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Levels

/-!
# Definitions for the tiling of the `N × D × N` product

* Section 2.3.4: `K₀`, the choices that the paper makes once and for all (`Layout`), bands, padding,
  row and column blocks, the matrices `X_Q` and `Y_Q` and the input arrays of a tile, and the
  position of a row or column in its band and block.
* Section 2.4.4: the output string of a position, the wanted strings of a tile, and the set of all
  tiles.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-- Section 2.3.4: "K₀ := ⌊√K⌋". -/
def K0 (L m : ℕ) : ℕ := Nat.sqrt (K L m)

/-- `N₀ = 3^{L-m}` is positive. -/
theorem N0_pos (L m : ℕ) : 0 < N0 L m := Nat.pow_pos (by decide)

/-- `K₀ = ⌊√binom(L, m)⌋` is positive when `m ≤ L`. -/
theorem K0_pos {L m : ℕ} (h : m ≤ L) : 0 < K0 L m := Nat.sqrt_pos.mpr (Nat.choose_pos h)

/-- The choices that the paper makes once and for all without naming them.

* `hmL`: `m ≤ L`. The paper never states this; it follows from `L = 19m` (Section 2) and from
  `L ≥ 10m` (Section 4). It makes `K₀ ≥ 1`.
* Section 2.3.3: "we index its N₀ rows by the N₀ strings of L - m outer left variables, and its D
  columns by the D strings of m inner left variables", and similarly for a `D × N₀` matrix.
  `rowIdx`, `colIdx` and `innerIdx` say which string indexes which row or column, counted from 0.
* Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
  of the grid, the same in every tile." `table (g, h)` is the subset of the block product of the
  `g`-th row block of a row band and the `h`-th column block of a column band.

Every statement about the tiling holds for every such choice. -/
structure Layout (L m : ℕ) where
  hmL : m ≤ L
  rowIdx : Fin (N0 L m) ≃ OuterStr L m
  colIdx : Fin (N0 L m) ≃ OuterStr L m
  innerIdx : Fin (D m) ≃ InnerStr m
  table : Fin (K0 L m) × Fin (K0 L m) → Finset (Fin L)
  table_card : ∀ gh, (table gh).card = m
  table_injective : Function.Injective table

/-- The number `K₀ N₀` of rows of a row band (Section 2.3.4: a band is `K₀` consecutive blocks of
`N₀` consecutive rows), which is also the number of columns of a column band. -/
def bandSize (L m : ℕ) : ℕ := K0 L m * N0 L m

/-- The number of row bands (and of column bands) after padding: `N / (K₀ N₀)` rounded up. -/
def numBands (L m N : ℕ) : ℕ := (N + bandSize L m - 1) / bandSize L m

/-- Section 2.3.4: "we first pad N to a multiple of K₀ N₀".  The padded size. -/
def padN (L m N : ℕ) : ℕ := numBands L m N * bandSize L m

/-- Section 2.3.4: `X` padded "with zero rows".  Rows are numbered from 0. -/
def padRows {N D' : ℕ} (X : Matrix (Fin N) (Fin D') ℤ) (I : ℕ) (k : Fin D') : ℤ :=
  if h : I < N then X ⟨I, h⟩ k else 0

/-- Section 2.3.4: `Y` padded with "zero columns".  Columns are numbered from 0. -/
def padCols {N D' : ℕ} (Y : Matrix (Fin D') (Fin N) ℤ) (k : Fin D') (J : ℕ) : ℤ :=
  if h : J < N then Y k ⟨J, h⟩ else 0

/-- Section 2.3.4: "Cut X into row blocks of N₀ consecutive rows".  The `B`-th row block (counted
from 0) consists of the rows `B N₀, …, B N₀ + N₀ - 1`. -/
def rowBlock {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (B : ℕ) :
    LeftMat L m :=
  fun r π => padRows X (B * N0 L m + lay.rowIdx.symm r) (lay.innerIdx.symm π)

/-- Section 2.3.4: "and Y into column blocks of N₀ consecutive columns". -/
def colBlock {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (B : ℕ) :
    RightMat L m :=
  fun π c => padCols Y (lay.innerIdx.symm π) (B * N0 L m + lay.colIdx.symm c)

/-- Section 2.3.4: "In a tile, let X_Q and Y_Q be the row block and the column block of the block
product with subset Q, and let X_Q = Y_Q = 0 for the other subsets Q." The row band `β` (counted
from 0) consists of the row blocks `β K₀, …, β K₀ + K₀ - 1`. The subsets in the table are distinct,
so at most one summand is nonzero. -/
def bandFamilyL {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) :
    Finset (Fin L) → LeftMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then rowBlock lay X (β * K0 L m + gh.1) else 0

/-- The matrices `Y_Q` of a tile; they depend only on its column band `β`. -/
def bandFamilyR {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) :
    Finset (Fin L) → RightMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then colBlock lay Y (β * K0 L m + gh.2) else 0

/-- Section 2.3.4: "the left input array of a tile depends only on its row band". -/
def bandArrayL {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) :
    LeftStr L → ℤ :=
  arrayL m (bandFamilyL lay X β)

/-- Section 2.3.4: "and the right one only on its column band". -/
def bandArrayR {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) :
    RightStr L → ℤ :=
  arrayR m (bandFamilyR lay Y β)

/-- The band that contains row (or column) `I`. -/
def bandOf (L m I : ℕ) : ℕ := I / bandSize L m

/-- The position, within its band, of the block that contains row (or column) `I`. -/
def blockOf {L m : ℕ} (lay : Layout L m) (I : ℕ) : Fin (K0 L m) :=
  ⟨I / N0 L m % K0 L m, Nat.mod_lt _ (K0_pos lay.hmL)⟩

/-- The position of row (or column) `I` within its block. -/
def offsetOf (L m I : ℕ) : Fin (N0 L m) := ⟨I % N0 L m, Nat.mod_lt _ (N0_pos L m)⟩

/-- Section 2.4.4: "Each wanted position (I, J) ∈ W lies in one tile T and is indexed by one output
string of T, the string whose inner set is the subset Q of the block product containing (I, J) and
whose row and column are those of (I, J) within that block product". The tile is the pair
`(bandOf L m I, bandOf L m J)`, and this is the output string. -/
def outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) : OutStr L :=
  outStrOf (lay.table (blockOf lay I, blockOf lay J)) (lay.table_card _)
    (lay.rowIdx (offsetOf L m I)) (lay.colIdx (offsetOf L m J))

/-- Section 2.4.4: "For each tile T, let W_T be the set of the output strings of the wanted
positions in T."  The tile `T` is given by its row band `β` and its column band `β'`. -/
def wantedStrings {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N)) (β β' : ℕ) :
    Finset (OutStr L) :=
  (W.filter fun IJ => bandOf L m IJ.1 = β ∧ bandOf L m IJ.2 = β').image
    fun IJ => outStrOfPos lay IJ.1 IJ.2

/-- All the tiles: pairs of a row band and a column band. -/
def tiles (L m N : ℕ) : Finset (ℕ × ℕ) := range (numBands L m N) ×ˢ range (numBands L m N)

end ThreeSumApsp
