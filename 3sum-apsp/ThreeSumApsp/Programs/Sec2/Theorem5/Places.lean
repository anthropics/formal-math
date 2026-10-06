/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Tiling.Definitions
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/

/-- The parameters of the recursion and of the matrices: `L` levels, `m` of them inner, matrices
`N × D` and `D × N` with `D = 4^m`. -/
structure Par where
  /-- The number of levels of the recursion. -/
  L : ℕ
  /-- The number of inner levels. -/
  m : ℕ
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ

namespace Par

/-- `D = 4^m`. -/
def D (p : Par) : ℕ := ThreeSumApsp.D p.m
/-- The number `L - m` of outer levels. -/
def Lo (p : Par) : ℕ := p.L - p.m
/-- `N₀ = 3^{L-m}`. -/
def N0 (p : Par) : ℕ := ThreeSumApsp.N0 p.L p.m
/-- `K = binom(L, m)`. -/
def K (p : Par) : ℕ := ThreeSumApsp.K p.L p.m
/-- `K₀ = ⌊√K⌋`. -/
def K0 (p : Par) : ℕ := ThreeSumApsp.K0 p.L p.m
/-- The number `K₀²` of subsets in the table. -/
def KK (p : Par) : ℕ := p.K0 * p.K0
/-- The number of row bands, and of column bands. -/
def nB (p : Par) : ℕ := numBands p.L p.m p.N
/-- The number of tiles. -/
def nT (p : Par) : ℕ := p.nB * p.nB
/-- The number `10^L` of leaves: the length of an encoding. -/
def T (p : Par) : ℕ := 10 ^ p.L
/-- The number `7^L` of left strings: the length of an input array. -/
def S7 (p : Par) : ℕ := 7 ^ p.L

/-! ## The shared block, from its base address `b0` on -/

/-- The directory: 32 cells, see `dirList`. -/
def aDIR (_p : Par) (b0 : ℕ) : ℕ := b0
/-- Powers of 3: `L + 1` cells. -/
def aP3 (_p : Par) (b0 : ℕ) : ℕ := b0 + 32
/-- Powers of 4: `L + 1` cells. -/
def aP4 (p : Par) (b0 : ℕ) : ℕ := p.aP3 b0 + (p.L + 1)
/-- Powers of 7: `L + 1` cells. -/
def aP7 (p : Par) (b0 : ℕ) : ℕ := p.aP4 b0 + (p.L + 1)
/-- Powers of 10: `L + 1` cells. -/
def aP10 (p : Par) (b0 : ℕ) : ℕ := p.aP7 b0 + (p.L + 1)
/-- Scratch for a row of Pascal's triangle: `L + 2` cells. -/
def aPAS (p : Par) (b0 : ℕ) : ℕ := p.aP10 b0 + (p.L + 1)
/-- The coefficients `φ_λ(s)`: 70 cells, row `λ` at `7 λ`. -/
def aPHI (p : Par) (b0 : ℕ) : ℕ := p.aPAS b0 + (p.L + 2)
/-- The coefficients `ψ_λ(t)`: 70 cells. -/
def aPSI (p : Par) (b0 : ℕ) : ℕ := p.aPHI b0 + 70
/-- The table of subsets: `K₀²` rows of `L` bits, the subset of the block product `(g, h)` in row
`g K₀ + h`. -/
def aMASK (p : Par) (b0 : ℕ) : ℕ := p.aPSI b0 + 70
/-- The band of every row: `N` cells. -/
def aBAND (p : Par) (b0 : ℕ) : ℕ := p.aMASK b0 + p.KK * p.L
/-- The block, within its band, of every row: `N` cells. -/
def aBLOCK (p : Par) (b0 : ℕ) : ℕ := p.aBAND b0 + p.N
/-- The base-3 digits of the offset of every row within its block: `N` rows of `L - m` cells, most
significant digit first. -/
def aDIG3 (p : Par) (b0 : ℕ) : ℕ := p.aBLOCK b0 + p.N
/-- The base-4 digits of every column of `X`: `D` rows of `m` cells, most significant digit first.
-/
def aDIG4 (p : Par) (b0 : ℕ) : ℕ := p.aDIG3 b0 + p.N * p.Lo
/-- The encodings of the row bands: band `β` at `β 10^L`. -/
def aENCA (p : Par) (b0 : ℕ) : ℕ := p.aDIG4 b0 + p.D * p.m
/-- The encodings of the column bands. -/
def aENCB (p : Par) (b0 : ℕ) : ℕ := p.aENCA b0 + p.nB * p.T
/-- The input array of the band that is being encoded: `7^L` cells.  Dead after the shared stage.
-/
def aARR (p : Par) (b0 : ℕ) : ℕ := p.aENCB b0 + p.nB * p.T
/-- Scratch of the recursive encoding: `7^L` cells (`7^{L-1} + … + 1` are used). Dead after the
shared stage. -/
def aZS (p : Par) (b0 : ℕ) : ℕ := p.aARR b0 + p.S7
/-- The first address after the shared block. -/
def sharedEnd (p : Par) (b0 : ℕ) : ℕ := p.aZS b0 + p.S7

end Par

/-- The content of the first 31 cells of the directory (the shared stage does not use the last one);
`aX` and `aY` are the addresses of `X` and `Y`. -/
def dirList (p : Par) (aX aY b0 : ℕ) : List ℕ :=
  [p.L, p.m, p.N, p.D, p.Lo, p.N0, p.K, p.K0, p.KK, p.nB, p.T, p.S7, aX, aY, p.aP3 b0, p.aP4 b0,
    p.aP7 b0, p.aP10 b0, p.aPAS b0, p.aPHI b0, p.aPSI b0, p.aMASK b0, p.aBAND b0, p.aBLOCK b0,
    p.aDIG3 b0, p.aDIG4 b0, p.aENCA b0, p.aENCB b0, p.aARR b0, p.aZS b0, p.sharedEnd b0]

/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par

/-- The tile number `band(I) nB + band(J)` of every wanted position: `w` cells. -/
def aTID (p : Par) (fr _w : ℕ) : ℕ := p.sharedEnd fr
/-- The code of the output string of every wanted position: `w` cells. -/
def aCODE (p : Par) (fr w : ℕ) : ℕ := p.aTID fr w + w
/-- The `L` digits of the code of the output string of every wanted position, most significant
first: `w` rows of `L` cells. -/
def aDGT (p : Par) (fr w : ℕ) : ℕ := p.aCODE fr w + w
/-- The permutation that sorts the wanted positions by tile and, within a tile, by code: `w` cells.
-/
def aPERM (p : Par) (fr w : ℕ) : ℕ := p.aDGT fr w + w * p.L
/-- The second buffer of the sort: `w` cells. -/
def aPERM2 (p : Par) (fr w : ℕ) : ℕ := p.aPERM fr w + w
/-- The counters of the sort: `nT + 11` cells. -/
def aCNT (p : Par) (fr w : ℕ) : ℕ := p.aPERM2 fr w + w
/-- For every tile the number of wanted positions in earlier tiles: `nT + 1` cells. -/
def aSTART (p : Par) (fr w : ℕ) : ℕ := p.aCNT fr w + (p.nT + 11)
/-- The codes in sorted order: `w` cells. -/
def aSC (p : Par) (fr w : ℕ) : ℕ := p.aSTART fr w + (p.nT + 1)
/-- The values in sorted order: `w` cells. -/
def aSV (p : Par) (fr w : ℕ) : ℕ := p.aSC fr w + w
/-- The stack of the pruned recursion: `L` frames of at most `3 w + 11` cells. -/
def aSTK (p : Par) (fr w : ℕ) : ℕ := p.aSV fr w + w
/-- The first address that Theorem 5's program does not use. -/
def end5 (p : Par) (fr w : ℕ) : ℕ := p.aSTK fr w + p.L * (3 * w + 11)
/-- The number of cells, from the free pointer on, that Theorem 5's program uses. -/
def cells5 (p : Par) (w : ℕ) : ℕ := p.end5 0 w

end Par

/-! ## The places and the sizes, as equations and inequalities -/

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)

theorem one_le_T : 1 ≤ p.T := Nat.one_le_pow _ _ (by omega)

theorem L_lt_T : p.L < p.T := Nat.lt_pow_self (by omega)

/-- `2^L ≤ 10^L`. -/
theorem two_pow_le_T : 2 ^ p.L ≤ p.T := Nat.pow_le_pow_left (by omega) _

theorem K_le_T : p.K ≤ p.T := (Nat.choose_le_two_pow _ _).trans p.two_pow_le_T

theorem N0_le_T : p.N0 ≤ p.T :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

theorem D_le_T (hmL : p.m ≤ p.L) : p.D ≤ p.T :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hmL)

theorem K0_le_K : p.K0 ≤ p.K := Nat.sqrt_le_self _

/-- `K₀² ≤ K`. -/
theorem KK_le_K : p.KK ≤ p.K := Nat.sqrt_le _

/-- The sizes: 1, `L`, `2^L`, `K`, `N₀` and `D` are at most `T = 10^L`; `K₀` and `K₀²` are at most
`K`; `K₀` and `N₀` are positive; and the definition of `Lo`. -/
theorem sizes (hmL : p.m ≤ p.L) :
    1 ≤ p.T ∧ p.L < p.T ∧ 2 ^ p.L ≤ p.T ∧ p.K ≤ p.T ∧ p.N0 ≤ p.T ∧ p.D ≤ p.T ∧ p.K0 ≤ p.K
      ∧ p.KK ≤ p.K ∧ 0 < p.K0 ∧ 0 < p.N0 ∧ p.Lo = p.L - p.m :=
  ⟨p.one_le_T, p.L_lt_T, p.two_pow_le_T, p.K_le_T, p.N0_le_T, p.D_le_T hmL, p.K0_le_K, p.KK_le_K,
    ThreeSumApsp.K0_pos hmL, ThreeSumApsp.N0_pos _ _, rfl⟩

end Par

/-- The places of the private block of Theorem 5, which follows the shared block. -/
theorem Par.places5 (p : Par) (fr w : ℕ) :
    p.aTID fr w = p.sharedEnd fr ∧ p.aCODE fr w = p.aTID fr w + w ∧ p.aDGT fr w = p.aCODE fr w + w
      ∧ p.aPERM fr w = p.aDGT fr w + w * p.L ∧ p.aPERM2 fr w = p.aPERM fr w + w
      ∧ p.aCNT fr w = p.aPERM2 fr w + w ∧ p.aSTART fr w = p.aCNT fr w + (p.nB * p.nB + 11)
      ∧ p.aSC fr w = p.aSTART fr w + (p.nB * p.nB + 1) ∧ p.aSV fr w = p.aSC fr w + w
      ∧ p.aSTK fr w = p.aSV fr w + w ∧ p.end5 fr w = p.aSTK fr w + p.L * (3 * w + 11)
      ∧ p.nT = p.nB * p.nB :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Light.Sec2
