/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.PowTable
public import ThreeSumApsp.Programs.Sec2.Theorem5.Places
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout
public import ThreeSumApsp.Spec.Sec2.Theorem5.PrunedList

/-!
# Theorem 5 in the light language: the map

One file that fixes everything on which two routines have to agree, besides the sizes and the places
of the arrays: the numbers of the procedures, and for every procedure its arguments, what it needs,
what it leaves behind, which cells it may change, and the shape of its running time. A routine is
proved against its own entry; a caller assumes the entries of the routines it calls. So the proof of
a routine does not depend on the proofs of the routines that it calls.

* Routines never contain an address.  They receive scalars and base addresses as arguments.  Only
  the two main routines (Theorem 5 here, the data structure of Section 4) know the places.
* The stages up to the encodings of all bands are shared with Section 4: procedure pShared fills the
  shared block, which starts at an address b0 above the input and the output of the program that
  calls it (the free pointer).
* An entry XSpec lim P c says: in the program P, within the limits lim, procedure number pX does its
  job within c times the shape of its running time (Meets).  The theorem on a routine proves its
  entry for every c from the constant of the routine on, so a caller can assume several entries at
  one constant.
* The entries of encStep, encodeBands, countSort, copy, runTiles and report stand with these
  routines.
* Strings are numbers: a string over an alphabet of b symbols is its code in base b, level 1 most
  significant (namespace Spec).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Vocabulary -/

/-- The cells from a on hold a list of bits, as 1 and 0. -/
def SegB (μ : ℕ → ℤ) (a : ℕ) (l : List Bool) : Prop :=
  Seg μ a (l.map fun b : Bool => if b then (1 : ℤ) else 0)

/-- A cell of a segment of bits. -/
theorem SegB.get {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : SegB μ a l) {q : ℕ} (hq : q < l.length) :
    μ (a + q) = if l.getD q false then 1 else 0 :=
  (Seg.getD h (by rwa [List.length_map]) 0).trans (List.getD_map_of_lt _ hq false 0)

/-! ## The numbers of the procedures

Number 0 is empty.  1 to 25: the shared routines and those of Theorem 5.  26 to 28: the test of the
regime, the brute force, and the solver for all instances.  29 to 39 are not used.  From 40 on:
Section 4. -/

/-- The number of shared. -/
def pShared : ℕ := 1
/-- The number of pow. -/
def pPow : ℕ := 2
/-- The number of binom. -/
def pBinom : ℕ := 3
/-- The number of sqrt. -/
def pSqrt : ℕ := 4
/-- The number of subsets. -/
def pSubsets : ℕ := 5
/-- The number of counters. -/
def pCounters : ℕ := 6
/-- The number of digits. -/
def pDigits : ℕ := 7
/-- The number of coef. -/
def pCoef : ℕ := 8
/-- The number of bandArray. -/
def pBandArray : ℕ := 9
/-- The number of encStep. -/
def pEncStep : ℕ := 10
/-- The number of encode. -/
def pEncode : ℕ := 11
/-- The number of encodeBands. -/
def pEncodeBands : ℕ := 12
/-- The number of wanted. -/
def pWanted : ℕ := 13
/-- The number of countSort. -/
def pCountSort : ℕ := 14
/-- The number of sortWanted. -/
def pSortWanted : ℕ := 15
/-- The number of segBounds. -/
def pSegBounds : ℕ := 16
/-- The number of union. -/
def pUnion : ℕ := 17
/-- The number of pick. -/
def pPick : ℕ := 18
/-- The number of pruned. -/
def pPruned : ℕ := 19
/-- The number of runTiles. -/
def pRunTiles : ℕ := 20
/-- The number of report. -/
def pReport : ℕ := 21
/-- The number of fill. -/
def pFill : ℕ := 22
/-- The number of copy. -/
def pCopy : ℕ := 23
/-- The number of gather. -/
def pGather : ℕ := 24
/-- The number of the solver of Theorem 5. -/
def pThm5 : ℕ := 25
/-- The number of the test of the regime. -/
def pRegime : ℕ := 26
/-- The number of the brute force. -/
def pThinBrute : ℕ := 27
/-- The number of the solver for all instances. -/
def pThin : ℕ := 28

/-! ## The entries of the shared routines -/

section Entries

variable (lim : Limits) (P : Program) (c : ℕ)

/-- pow(b, n, dst): writes b^0, …, b^n to dst. -/
def PowSpec : Prop :=
  ∀ (b n dst : ℕ) (μ : ℕ → ℤ),
    1 ≤ dst → dst + (n + 1) ≤ lim.space → 1 ≤ b →
    ((b ^ (n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, n, dst] μ (c * (n + 1)) fun _ μ' =>
      Seg μ' dst (powList b (n + 1)) ∧ SameOutside μ μ' dst (n + 1)

/-- binom(L, m, pas): returns binom(L, m), by Pascal's triangle in the L + 2 cells from pas. -/
def BinomSpec : Prop :=
  ∀ (L m pas : ℕ) (μ : ℕ → ℤ),
    pas + (L + 2) ≤ lim.space → m ≤ L → ((2 ^ L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pBinom d [L, m, pas] μ (c * (L + 1) ^ 2) fun r μ' =>
      r = (L.choose m : ℕ) ∧ SameOutside μ μ' pas (L + 2)

/-- sqrt(K): returns ⌊√K⌋, by counting up.  Changes no cell. -/
def SqrtSpec : Prop :=
  ∀ (K : ℕ) (μ : ℕ → ℤ),
    ((4 * K + 4 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pSqrt d [K] μ (c * (Nat.sqrt K + 1)) fun r μ' =>
      r = (Nat.sqrt K : ℕ) ∧ μ' = μ

/-- subsets(L, m, KK, mask): writes the first KK subsets of size m of the L levels, as rows of L
bits, in the order of Spec.unrank. -/
def SubsetsSpec : Prop :=
  ∀ (L m KK mask : ℕ) (μ : ℕ → ℤ),
    mask + KK * L ≤ lim.space → m ≤ L → KK ≤ L.choose m →
    ((KK + L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pSubsets d [L, m, KK, mask] μ (c * ((KK + 1) * (L + 1))) fun _ μ' =>
      (∀ s < KK, SegB μ' (mask + s * L) (Spec.unrank L m s)) ∧ SameOutside μ μ' mask (KK * L)

/-- counters(N, K0, N0, band): for every row I < N writes its band I / (K0 N0) to band + I and its
block I / N0 % K0 to band + N + I, by counting. -/
def CountersSpec : Prop :=
  ∀ (N K0 N0 band : ℕ) (μ : ℕ → ℤ),
    band + 2 * N ≤ lim.space → 0 < K0 → 0 < N0 →
    ((K0 + N0 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pCounters d [N, K0, N0, band] μ (c * (N + 1)) fun _ μ' =>
      (∀ I < N, μ' (band + I) = (I / (K0 * N0) : ℕ) ∧ μ' (band + N + I) = (I / N0 % K0 : ℕ))
      ∧ SameOutside μ μ' band (2 * N)

/-- digits(n, b, len, dst): for every x < n writes the len digits of x % b^len in base b, most
significant first, to dst + x len, by an odometer. -/
def DigitsSpec : Prop :=
  ∀ (n b len dst : ℕ) (μ : ℕ → ℤ),
    dst + n * len ≤ lim.space → 2 ≤ b → (b : ℤ) ≤ lim.word →
    (n : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pDigits d [n, b, len, dst] μ (c * ((n + 1) * (len + 1))) fun _ μ' =>
      (∀ x < n, SegN μ' (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len)))
      ∧ SameOutside μ μ' dst (n * len)

/-- coef(phi): writes the 70 coefficients φ_λ(s) to phi and the 70 coefficients ψ_λ(t) to phi + 70.
-/
def CoefSpec : Prop :=
  ∀ (phi : ℕ) (μ : ℕ → ℤ),
    phi + 140 ≤ lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pCoef d [phi] μ c fun _ μ' =>
      Seg μ' phi Spec.phiFlat ∧ Seg μ' (phi + 70) Spec.psiFlat
      ∧ SameOutside μ μ' phi 140

/-- What bandArray reads, apart from the matrix: the table of subsets and the two tables of digits,
all below the array it writes. -/
structure BandTables (p : Par) (μ : ℕ → ℤ) (mask dig3 dig4 arr : ℕ) : Prop where
  hmask : ∀ s < p.KK, SegB μ (mask + s * p.L) (Spec.unrank p.L p.m s)
  hdig3 : ∀ I < p.N, SegN μ (dig3 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  hdig4 : ∀ x < p.D, SegN μ (dig4 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)
  mask_le : mask + p.KK * p.L ≤ arr
  dig3_le : dig3 + p.N * p.Lo ≤ arr
  dig4_le : dig4 + p.D * p.m ≤ arr

/-- The shape of the running time of bandArray: clear 7^L cells, then one entry in O(L) steps for
each subset of the table, each row of a block and each column. -/
def bandArrayShape (p : Par) : ℕ := p.S7 + (p.KK * p.N0 * p.D + 1) * (p.L + 1)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr), for the left
side: side = 0, aA the address of X, sI = D, sK = 1 (sI and sK are the strides of the index I of the
band and of the inner index k: the entry is at aA + I sI + k sK).  Writes the input array of the row
band β (Section 2.3.4), in the order of the codes, to arr. -/
def BandArrayLSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aX mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aX X → aX + p.N * p.D ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 0, aX, p.D, 1, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β)) ∧ SameOutside μ μ' arr p.S7

/-- The same procedure for the right side: side = 1, aA the address of Y, sI = 1, sK = N. Writes the
input array of the column band β. -/
def BandArrayRSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aY mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aY Y → aY + p.D * p.N ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 1, aY, 1, p.N, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β)) ∧ SameOutside μ μ' arr p.S7

/-- Where encode finds its tables and its areas: the tables lie below dst, the 10^n cells of dst
below src, the 7^n cells of src below scr, and scr has 7^n cells. -/
structure EncodePlaces (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) : Prop where
  n_le : n ≤ Lmax
  hp7 : Seg μ p7 (powList 7 (Lmax + 1))
  hp10 : Seg μ p10 (powList 10 (Lmax + 1))
  tab_le : tab + 70 ≤ dst
  p7_le : p7 + (Lmax + 1) ≤ dst
  p10_le : p10 + (Lmax + 1) ≤ dst
  dst_le : dst + 10 ^ n ≤ src
  src_le : src + 7 ^ n ≤ scr
  scr_le : scr + 7 ^ n ≤ lim.space

/-- encode(n, src, dst, scr, tab, p7, p10), the procedure of Section 2.4.1, recursive as
printed, with the coefficients φ: from the array a at src it computes the encoding of a at dst. -/
def EncodeLSpec : Prop :=
  ∀ (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) (a : LeftStr n → ℤ) (V : ℤ),
    EncodePlaces lim n Lmax src dst scr tab p7 p10 μ →
    Seg μ tab Spec.phiFlat → Seg μ src (Spec.arrL a) → (∀ u, |a u| ≤ V) →
    7 ^ (n + 1) * V ≤ lim.word →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pEncode d [n, src, dst, scr, tab, p7, p10] μ (c * 10 ^ n) fun _ μ' =>
      Seg μ' dst (Spec.arrT (encodingL a)) ∧ SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n)

/-- The same procedure with the coefficients ψ. -/
def EncodeRSpec : Prop :=
  ∀ (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) (b : RightStr n → ℤ) (V : ℤ),
    EncodePlaces lim n Lmax src dst scr tab p7 p10 μ →
    Seg μ tab Spec.psiFlat → Seg μ src (Spec.arrR b) → (∀ v, |b v| ≤ V) →
    7 ^ (n + 1) * V ≤ lim.word →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pEncode d [n, src, dst, scr, tab, p7, p10] μ (c * 10 ^ n) fun _ μ' =>
      Seg μ' dst (Spec.arrT (encodingR b)) ∧ SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n)

/-! ## The shared stage -/

/-- The tables of the powers of 3, 4, 7 and 10 in the shared block. -/
structure PowTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  p3 : Seg μ (p.aP3 b0) (powList 3 (p.L + 1))
  p4 : Seg μ (p.aP4 b0) (powList 4 (p.L + 1))
  p7 : Seg μ (p.aP7 b0) (powList 7 (p.L + 1))
  p10 : Seg μ (p.aP10 b0) (powList 10 (p.L + 1))

/-- The other tables of the shared block: the coefficients, the subsets, the band and the block of
every row, and the digits of the offsets and of the inner indices. -/
structure RowTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  phi : Seg μ (p.aPHI b0) Spec.phiFlat
  psi : Seg μ (p.aPSI b0) Spec.psiFlat
  mask : ∀ s < p.KK, SegB μ (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s)
  band : ∀ I < p.N, μ (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
  block : ∀ I < p.N, μ (p.aBLOCK b0 + I) = (I / p.N0 % p.K0 : ℕ)
  dig3 : ∀ I < p.N, SegN μ (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  dig4 : ∀ x < p.D, SegN μ (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)

/-- The tables of the shared block, all in one memory. -/
structure SharedTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop
  extends PowTables p b0 μ, RowTables p b0 μ

/-- What the shared stage leaves behind: the tables, the directory, and the encodings of all bands.
(Cell 31 of the directory is not used by it.) -/
structure SharedReady (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop
  extends SharedTables p b0 μ where
  dir : SegN μ (p.aDIR b0) (dirList p aX aY b0)
  encA : ∀ β < p.nB, Seg μ (p.aENCA b0 + β * p.T)
    (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))
  encB : ∀ β < p.nB, Seg μ (p.aENCB b0 + β * p.T)
    (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))

/-- The shape of the running time of the shared stage. -/
def sharedShape (p : Par) : ℕ :=
  (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1)
    + p.nB * (p.T + bandArrayShape p)

/-- What the shared stage assumes: the shared block fits in the memory, X and Y stand below it, V
bounds their entries, and the encoded numbers and the powers of ten fit in a word. -/
structure SharedPre (p : Par) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ) (μ : ℕ → ℤ) : Prop where
  space : p.sharedEnd b0 ≤ lim.space
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  belowX : aX + p.N * p.D ≤ b0
  belowY : aY + p.D * p.N ≤ b0
  absX : ∀ i j, |X i j| ≤ V
  absY : ∀ i j, |Y i j| ≤ V
  seven : 7 ^ (p.L + 1) * V ≤ lim.word
  ten : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word

/-- shared(L, m, N, D, aX, aY, b0): fills the shared block. -/
def SharedSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    SharedPre lim p aX aY b0 X Y V μ →
    ∀ d, d + (p.L + 3) ≤ lim.depth →
    Meets lim P pShared d [p.L, p.m, p.N, p.D, aX, aY, b0] μ (c * sharedShape p) fun _ μ' =>
      SharedReady p hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (p.sharedEnd b0 - b0)

/-! ## Theorem 5 -/

/-- What wanted reads, apart from the positions: all of it lies below the area it writes. -/
structure WantedTables (p : Par) (μ : ℕ → ℤ) (band dig3 mask tid : ℕ) : Prop where
  hband : ∀ I < p.N, μ (band + I) = (I / (p.K0 * p.N0) : ℕ)
  hblock : ∀ I < p.N, μ (band + p.N + I) = (I / p.N0 % p.K0 : ℕ)
  hdig3 : ∀ I < p.N, SegN μ (dig3 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  hmask : ∀ s < p.KK, SegB μ (mask + s * p.L) (Spec.unrank p.L p.m s)
  band_le : band + 2 * p.N ≤ tid
  dig3_le : dig3 + p.N * p.Lo ≤ tid
  mask_le : mask + p.KK * p.L ≤ tid

/-- What wanted assumes. -/
structure Wanted.WantedPre (p : Par) (w aWI aWJ band dig3 mask tid : ℕ) (I J : ℕ → ℕ)
    (μ : ℕ → ℤ) : Prop where
  hmL : p.m ≤ p.L
  tab : WantedTables p μ band dig3 mask tid
  hI : ∀ i < w, μ (aWI + i) = I i ∧ I i < p.N
  hJ : ∀ i < w, μ (aWJ + i) = J i ∧ J i < p.N
  hpow : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word
  hnB : (((p.nB + 1) * (p.nB + 1) : ℕ) : ℤ) ≤ lim.word
  room : tid + (2 * w + w * p.L) ≤ lim.space := by light_arith
  hWI : aWI + w ≤ tid := by light_arith
  hWJ : aWJ + w ≤ tid := by light_arith

/-- wanted(w, L, Lo, N, K0, nB, aWI, aWJ, band, dig3, mask, tid): "locate the output strings"
(Section 2.4.4). For the i-th wanted position (I, J) it writes the number of its tile to tid + i,
the code of its output string to tid + w + i, and the L digits of that code to tid + 2 w + i L. -/
def WantedSpec : Prop :=
  ∀ (p : Par) (w aWI aWJ band dig3 mask tid : ℕ) (μ : ℕ → ℤ) (I J : ℕ → ℕ),
    Wanted.WantedPre lim p w aWI aWJ band dig3 mask tid I J μ →
    ∀ d, d ≤ lim.depth →
    Meets lim P pWanted d [w, p.L, p.Lo, p.N, p.K0, p.nB, aWI, aWJ, band, dig3, mask, tid] μ
      (c * ((w + 1) * (p.L + 1))) fun _ μ' =>
      (∀ i < w, μ' (tid + i) = (I i / (p.K0 * p.N0) * p.nB + J i / (p.K0 * p.N0) : ℕ)
        ∧ μ' (tid + w + i) = (Spec.outCodeOfPos p.L p.m (I i) (J i) : ℕ)
        ∧ SegN μ' (tid + 2 * w + i * p.L)
          (ThreeSumApsp.digitList 10 p.L (Spec.outCodeOfPos p.L p.m (I i) (J i))))
      ∧ SameOutside μ μ' tid (2 * w + w * p.L)

namespace SortWanted

/-- The arguments of sortWanted. -/
structure Args where
  /-- the number of positions -/
  w : ℕ
  /-- the number of digits of a code -/
  L : ℕ
  /-- the number of tiles -/
  nT : ℕ
  /-- where the numbers of the tiles stand -/
  tid : ℕ
  /-- where the digits of the codes stand -/
  dgt : ℕ
  /-- where the sorted list goes -/
  perm : ℕ

/-- The number of cells from perm on that may change. -/
def Args.room (A : Args) : ℕ := 2 * A.w + (A.nT + 11) + (A.nT + 1)

/-- The number of cells, written out. -/
theorem Args.room_eq (A : Args) : A.room = 2 * A.w + (A.nT + 11) + (A.nT + 1) := rfl

end SortWanted

/-- What sortWanted assumes: t i and x i are the tile and the code of position i, and they stand
before the cells that may change. -/
structure SwPre (μ : ℕ → ℤ) (A : SortWanted.Args) (t x : ℕ → ℕ) : Prop where
  space : A.perm + A.room ≤ lim.space
  tidBefore : A.tid + A.w ≤ A.perm
  dgtBefore : A.dgt + A.w * A.L ≤ A.perm
  tiles : ∀ i < A.w, μ (A.tid + i) = t i
  tileLt : ∀ i < A.w, t i < A.nT
  codes : ∀ i < A.w, SegN μ (A.dgt + i * A.L) (ThreeSumApsp.digitList 10 A.L (x i))
  codeLt : ∀ i < A.w, x i < 10 ^ A.L

/-- sortWanted(w, L, nT, tid, dgt, perm): "sort the sets W_T" (Section 2.4.4), by a radix sort: L
stable counting sorts on the digits of the codes, the last digit first, then one on the numbers of
the tiles. t i and x i are the tile and the code of position i. It writes the sorting permutation to
perm and, for every s ≤ nT, the number of positions in tiles below s to perm + 2 w + nT + 11 + s.
The cells from perm + w to perm + 2 w + nT + 11 are scratch. -/
def SortWantedSpec : Prop :=
  ∀ (A : SortWanted.Args) (μ : ℕ → ℤ) (t x : ℕ → ℕ), SwPre lim μ A t x →
    ∀ d, d + 1 ≤ lim.depth →
    Meets lim P pSortWanted d [A.w, A.L, A.nT, A.tid, A.dgt, A.perm] μ
      (c * ((A.L + 1) * (A.w + 10) + A.nT + 1)) fun _ μ' =>
      (∃ π : List ℕ, π.Perm (List.range A.w) ∧ SegN μ' A.perm π
        ∧ (π.map fun i => t i * 10 ^ A.L + x i).Pairwise (· ≤ ·))
      ∧ (∀ s ≤ A.nT, μ' (A.perm + 2 * A.w + (A.nT + 11) + s)
        = (((List.range A.w).filter fun i => t i < s).length : ℕ))
      ∧ SameOutside μ μ' A.perm A.room

/-- fill(dst, n, x): dst[i] := x for i < n. -/
def FillSpec : Prop :=
  ∀ (dst n : ℕ) (x : ℤ) (μ : ℕ → ℤ),
    dst + n ≤ lim.space → n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pFill d [dst, n, x] μ (c * (n + 1)) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n

/-- The number of codes of an increasing list whose first digit (of n + 1) is below z. -/
def segStart (n : ℕ) (codes : List ℕ) (z : ℕ) : ℕ :=
  ((List.range z).map fun t => (Spec.sliceList n t codes).length).sum

/-- segBounds(l, len, pw, bnd), with pw = 10^n: one pass over an increasing list of codes of n + 1
digits. For z ≤ 10 it writes the number of codes with first digit below z to bnd + z, and it writes
the codes without their first digits to the len cells from bnd + 11. So the slice at z (Section
2.4.2), Spec.sliceList n z codes, is the segment that starts at bnd + 11 + segStart n codes z. -/
def SegBoundsSpec : Prop :=
  ∀ (n l bnd : ℕ) (codes : List ℕ) (μ : ℕ → ℤ),
    SegN μ l codes → codes.Pairwise (· < ·) → (∀ x ∈ codes, x < 10 ^ (n + 1)) →
    l + codes.length ≤ bnd → bnd + (11 + codes.length) ≤ lim.space →
    ((10 ^ (n + 2) : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pSegBounds d [l, codes.length, (10 ^ n : ℕ), bnd] μ
      (c * (codes.length + 11)) fun _ μ' =>
      (∀ z ≤ 10, μ' (bnd + z) = segStart n codes z)
      ∧ (∀ z < 10, SegN μ' (bnd + 11 + segStart n codes z) (Spec.sliceList n z codes))
      ∧ SameOutside μ μ' bnd (11 + codes.length)

/-- union(pa, na, pb, nb, pc): writes the merge of two lists, a number that heads both being taken
once, to pc, and returns its length. -/
def UnionSpec : Prop :=
  ∀ (pa pb pc : ℕ) (la lb : List ℕ) (μ : ℕ → ℤ),
    SegN μ pa la → SegN μ pb lb → pa + la.length ≤ pc → pb + lb.length ≤ pc →
    pc + (la.length + lb.length) ≤ lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pUnion d [pa, la.length, pb, lb.length, pc] μ
      (c * (la.length + lb.length + 1)) fun r μ' =>
      r = ((Spec.mergeUnion la lb).length : ℕ) ∧ SegN μ' pc (Spec.mergeUnion la lb)
      ∧ SameOutside μ μ' pc (la.length + lb.length)

/-- The arguments of pick but for the mode, with the data behind them: the list small stands at
pSub, the list big at pU, the list values at pVal, and pDst is the destination. -/
structure PickArgs : Type where
  (pSub pU pVal pDst : ℕ)
  (small big : List ℕ) (values : List ℤ)

/-- The values of the arguments of pick. -/
abbrev PickArgs.vals (x : PickArgs) (add : ℕ) : List ℤ :=
  [x.pSub, x.small.length, x.pU, x.big.length, x.pVal, x.pDst, add]

/-- What pick assumes: big is an increasing list, values has a value for each of its numbers, and
small is an increasing list of numbers of big; all of it lies above the cells that pick writes. -/
structure PickPre (μ : ℕ → ℤ) (x : PickArgs) : Prop where
  small : SegN μ x.pSub x.small
  big : SegN μ x.pU x.big
  values : Seg μ x.pVal x.values
  len : x.values.length = x.big.length
  big_sorted : x.big.Pairwise (· < ·)
  small_sorted : x.small.Pairwise (· < ·)
  sub : ∀ c ∈ x.small, c ∈ x.big
  dst_sub : x.pDst + x.small.length ≤ x.pSub := by light_arith
  dst_big : x.pDst + x.small.length ≤ x.pU := by light_arith
  dst_val : x.pDst + x.small.length ≤ x.pVal := by light_arith
  sub_le : x.pSub + x.small.length ≤ lim.space := by light_arith
  big_le : x.pU + x.big.length ≤ lim.space := by light_arith
  val_le : x.pVal + x.big.length ≤ lim.space := by light_arith

/-- pick(pSub, nSub, pU, nU, pVal, pDst, 0): restriction of an array on a set to a subset (step (4)
of Pruned), in one walk through both lists: writes the values of the numbers of small to pDst. -/
def PickSetSpec : Prop :=
  ∀ (x : PickArgs) (μ : ℕ → ℤ), PickPre lim μ x →
    ∀ d, d ≤ lim.depth →
    Meets lim P pPick d (x.vals 0) μ (c * (x.small.length + x.big.length + 1)) fun _ μ' =>
      Seg μ' x.pDst (Spec.restrictList x.big x.values x.small) ∧
        SameOutside μ μ' x.pDst x.small.length

/-- pick(pSub, nSub, pU, nU, pVal, pDst, 1): the same, but the values are added to the cells from
pDst on, which hold the list acc. -/
def PickAddSpec : Prop :=
  ∀ (x : PickArgs) (acc : List ℤ) (μ : ℕ → ℤ), PickPre lim μ x → Seg μ x.pDst acc →
    acc.length = x.small.length →
    (∀ y ∈ List.zipWith (· + ·) acc (Spec.restrictList x.big x.values x.small), |y| ≤ lim.word) →
    ∀ d, d ≤ lim.depth →
    Meets lim P pPick d (x.vals 1) μ (c * (x.small.length + x.big.length + 1)) fun _ μ' =>
      Seg μ' x.pDst (List.zipWith (· + ·) acc (Spec.restrictList x.big x.values x.small))
      ∧ SameOutside μ μ' x.pDst x.small.length

/-- The arguments of pruned but for the number n of levels that are left, with the data behind them.
The two encodings are the lists EA at aEA and EB at aEB, and the parts of them below the current
vertex begin at the position base.  The list codes stands at l, the values are written to out, the
stack begins at sp, and the powers of ten up to 10^Lmax stand at p10.  A and B bound the numbers in
the two encodings. -/
structure PrunedArgs : Type where
  (aEA aEB base l out sp p10 : ℕ)
  (Lmax : ℕ) (EA EB : List ℤ) (codes : List ℕ) (A B : ℤ)

/-- The values of the arguments of pruned. -/
abbrev PrunedArgs.vals (x : PrunedArgs) (n : ℕ) : List ℤ :=
  [n, (x.aEA + x.base : ℕ), (x.aEB + x.base : ℕ), x.l, x.codes.length, x.out, x.sp, x.p10]

/-- What a call of pruned with n levels left assumes.  The list codes is an increasing list of
output strings, as numbers below 10^n.  The two encodings and the powers of ten lie below that list;
then come the cells of out, one for each code; then, from sp on, the stack, n frames of 3 len + 11
cells.  Sums of 10^n products of a number of EA and a number of EB fit in a word. -/
structure PrunedPre (μ : ℕ → ℤ) (n : ℕ) (x : PrunedArgs) : Prop where
  powers : Seg μ x.p10 (powList 10 (x.Lmax + 1))
  encA : Seg μ x.aEA x.EA
  encB : Seg μ x.aEB x.EB
  list : SegN μ x.l x.codes
  sorted : x.codes.Pairwise (· < ·)
  lt : ∀ c ∈ x.codes, c < 10 ^ n
  boundA : AbsLe x.EA x.A
  boundB : AbsLe x.EB x.B
  word : 10 ^ n * (x.A * x.B) ≤ lim.word
  pow : ((10 ^ (n + 1) : ℕ) : ℤ) ≤ lim.word
  levels : n ≤ x.Lmax := by light_arith
  partA : x.base + 10 ^ n ≤ x.EA.length := by light_arith
  partB : x.base + 10 ^ n ≤ x.EB.length := by light_arith
  belowPowers : x.p10 + (x.Lmax + 1) ≤ x.l := by light_arith
  belowA : x.aEA + x.EA.length ≤ x.l := by light_arith
  belowB : x.aEB + x.EB.length ≤ x.l := by light_arith
  belowOut : x.l + x.codes.length ≤ x.out := by light_arith
  belowStack : x.out + x.codes.length ≤ x.sp := by light_arith
  space : x.sp + n * (3 * x.codes.length + 11) ≤ lim.space := by light_arith

/-- pruned(n, ea, eb, l, len, out, sp, p10), the procedure Pruned of Section 2.4.2, recursive as
printed, on increasing lists of codes: a slice is a segment and a union of slices is a merge
(Section 2.4.4). ea = aEA + base and eb = aEB + base are the addresses at which the parts of the two
encodings below the current vertex begin. It writes the values, in the order of the list, to out,
and changes no other cell but those of its stack.
Time: c for each call and for each code passed to a call. -/
def PrunedSpec : Prop :=
  ∀ (n : ℕ) (x : PrunedArgs) (μ : ℕ → ℤ), PrunedPre lim μ n x →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pPruned d (x.vals n) μ (c * Spec.prunedWork n x.codes) fun _ μ' =>
      Seg μ' x.out (Spec.prunedList x.EA x.EB n x.base x.codes) ∧
        SameOutside2 μ μ' x.out x.codes.length x.sp (n * (3 * x.codes.length + 11))

/-- gather(w, perm, src, dst): dst[i] := src[perm[i]] for i < w. -/
def GatherSpec : Prop :=
  ∀ (w perm src dst : ℕ) (μ : ℕ → ℤ) (π : List ℕ),
    dst + w ≤ lim.space → π.length = w → SegN μ perm π → (∀ i ∈ π, i < w) →
    perm + w ≤ dst → src + w ≤ dst →
    ∀ d, d ≤ lim.depth → Meets lim P pGather d [w, perm, src, dst] μ (c * (w + 1)) fun _ μ' =>
      (∀ i (h : i < π.length), μ' (dst + i) = μ (src + π[i])) ∧ SameOutside μ μ' dst w

/-- The shape of the running time of Theorem 5's program; work is the sum over the tiles of the work
of the pruned recursions. -/
def thm5Shape (p : Par) (w work : ℕ) : ℕ :=
  sharedShape p + (w + 1) * (p.L + 1) + ((p.L + 1) * (w + 10) + p.nT + 1) + (work + p.nT + 1)
    + (w + 1) + (p.m + 1)

end Entries

end Light.Sec2
