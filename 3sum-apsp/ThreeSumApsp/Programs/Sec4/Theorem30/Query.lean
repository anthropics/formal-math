/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory
public import ThreeSumApsp.Programs.Sec4.Theorem30.RoutineFacts
public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums

/-!
# A query, from the block that holds the data structure (proof of Theorem 30, "Query")

"Given (I, J), we find its tile from the bands of row I and column J, the subset Q of its block
product, and its output string w […], all in O(L) operations". Below, the output string is called η.
queryAt(I, J, b0) has four parts. It reads the sizes, the addresses of the tables and the bands of I
and J from the block at b0 (queryAtReads), computes the addresses of the areas of Section 4
(queryAtAreas), lets outDigits write the digits of η (queryAtOut), reads the root of the trie of the
tile from the table of roots, and lets queryCore compute the sum of Lemma 28 from the two encodings
and this trie (queryAtCore). There is one lemma for each part; for each of the two calls a record
holds the arguments (outArgs, coreArgs) and a lemma says that the block holds what the routine
assumes (outArgs_pre, coreArgs_pre). queryAt_spec puts the four parts together.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace QueryAt

/-- The local variables of queryAt: the arguments I, J, b0; the sizes L, m, t, L - m, K₀, nB, 10^L;
the addresses of the tables BAND, BLOCK, DIG3 and of the area WD; the bands of I and J; the
addresses of the areas BOX, SS, ROOTS, TR; and a local for the result of outDigits, which is not
used. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Base : ℕ := 2
@[inherit_doc Row] abbrev Levels : ℕ := 3
@[inherit_doc Row] abbrev Inner : ℕ := 4
@[inherit_doc Row] abbrev Switch : ℕ := 5
@[inherit_doc Row] abbrev Outer : ℕ := 6
@[inherit_doc Row] abbrev Blocks : ℕ := 7
@[inherit_doc Row] abbrev Bands : ℕ := 8
@[inherit_doc Row] abbrev Leaves : ℕ := 9
@[inherit_doc Row] abbrev BandTab : ℕ := 10
@[inherit_doc Row] abbrev BlockTab : ℕ := 11
@[inherit_doc Row] abbrev DigitTab : ℕ := 12
@[inherit_doc Row] abbrev Digits : ℕ := 13
@[inherit_doc Row] abbrev BandI : ℕ := 14
@[inherit_doc Row] abbrev BandJ : ℕ := 15
@[inherit_doc Row] abbrev Box : ℕ := 16
@[inherit_doc Row] abbrev Str : ℕ := 17
@[inherit_doc Row] abbrev Roots : ℕ := 18
@[inherit_doc Row] abbrev Tries : ℕ := 19
@[inherit_doc Row] abbrev Void : ℕ := 20

end QueryAt

open QueryAt in
/-- The first part of queryAt(I, J, b0): what is read from the directory and from the table BAND. -/
def queryAtReads : Stmt :=
  .set Levels (M (v Base +' k Dir.levels)) ;;
  .set Inner (M (v Base +' k Dir.inner)) ;;
  .set Switch (M (v Base +' k Dir.switch)) ;;
  .set Outer (M (v Base +' k Dir.outer)) ;;
  .set Blocks (M (v Base +' k Dir.blocks)) ;;
  .set Bands (M (v Base +' k Dir.bands)) ;;
  .set Leaves (M (v Base +' k Dir.leaves)) ;;
  .set BandTab (M (v Base +' k Dir.band)) ;;
  .set BlockTab (M (v Base +' k Dir.block)) ;;
  .set DigitTab (M (v Base +' k Dir.digits)) ;;
  .set Digits (M (v Base +' k Dir.sharedEnd)) ;;
  .set BandI (M (v BandTab +' v Row)) ;;
  .set BandJ (M (v BandTab +' v Col))

open QueryAt in
/-- The second part: the areas of Section 4 lie one behind the other from WD on. -/
def queryAtAreas : Stmt :=
  .set Box (v Digits +' v Levels +' v Levels) ;;
  .set Str (v Box +' v Levels) ;;
  .set Roots (v Str +' v Inner +' k 1) ;;
  .set Tries (v Roots +' v Bands *' v Bands)

open QueryAt in
/-- The call of outDigits: the digits of the output string. -/
def queryAtOut : Stmt :=
  .call Proc.outDigits [M (v BlockTab +' v Row), M (v BlockTab +' v Col),
    v DigitTab +' v Row *' v Outer, v DigitTab +' v Col *' v Outer, M (v Base +' k Dir.mask),
    v Blocks, v Levels, v Digits] Void

open QueryAt in
/-- The call of queryCore: the sum of Lemma 28. The tile of (I, J) has the number bandI nB + bandJ,
and the root of its trie is read from the table of roots. -/
def queryAtCore : Stmt :=
  .call Proc.queryCore [M (v Base +' k Dir.encA) +' v BandI *' v Leaves,
    M (v Base +' k Dir.encB) +' v BandJ *' v Leaves, v Tries,
    M (v Roots +' (v BandI *' v Bands +' v BandJ)), v Digits, v Str, v Box, v Levels, v Inner,
    v Switch] Row

/-- queryAt(I, J, b0) returns (XY)[I, J]: the result of a procedure is its local 0, into which the
last call stores. -/
def queryAtBody : Stmt := queryAtReads ;; queryAtAreas ;; queryAtOut ;; queryAtCore

/-- What the locals hold after the first part. -/
def queryAtRead (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  [I, J, b0, p.L, p.m, t, p.Lo, p.K0, p.nB, p.T, p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, aWD p b0,
    (I / (p.K0 * p.N0) : ℕ), (J / (p.K0 * p.N0) : ℕ)]

/-- What the locals hold after the second part. -/
def queryAtLocals (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  queryAtRead p t b0 I J ++ [(aBOX p b0 : ℤ), aSS p b0, aROOTS p b0, aTR p b0]

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first two parts -/

/-- The first part reads the sizes, the addresses of the tables, and the two bands. -/
theorem queryAtReads_spec (hlim : Lim30 lim p t b0 U) (hds : DSReady p t hmL aX aY b0 X Y μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) :
    Ends lim P d queryAtReads ⟨frame [(I : ℤ), (J : ℤ), (b0 : ℤ)], μ⟩ 90
      (· = ⟨frame (queryAtRead p t b0 I J), μ⟩) := by
  have hw := hlim.std.space_le
  have hdir : b0 + 31 < lim.space ∧ p.aBAND b0 + p.N ≤ lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have dir := hds.shared.dirCells
  have cellT : μ ((b0 : ℤ) + 31).toNat = (t : ℕ) :=
    (congrArg μ (toNat_natCast_add_natCast b0 31)).trans hds.cellT
  have bandI := hds.shared.band I hI
  have bandJ := hds.shared.band J hJ
  -- levels := dir[0]; inner := dir[1]; switch := dir[31]; outer := dir[4]
  light_set (p.L : ℕ) using dir.levels
  light_set (p.m : ℕ) using dir.inner
  light_set (t : ℕ) using cellT
  light_set (p.Lo : ℕ) using dir.outer
  -- blocks := dir[7]; bands := dir[9]; leaves := dir[10]
  light_set (p.K0 : ℕ) using dir.blocks
  light_set (p.nB : ℕ) using dir.bands
  light_set (p.T : ℕ) using dir.leaves
  -- bandTab := dir[22]; blockTab := dir[23]; digitTab := dir[24]; digits := dir[30]
  light_set (p.aBAND b0 : ℕ) using dir.band
  light_set (p.aBLOCK b0 : ℕ) using dir.block
  light_set (p.aDIG3 b0 : ℕ) using dir.digits
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  -- bandI := bandTab[I]; bandJ := bandTab[J]
  light_set (I / (p.K0 * p.N0) : ℕ) using bandI
  light_set (J / (p.K0 * p.N0) : ℕ) using bandJ
  rfl

/-- The second part computes the addresses of the areas of Section 4. -/
theorem queryAtAreas_spec (hlim : Lim30 lim p t b0 U) (I J : ℕ) :
    Ends lim P d queryAtAreas ⟨frame (queryAtRead p t b0 I J), μ⟩ 50
      (· = ⟨frame (queryAtLocals p t b0 I J), μ⟩) := by
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold queryAtLocals queryAtRead
  -- the product nB², in the integers
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have hsq0 : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at htr
  -- box := digits + L + L; str := box + L; roots := str + m + 1
  light_set (aBOX p b0 : ℕ)
  light_set (aSS p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  -- tries := roots + nB nB
  light_set (aTR p b0 : ℕ)
  rfl

/-! ## The call of outDigits -/

/-- Bits as natural numbers. -/
theorem segN_of_segB {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : Sec2.SegB μ a l) :
    SegN μ a (l.map fun b => if b then 1 else 0) := by
  unfold Sec2.SegB at h
  unfold SegN
  rw [List.map_map]
  convert h using 2
  funext b
  cases b <;> simp

/-- The arguments of the call of outDigits, and the data behind them. -/
def outArgs (p : Sec2.Par) (b0 I J : ℕ) : OutDigitsArgs :=
  ⟨I / p.N0 % p.K0, J / p.N0 % p.K0, p.aDIG3 b0 + I * p.Lo, p.aDIG3 b0 + J * p.Lo, p.aMASK b0, p.K0,
    p.L, aWD p b0, p.m, digitList 3 p.Lo (I % p.N0), digitList 3 p.Lo (J % p.N0)⟩

/-- The block holds what outDigits assumes. -/
theorem outArgs_pre (hlim : Lim30 lim p t b0 U) (hds : DSReady p t hmL aX aY b0 X Y μ) {I J : ℕ}
    (hI : I < p.N) (hJ : J < p.N) : OutDigitsPre lim μ (outArgs p b0 I J) := by
  have hgI : I / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hgJ : J / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hidx : I / p.N0 % p.K0 * p.K0 + J / p.N0 % p.K0 < p.KK := Nat.mul_add_lt_mul hgI hgJ
  -- the three tables lie below WD, and WD inside the memory
  have hsp := hlim.space
  have hmaskI := Nat.mul_add_le_mul hidx (le_refl p.L)
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hLo : p.L - p.m = p.Lo := rfl
  obtain ⟨⟩ := areas p t b0
  refine'
    { std := hlim.std
      m_le := hmL
      gI_lt := hgI
      gJ_lt := hgJ
      index_lt := tableIndex_lt p.L p.m (⟨_, hgI⟩, ⟨_, hgJ⟩)
      segMask := segN_of_segB (hds.shared.mask _ hidx)
      segI := hds.shared.dig3 I hI
      segJ := hds.shared.dig3 J hJ
      lenI := length_digitList ..
      lenJ := length_digitList ..
      ltI := fun _ => lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => lt_of_mem_digitList (by norm_num)
      spaceMasks := by change p.aMASK b0 + p.KK * p.L < lim.space; omega
      .. }
  -- the six fields that are left: the tables lie apart from WD, and all within the memory
  all_goals
    simp only [outArgs, OutDigitsArgs.base]
    omega

/-- The third part writes the digits of the output string of (I, J) at WD. -/
theorem queryAtOut_spec (hOut : OutDigitsSpec lim P) (hlim : Lim30 lim p t b0 U)
    (hds : DSReady p t hmL aX aY b0 X Y μ) {I J : ℕ} (hI : I < p.N) (hJ : J < p.N)
    (hd : d + 1 ≤ lim.depth) :
    Ends lim P d queryAtOut ⟨frame (queryAtLocals p t b0 I J), μ⟩ (tOutDigits p.L + 40) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ'⟩ ∧
        SegN μ' (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J)) ∧
        SameOutside μ μ' (aWD p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := outArgs_pre hlim hds hI hJ
  have blockI := hds.shared.block I hI
  have blockJ := hds.shared.block J hJ
  have hsp := hlim.space
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hbound : b0 + 31 < lim.space ∧ p.aBLOCK b0 + p.N ≤ lim.space ∧
      p.aDIG3 b0 + p.N * p.Lo ≤ lim.space := by
    obtain ⟨⟩ := areas p t b0
    omega
  have hprodI : ((p.aDIG3 b0 + I * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + I * p.Lo ≤ lim.space)
  have hprodJ : ((p.aDIG3 b0 + J * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + J * p.Lo ≤ lim.space)
  have hI0 : (0 : ℤ) ≤ (I : ℤ) * p.Lo := by positivity
  have hJ0 : (0 : ℤ) ≤ (J : ℤ) * p.Lo := by positivity
  push_cast at hprodI hprodJ
  -- outDigits(blockTab[I], blockTab[J], digitTab + I (L - m), digitTab + J (L - m), dir[21], …)
  light_call (hOut _ μ hpre) using queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
    hds.shared.dirCells.mask with r μ' h
  refine ⟨r, μ', rfl, ?_, h.2⟩
  rw [digitsO_outStrOfPos]
  exact h.1

/-! ## The call of queryCore -/

/-- The number of the tile of the position (I, J). -/
def tileOf (p : Sec2.Par) (I J : ℕ) : ℕ := I / (p.K0 * p.N0) * p.nB + J / (p.K0 * p.N0)

/-- The arguments of the call of queryCore, and the data behind them. -/
def coreArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (I J : ℕ) :
    QueryCoreArgs where
  L := p.L
  m := p.m
  t := t
  encA := encRow p hmL X (I / (p.K0 * p.N0))
  encB := encCol p hmL Y (J / (p.K0 * p.N0))
  η := outStrOfPos (stdLayout hmL) I J
  aA := p.aENCA b0 + I / (p.K0 * p.N0) * p.T
  aB := p.aENCB b0 + J / (p.K0 * p.N0) * p.T
  tr := aTR p b0
  root := (dsTries p t hmL X Y).root (tileOf p I J)
  wd := aWD p b0
  ss := aSS p b0
  box := aBOX p b0
  T := (dsTries p t hmL X Y).cells

/-- Every product of two encoded numbers fits in a word. -/
theorem abs_enc_mul_le (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) (τ : Leaf p.L) :
    |encRow p hmL X β τ * encCol p hmL Y β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY β β'
  rw [abs_mul]
  calc |encRow p hmL X β τ| * |encCol p hmL Y β' τ| ≤ (7 ^ p.L * U) * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ lim.word := hlim.value

section Tile

variable (I J : Fin p.N)

/-- The tile of the position (I, J) is one of the nB² tiles. -/
theorem tileOf_lt (hmL : p.m ≤ p.L) : tileOf p I J < p.nB * p.nB :=
  Nat.mul_add_lt_mul (bandOf_lt_numBands hmL p.N I I.isLt) (bandOf_lt_numBands hmL p.N J J.isLt)

/-- It is given by the encodings of the band of I and of the band of J. -/
theorem getElem?_tileOf :
    (tileList p.nB (encRow p hmL X) (encCol p hmL Y))[tileOf p I J]?
      = some ⟨arrT (coreArgs p t hmL b0 X Y I J).encA, arrT (coreArgs p t hmL b0 X Y I J).encB⟩ :=
  getElem?_tileList p.nB _ _ (bandOf_lt_numBands hmL p.N I I.isLt)
    (bandOf_lt_numBands hmL p.N J J.isLt)

variable (ht : t ≤ p.m)

include ht

/-- Every box of the query is found in the trie of the tile. -/
theorem coreArgs_walk (l : List ℕ)
    (hl : l ∈ boxesOf p.m t (digitsO (coreArgs p t hmL b0 X Y I J).η)) :
    WalkOK (coreArgs p t hmL b0 X Y I J).T (coreArgs p t hmL b0 X Y I J).root l :=
  walkOK_allTries ht (getElem?_tileOf (t := t) (b0 := b0) I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J) hl

/-- Every partial sum of the query fits in a word. -/
theorem coreArgs_sums (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (j : ℕ) :
    |((coreArgs p t hmL b0 X Y I J).terms.take j).sum| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY ((I : ℕ) / (p.K0 * p.N0))
    ((J : ℕ) / (p.K0 * p.N0))
  have hcard := card_innerSetO_outStrOfPos (stdLayout hmL) I J
  have hterms := queryTerms_allTries ht
    (getElem?_tileOf (t := t) (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J) hcard
  rw [QueryCoreArgs.terms]
  exact (congrArg (fun l => |(l.take j).sum|) hterms).trans_le
    ((abs_query_partial_sum_le hrow hcol ht hcard j).trans hlim.value)

/-- What queryCore returns for the tile of (I, J) is (XY)[I, J], by Theorem 30. -/
theorem coreArgs_value :
    trieQuery p.m t (arrT (coreArgs p t hmL b0 X Y I J).encA)
      (arrT (coreArgs p t hmL b0 X Y I J).encB) (coreArgs p t hmL b0 X Y I J).T
      (coreArgs p t hmL b0 X Y I J).root (digitsO (coreArgs p t hmL b0 X Y I J).η) = (X * Y) I J :=
  (trieQuery_allTries ht _ _ (getElem?_tileOf I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J)).trans
    (Theorem30.correct t ht (stdLayout hmL) X Y I J)

end Tile

/-- The block, with the digits of the output string at WD, holds what queryCore assumes. -/
theorem coreArgs_pre (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReady p t hmL aX aY b0 X Y μ) (I J : Fin p.N)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    QueryCorePre lim μ (coreArgs p t hmL b0 X Y I J) := by
  have hU : 0 ≤ U := (abs_nonneg _).trans (hX I ⟨0, Nat.pow_pos (by norm_num)⟩)
  have hβ : (I : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N I I.isLt
  have hβ' : (J : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N J J.isLt
  -- the encodings lie below WD, the tries behind the scratch strings
  have hsp := hlim.space
  have hlen := length_dsTries_le p t hmL X Y
  have hrowA := Nat.mul_add_le_mul hβ (le_refl p.T)
  have hrowB := Nat.mul_add_le_mul hβ' (le_refl p.T)
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  refine'
    { std := hlim.std
      t_le := ht
      card := card_innerSetO_outStrOfPos (stdLayout hmL) I J
      segA := hds.shared.encA _ hβ
      segB := hds.shared.encB _ hβ'
      segT := hds.trie
      segDigits := hwd
      walk := coreArgs_walk I J ht
      sums := coreArgs_sums I J ht hlim hU hX hY
      prod := abs_enc_mul_le hlim hU hX hY _ _
      pow := hlim.pow_le
      .. }
  -- the fifteen fields that are left: the areas lie apart from each other and within the memory
  all_goals
    simp only [coreArgs]
    omega

/-- The fourth part returns (XY)[I, J] and changes the scratch strings BOX and SS only. -/
theorem queryAtCore_spec (hCore : QueryCoreSpec lim P) (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReady p t hmL aX aY b0 X Y μ)
    (I J : Fin p.N) (hd : d + 2 ≤ lim.depth) (r : ℤ)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    Ends lim P d queryAtCore ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ⟩
      (tQueryCore p.L p.m t + 60) fun σ' =>
        σ'.loc 0 = (X * Y) I J ∧ SameOutside2 μ σ'.mem (aSS p b0) p.m (aBOX p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := coreArgs_pre ht hlim hX hY hds I J hwd
  have hvalue := coreArgs_value (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J ht
  have dir := hds.shared.dirCells
  have htile := tileOf_lt I J hmL
  have cellRoot : μ (aROOTS p b0 + tileOf p I J)
      = ((dsTries p t hmL X Y).root (tileOf p I J) : ℕ) :=
    hds.roots.read (by rw [length_dsTries_roots]; exact htile)
  have hdir : b0 + 31 < lim.space ∧ aROOTS p b0 + p.nB * p.nB < lim.space := by
    have hsp := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have hmeets := (hCore _ μ hpre _ (by omega))
  have hencA := hpre.aA_lt
  have hencB := hpre.aB_lt
  simp only [coreArgs, tileOf] at hmeets hvalue hencA hencB htile cellRoot
  unfold queryAtLocals queryAtRead
  -- the bands, the root and 10^L become variables; the products in the arguments, in the integers
  generalize 10 ^ p.L = leaves at hencA hencB
  generalize (I : ℕ) / (p.K0 * p.N0) = β at *
  generalize (J : ℕ) / (p.K0 * p.N0) = β' at *
  generalize (dsTries p t hmL X Y).root (β * p.nB + β') = root at *
  have hencA' : ((p.aENCA b0 + β * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hencB' : ((p.aENCB b0 + β' * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hroot' : ((aROOTS p b0 + (β * p.nB + β') : ℕ) : ℤ) < lim.space := by
    exact_mod_cast (by omega)
  have hrow0 : (0 : ℤ) ≤ (β : ℤ) * p.T := by positivity
  have hcol0 : (0 : ℤ) ≤ (β' : ℤ) * p.T := by positivity
  have hband0 : (0 : ℤ) ≤ (β : ℤ) * p.nB := by positivity
  have haddr : ((aROOTS p b0 : ℤ) + ((β : ℤ) * p.nB + β')).toNat
      = aROOTS p b0 + (β * p.nB + β') := by exact_mod_cast Int.toNat_natCast _
  push_cast at hencA' hencB' hroot'
  -- queryCore(dir[26] + bandI 10^L, dir[27] + bandJ 10^L, tries, roots[bandI nB + bandJ], …)
  light_call hmeets using dir.encA, dir.encB, haddr, cellRoot with r' μ' h
  refine ⟨?_, h.2⟩
  simp only [setLocal, List.cons_append, frame, List.getD_cons_zero]
  rw [h.1, hvalue]

/-! ## The routine -/

/-- **queryAt** meets its specification. -/
theorem queryAt_spec (hP : P[Proc.queryAt]? = some queryAtBody) (hOut : OutDigitsSpec lim P)
    (hCore : QueryCoreSpec lim P) : QueryAtSpec lim P := by
  intro p t hmL aX aY b0 X Y U μ I J ht hlim hX hY hds
  refine fun d hd => ⟨queryAtBody, hP, ?_⟩
  unfold tQueryAt
  -- the sizes, the tables, the bands
  light_piece (queryAtReads_spec hlim hds I.isLt J.isLt) with _ rfl
  -- the areas
  light_piece (queryAtAreas_spec hlim I J) with _ rfl
  -- the digits of the output string, which change WD only
  light_piece (queryAtOut_spec hOut hlim hds I.isLt J.isLt (by omega))
    with _ ⟨r, μ₁, rfl, hwd, same₁⟩
  have same₁' : SameOutside μ μ₁ (aWD p b0) (3 * p.L + p.m) := same₁.mono le_rfl (by omega)
  -- the sum of Lemma 28, which changes BOX and SS only
  light_piece (queryAtCore_spec hCore ht hlim hX hY (hds.of_same same₁') I J (by omega) r hwd)
    with ⟨loc₂, μ₂⟩ ⟨hr, same₂⟩
  have same₂' : SameOutside μ μ₂ (aWD p b0) (3 * p.L + p.m) := by
    obtain ⟨⟩ := areas p t b0
    exact same₁'.then same₂ fun b hb => ⟨hb, by omega, by omega⟩
  exact ⟨hr, hds.of_same same₂', same₂'⟩

end Proof

end Light.Sec4
