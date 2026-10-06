/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays
public import ThreeSumApsp.Spec.Sec2.Theorem5.Subsets
public import ThreeSumApsp.Util.Counting
public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Util.Weave

/-!
# One computable layout of the tiling

The statements of Section 2.3.4 about the tiling hold for every `Layout`: every numbering of the
rows and columns of a block by strings, and every table of `K₀²` subsets of size `m`.  A
program needs one layout that it can compute.  In `stdLayout` the rows and columns of a block are
numbered by the base-3 codes of their strings, the columns of `X` by base-4 codes, and the block
product `(g, h)` of a tile gets the subset number `g K₀ + h` of the enumeration `unrank`.

The strings of Lemma 9 are glued from an inner part, at the levels of a set `Q`, and an outer part,
at the other levels.  Their codes are formed digit by digit:

1. the digits of a glued string are the digits of its two parts, interleaved along the mask of `Q`
   by `weaveList` (`ofFn_glue`), because the `k`-th level of `Q` has exactly `k` levels of `Q` below
   it (`Finset.card_filter_lt_orderEmbOfFin`, `count_take_maskOf`);
2. so `outDigitsOfPos` lists the digits, and `outCodeOfPos` is the code, of the output string of a
   position `(I, J)` (Section 2.4.4, `codeO_outStrOfPos`, `digitList_outCodeOfPos`);
3. and `gluedCode` is the code of the left or right string with given parts (`codeL_leftStrOf`,
   `codeR_rightStrOf`).  The input array of a band holds the entries of `X` or `Y` at these codes
   and 0 elsewhere (`bandArrayL_at`, `bandArrayL_eq_zero`, and the same for `R`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The layout -/

/-- `g K₀ + h` is below `binom(L, m)` for `g, h < K₀`. -/
theorem tableIndex_lt (L m : ℕ) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (gh.1 : ℕ) * K0 L m + gh.2 < L.choose m :=
  (Nat.mul_add_lt_mul gh.1.isLt gh.2.isLt).trans_le (Nat.sqrt_le _)

/-- The computable layout: the rows and columns of a block are numbered by the base-3 codes of their
strings, the columns of `X` by base-4 codes, and the block product `(g, h)` of a tile gets the
subset number `g K₀ + h` of the enumeration `unrank`. -/
def stdLayout {L m : ℕ} (hmL : m ≤ L) : Layout L m where
  hmL := hmL
  rowIdx := (codeEquiv 3 (L - m)).symm
  colIdx := (codeEquiv 3 (L - m)).symm
  innerIdx := (strEquiv pairEquiv m).symm
  table gh := maskSet L (unrank L m (gh.1 * K0 L m + gh.2))
  table_card gh := card_maskSet_unrank (tableIndex_lt L m gh)
  table_injective gh gh' h := by
    obtain ⟨hg, hh⟩ := Nat.mul_add_inj_of_lt gh.2.isLt gh'.2.isLt
      (eq_of_maskSet_unrank_eq (tableIndex_lt L m gh) (tableIndex_lt L m gh') h)
    exact Prod.ext (Fin.ext hg) (Fin.ext hh)

section
variable {L m : ℕ} (hmL : m ≤ L)

/-- The row with number `k` of a block is indexed by the string with code `k`. -/
private theorem codeOuter_rowIdx (k : Fin (N0 L m)) : codeOuter ((stdLayout hmL).rowIdx k) = k :=
  congrArg Fin.val ((codeEquiv 3 (L - m)).apply_symm_apply k)

/-- The column with number `k` of a block is indexed by the string with code `k`. -/
private theorem codeOuter_colIdx (k : Fin (N0 L m)) : codeOuter ((stdLayout hmL).colIdx k) = k :=
  codeOuter_rowIdx hmL k

/-- The string that indexes the row with number `k` of a block consists of the base-3 digits of
`k`. -/
private theorem ofFn_rowIdx (k : Fin (N0 L m)) :
    (List.ofFn fun ℓ => ((stdLayout hmL).rowIdx k ℓ : ℕ)) = digitList 3 (L - m) k :=
  (digitList_codeStr (Equiv.refl (Fin 3)) _).symm.trans
    (congrArg (digitList 3 (L - m)) (codeOuter_rowIdx hmL k))

/-- The string that indexes the column with number `k` of a block consists of the base-3 digits of
`k`. -/
private theorem ofFn_colIdx (k : Fin (N0 L m)) :
    (List.ofFn fun ℓ => ((stdLayout hmL).colIdx k ℓ : ℕ)) = digitList 3 (L - m) k :=
  ofFn_rowIdx hmL k

/-- The column with number `k` of `X` is indexed by the string with code `k`. -/
private theorem codeInner_innerIdx (k : Fin (D m)) : codeInner ((stdLayout hmL).innerIdx k) = k :=
  -- The number that `strEquiv` gives to a string is its code, by definition.
  congrArg Fin.val ((strEquiv pairEquiv m).apply_symm_apply k)

/-- The mask of the subset of a block product. -/
private theorem maskOf_table (gh : Fin (K0 L m) × Fin (K0 L m)) :
    maskOf ((stdLayout hmL).table gh) = unrank L m (gh.1 * K0 L m + gh.2) :=
  maskOf_maskSet _ (length_unrank _ _ _)

end

/-! ## Counting the levels of a set below a level -/

/-- The entries `true` (and `false`) among the first `n` entries of the mask of `Q` count the levels
of `Q` (and outside `Q`) below `n`. -/
private theorem count_take_maskOf {L : ℕ} (Q : Finset (Fin L)) (n : ℕ) :
    ((maskOf Q).take n).count true = (Q.filter fun x : Fin L => (x : ℕ) < n).card ∧
      ((maskOf Q).take n).count false = (Qᶜ.filter fun x : Fin L => (x : ℕ) < n).card := by
  constructor <;> rw [maskOf, List.count_take_ofFn] <;> congr 1 <;> ext x <;> simp [and_comm]

/-! ## The code of a glued string -/

/-- The digits of a string glued from `inner` at the levels of `Q` and `outer` at the other levels
are interleaved along the mask of `Q`. -/
theorem ofFn_glue {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (inner : Fin m → ℕ)
    (outer : Fin (L - m) → ℕ) :
    List.ofFn (glue Q hQ inner outer)
      = weaveList (maskOf Q) (List.ofFn outer) (List.ofFn inner) := by
  refine List.ext_getElem (by simp [length_maskOf]) fun n hn hweave => ?_
  replace hn : n < L := by simpa using hn
  obtain ⟨htrue, hfalse⟩ := count_take_maskOf Q n
  rw [List.getElem_ofFn, ← List.getD_eq_getElem _ 0 hweave, getD_weaveList,
    if_pos (by rwa [length_maskOf]), htrue, hfalse, getD_maskOf Q hn]
  by_cases hmem : (⟨n, hn⟩ : Fin L) ∈ Q
  · -- Level `n` is the `k`-th level of `Q`, and `k` levels of `Q` lie below it.
    obtain ⟨k, hk⟩ := exists_innerLevel Q hQ hmem
    have hcount := Finset.card_filter_lt_orderEmbOfFin Q hQ k
    rw [show ((Q.orderEmbOfFin hQ k : Fin L) : ℕ) = n from congrArg Fin.val hk] at hcount
    rw [← hk, glue_innerLevel, hk, hcount]
    simp [hmem]
  · -- Level `n` is the `k`-th level outside `Q`, and `k` levels outside `Q` lie below it.
    obtain ⟨k, hk⟩ := exists_outerLevel Q hQ hmem
    have hcount := Finset.card_filter_lt_orderEmbOfFin Qᶜ (card_compl_of_card_eq Q hQ) k
    rw [show ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ) k : Fin L) : ℕ) = n from
      congrArg Fin.val hk] at hcount
    rw [← hk, glue_outerLevel, hk, hcount]
    simp [hmem]

/-- The code of a string of digits glued from `inner` at the levels of `Q` and `outer` at the other
levels, by Horner's rule on the interleaved digits. -/
theorem code_glue (b : ℕ) {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (inner : Fin m → ℕ)
    (outer : Fin (L - m) → ℕ) :
    code b (glue Q hQ inner outer)
      = ofDigitList b (weaveList (maskOf Q) (List.ofFn outer) (List.ofFn inner)) := by
  rw [code_eq_ofDigitList, ofFn_glue]

/-! ## The digits and the code of the output string of a position -/

section outDigits
variable {m ℓ : ℕ} {mask : List Bool} {rI rJ : List ℕ}

/-- The digits of the output string whose inner set has the mask `mask`, with `m` levels, and whose
row and column have the digits `rI` and `rJ` in base 3: 9 at the levels of the set, and `3 x + y` at
the other levels, where `x` and `y` run through `rI` and `rJ`. -/
def outDigits (m : ℕ) (mask : List Bool) (rI rJ : List ℕ) : List ℕ :=
  weaveList mask (List.zipWith (fun x y => 3 * x + y) rI rJ) (List.replicate m 9)

/-- An output string has one digit for each level. -/
@[simp] theorem length_outDigits : (outDigits m mask rI rJ).length = mask.length :=
  length_weaveList ..

/-- The digit at a level of the inner set is 9. -/
theorem getD_outDigits_of_true (hm : mask.count true = m) (hℓ : ℓ < mask.length)
    (hb : mask.getD ℓ false = true) : (outDigits m mask rI rJ).getD ℓ 0 = 9 := by
  have hlt := List.count_take_lt hℓ false hb
  rw [outDigits, getD_weaveList, if_pos hℓ, if_pos hb,
    List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega), List.getElem_replicate]

/-- The digit at a level outside the inner set is `3 x + y` for the next digits `x` of the row and
`y` of the column. -/
theorem getD_outDigits_of_false (hI : rI.length = mask.count false)
    (hJ : rJ.length = mask.count false) (hℓ : ℓ < mask.length) (hb : mask.getD ℓ false = false) :
    (outDigits m mask rI rJ).getD ℓ 0
      = 3 * rI.getD ((mask.take ℓ).count false) 0 + rJ.getD ((mask.take ℓ).count false) 0 := by
  have hlt := List.count_take_lt hℓ false hb
  rw [outDigits, getD_weaveList, if_pos hℓ, if_neg (by rw [hb]; exact Bool.false_ne_true),
    List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

/-- The digits of an output string are below 10. -/
theorem lt_of_mem_outDigits (hI : ∀ x ∈ rI, x < 3) (hJ : ∀ y ∈ rJ, y < 3) :
    ∀ d ∈ outDigits m mask rI rJ, d < 10 := by
  refine lt_of_mem_weaveList (by norm_num) (fun d hd => ?_) fun d hd => ?_
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    rw [List.length_zipWith, lt_min_iff] at hi
    have hx := hI _ (List.getElem_mem hi.1)
    have hy := hJ _ (List.getElem_mem hi.2)
    rw [List.getElem_zipWith]
    omega
  · rw [List.eq_of_mem_replicate hd]
    norm_num

end outDigits

/-- The code of the output string with inner set `Q`, row `r` and column `c`. -/
theorem codeO_outStrOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (r c : OuterStr L m) :
    codeO (outStrOf Q hQ r c)
      = ofDigitList 10 (outDigits m (maskOf Q) (List.ofFn fun k => (r k : ℕ))
          (List.ofFn fun k => (c k : ℕ))) := by
  rw [outStrOf, codeO, codeStr,
    map_glue Q hQ (fun z => ((outEquiv z : Fin 10) : ℕ)), code_glue, outDigits,
    ← List.ofFn_const]
  simp only [outEquiv_apply, outIdx_z, outIdx_z0]
  congr 2
  exact List.ext_getElem (by simp) fun n _ _ => by simp

/-- The number, in the enumeration `unrank`, of the subset of the block product of the position
`(I, J)`. -/
def maskNo (L m I J : ℕ) : ℕ := I / N0 L m % K0 L m * K0 L m + J / N0 L m % K0 L m

/-- The subset of a position is one of the subsets of size `m`. -/
theorem maskNo_lt {L m : ℕ} (hmL : m ≤ L) (I J : ℕ) : maskNo L m I J < L.choose m :=
  tableIndex_lt L m (⟨_, Nat.mod_lt _ (K0_pos hmL)⟩, ⟨_, Nat.mod_lt _ (K0_pos hmL)⟩)

/-- The digits of the output string of the position `(I, J)`, from the block numbers and the base-3
digits of the offsets of `I` and `J`. -/
def outDigitsOfPos (L m I J : ℕ) : List ℕ :=
  outDigits m (unrank L m (maskNo L m I J)) (digitList 3 (L - m) (I % N0 L m))
    (digitList 3 (L - m) (J % N0 L m))

/-- The code of the output string of the position `(I, J)`: Horner's rule on its digits. -/
def outCodeOfPos (L m I J : ℕ) : ℕ := ofDigitList 10 (outDigitsOfPos L m I J)

/-- The output string of a position has `L` digits. -/
@[simp] theorem length_outDigitsOfPos (L m I J : ℕ) : (outDigitsOfPos L m I J).length = L := by
  rw [outDigitsOfPos, length_outDigits, length_unrank]

/-- The digits of the code of the output string of a position. -/
theorem digitList_outCodeOfPos (L m I J : ℕ) :
    digitList 10 L (outCodeOfPos L m I J) = outDigitsOfPos L m I J := by
  have hdigits := digitList_ofDigitList (outDigitsOfPos L m I J)
    (lt_of_mem_outDigits (fun _ => lt_of_mem_digitList (by norm_num))
      fun _ => lt_of_mem_digitList (by norm_num))
  rwa [length_outDigitsOfPos] at hdigits

/-- `outCodeOfPos` computes the code of the output string of a position, for the computable layout.
-/
theorem codeO_outStrOfPos {L m : ℕ} (hmL : m ≤ L) (I J : ℕ) :
    codeO (outStrOfPos (stdLayout hmL) I J) = outCodeOfPos L m I J := by
  rw [outStrOfPos, codeO_outStrOf, outCodeOfPos, outDigitsOfPos, maskOf_table, ofFn_rowIdx,
    ofFn_colIdx]
  -- By definition the block of `I` is `I / N₀ % K₀`, and its offset is `I % N₀`.
  rfl

/-! ## The codes of the left and right strings, and the input arrays of the bands -/

/-- The digits of the left string with inner set given by `mask`, outer part with the digits `o` and
inner part with the digits `i`: `o_j` at the `j`-th level outside the set, and `3 + i_j` at the
`j`-th level of the set.  The right string with the same parts has the same digits. -/
def gluedDigits (mask : List Bool) (o i : List ℕ) : List ℕ := weaveList mask o (i.map (3 + ·))

/-- A left or right string has one digit for each level. -/
@[simp] theorem length_gluedDigits (mask : List Bool) (o i : List ℕ) :
    (gluedDigits mask o i).length = mask.length :=
  length_weaveList ..

/-- The digits of a left or right string are below 7. -/
theorem lt_of_mem_gluedDigits {mask : List Bool} {o i : List ℕ} (ho : ∀ x ∈ o, x < 3)
    (hi : ∀ x ∈ i, x < 4) : ∀ d ∈ gluedDigits mask o i, d < 7 := by
  refine lt_of_mem_weaveList (by norm_num) (fun d hd => (ho d hd).trans (by norm_num))
    fun d hd => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
  have hlt := hi x hx
  omega

/-- The code of the left string, and of the right string, with inner set given by `mask`, outer part
with code `r` and inner part with code `k`. -/
def gluedCode (L m : ℕ) (mask : List Bool) (r k : ℕ) : ℕ :=
  ofDigitList 7 (gluedDigits mask (digitList 3 (L - m) r) (digitList 4 m k))

/-- The code of a left or right string of `L` levels is below `7^L`. -/
theorem gluedCode_lt {L : ℕ} (m : ℕ) {mask : List Bool} (hmask : mask.length = L) (r k : ℕ) :
    gluedCode L m mask r k < 7 ^ L := by
  have hlt := ofDigitList_lt (gluedDigits mask (digitList 3 (L - m) r) (digitList 4 m k))
    (lt_of_mem_gluedDigits (fun _ => lt_of_mem_digitList (by norm_num))
      fun _ => lt_of_mem_digitList (by norm_num))
  rwa [length_gluedDigits, hmask] at hlt

/-- Left and right strings at once: over an alphabet of seven letters in which the outer letter
number `i` has the digit `i` and the inner letter of the pair `p` the digit 3 plus the digit of `p`,
the string glued from the inner letters of `π` and the outer letters of `r` has the code
`gluedCode`. -/
private theorem codeStr_glue {α : Type} (e : α ≃ Fin 7) {inner : Fin 2 × Fin 2 → α}
    {outer : Fin 3 → α} (hinner : ∀ p, (e (inner p) : ℕ) = 3 + pairIdx p)
    (houter : ∀ i, (e (outer i) : ℕ) = i) {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r : OuterStr L m) (π : InnerStr m) :
    codeStr e (glue Q hQ (fun k => inner (π k)) fun k => outer (r k))
      = gluedCode L m (maskOf Q) (codeOuter r) (codeInner π) := by
  rw [gluedCode, gluedDigits, codeOuter, codeInner, digitList_codeStr, digitList_codeStr,
    List.map_ofFn, codeStr, map_glue Q hQ (fun s => ((e s : Fin 7) : ℕ)), code_glue]
  simp only [hinner, houter, pairEquiv_apply, Equiv.refl_apply, Function.comp_def]

/-- The code of the left string with inner set `Q`, outer part `r` and inner part `π`. -/
theorem codeL_leftStrOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (r : OuterStr L m)
    (π : InnerStr m) :
    codeL (leftStrOf Q hQ r π) = gluedCode L m (maskOf Q) (codeOuter r) (codeInner π) :=
  codeStr_glue leftEquiv (inner := fun p => .p p.1 p.2) (fun p => leftIdx_p p.1 p.2)
    (fun _ => rfl) Q hQ r π

/-- The code of the right string with inner set `Q`, inner part `π` and outer part `c`. -/
theorem codeR_rightStrOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (π : InnerStr m)
    (c : OuterStr L m) :
    codeR (rightStrOf Q hQ π c) = gluedCode L m (maskOf Q) (codeOuter c) (codeInner π) :=
  codeStr_glue rightEquiv (inner := fun p => .q p.1 p.2) (fun p => rightIdx_q p.1 p.2)
    (fun _ => rfl) Q hQ c π

section
variable {L m N : ℕ} (hmL : m ≤ L)

/-- `gluedCode` at the subset of the block product `(g, h)`, a row number and a column number is the
code of a left string. -/
private theorem gluedCode_table_left (gh : Fin (K0 L m) × Fin (K0 L m)) (r : Fin (N0 L m))
    (k : Fin (D m)) :
    gluedCode L m (unrank L m (gh.1 * K0 L m + gh.2)) r k
      = codeL (leftStrOf ((stdLayout hmL).table gh) ((stdLayout hmL).table_card gh)
          ((stdLayout hmL).rowIdx r) ((stdLayout hmL).innerIdx k)) := by
  rw [codeL_leftStrOf, codeOuter_rowIdx, codeInner_innerIdx, maskOf_table]

/-- `gluedCode` at the subset of the block product `(g, h)`, a column number of the block and a row
number of `Y` is the code of a right string. -/
private theorem gluedCode_table_right (gh : Fin (K0 L m) × Fin (K0 L m)) (c : Fin (N0 L m))
    (k : Fin (D m)) :
    gluedCode L m (unrank L m (gh.1 * K0 L m + gh.2)) c k
      = codeR (rightStrOf ((stdLayout hmL).table gh) ((stdLayout hmL).table_card gh)
          ((stdLayout hmL).innerIdx k) ((stdLayout hmL).colIdx c)) := by
  rw [codeR_rightStrOf, codeOuter_colIdx, codeInner_innerIdx, maskOf_table]

/-- The input array of a row band, entry by entry: at the code `gluedCode` of the subset of the
block product `(g, h)`, the row `r` of the block and the column `k`, it holds the entry of (the
padded) `X` in row `(β K₀ + g) N₀ + r` and column `k`. -/
theorem bandArrayL_at (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) (g h : Fin (K0 L m))
    (r : Fin (N0 L m)) (k : Fin (D m)) :
    (arrL (bandArrayL (stdLayout hmL) X β)).getD
        (gluedCode L m (unrank L m (g * K0 L m + h)) r k) 0
      = padRows X ((β * K0 L m + g) * N0 L m + r) k := by
  rw [gluedCode_table_left hmL (g, h) r k, getD_arrL, bandArrayL, arrayL_leftStrOf,
    bandFamilyL_table, rowBlock, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The input array of a column band, entry by entry: at the code `gluedCode` of the subset of the
block product `(g, h)`, the column `c` of the block and the row `k`, it holds the entry of (the
padded) `Y` in row `k` and column `(β K₀ + h) N₀ + c`. -/
theorem bandArrayR_at (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) (g h : Fin (K0 L m))
    (c : Fin (N0 L m)) (k : Fin (D m)) :
    (arrR (bandArrayR (stdLayout hmL) Y β)).getD
        (gluedCode L m (unrank L m (g * K0 L m + h)) c k) 0
      = padCols Y k ((β * K0 L m + h) * N0 L m + c) := by
  rw [gluedCode_table_right hmL (g, h) c k, getD_arrR, bandArrayR, arrayR_rightStrOf,
    bandFamilyR_table, colBlock, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end

/-- The input array of a row band is 0 at every left string whose inner set is not in the table. -/
private theorem bandArrayL_apply_eq_zero {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) (u : LeftStr L)
    (hu : ∀ gh r π, u ≠ leftStrOf (lay.table gh) (lay.table_card gh) r π) :
    bandArrayL lay X β u = 0 := by
  rw [bandArrayL, arrayL]
  split_ifs with hcard
  · -- Section 2.3.4: "let X_Q = Y_Q = 0 for the other subsets Q".
    rw [bandFamilyL_eq_zero lay X β fun gh hgh =>
      hu gh _ _ (leftStr_eq_leftStrOf (lay.table_card gh) hgh.symm hcard)]
    rfl
  · rfl

/-- The input array of a column band is 0 at every right string whose inner set is not in the
table. -/
private theorem bandArrayR_apply_eq_zero {L m N : ℕ} (lay : Layout L m)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) (v : RightStr L)
    (hv : ∀ gh π c, v ≠ rightStrOf (lay.table gh) (lay.table_card gh) π c) :
    bandArrayR lay Y β v = 0 := by
  rw [bandArrayR, arrayR]
  split_ifs with hcard
  · -- Section 2.3.4: "let X_Q = Y_Q = 0 for the other subsets Q".
    rw [bandFamilyR_eq_zero lay Y β fun gh hgh =>
      hv gh _ _ (rightStr_eq_rightStrOf (lay.table_card gh) hgh.symm hcard)]
    rfl
  · rfl

/-- The input array of a row band is 0 at every place that is not a code `gluedCode` as in
`bandArrayL_at`. -/
theorem bandArrayL_eq_zero {L m N : ℕ} (hmL : m ≤ L) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β pos : ℕ) (hpos : ∀ (g h : Fin (K0 L m)) (r : Fin (N0 L m)) (k : Fin (D m)),
      pos ≠ gluedCode L m (unrank L m (g * K0 L m + h)) r k) :
    (arrL (bandArrayL (stdLayout hmL) X β)).getD pos 0 = 0 := by
  refine getD_arrStr_eq_zero leftEquiv _ fun u hcode =>
    bandArrayL_apply_eq_zero _ X β u fun gh r π hu =>
      hpos gh.1 gh.2 ((stdLayout hmL).rowIdx.symm r) ((stdLayout hmL).innerIdx.symm π) ?_
  rw [gluedCode_table_left hmL gh, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hu]
  exact hcode.symm

/-- The input array of a column band is 0 at every place that is not a code `gluedCode` as in
`bandArrayR_at`. -/
theorem bandArrayR_eq_zero {L m N : ℕ} (hmL : m ≤ L) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β pos : ℕ) (hpos : ∀ (g h : Fin (K0 L m)) (c : Fin (N0 L m)) (k : Fin (D m)),
      pos ≠ gluedCode L m (unrank L m (g * K0 L m + h)) c k) :
    (arrR (bandArrayR (stdLayout hmL) Y β)).getD pos 0 = 0 := by
  refine getD_arrStr_eq_zero rightEquiv _ fun v hcode =>
    bandArrayR_apply_eq_zero _ Y β v fun gh π c hv =>
      hpos gh.1 gh.2 ((stdLayout hmL).colIdx.symm c) ((stdLayout hmL).innerIdx.symm π) ?_
  rw [gluedCode_table_right hmL gh, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hv]
  exact hcode.symm

end ThreeSumApsp.Spec
