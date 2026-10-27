/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.Sparse
public import Groundwork.Grid.Expand

/-! One rectangle of the grid; n is the length λ of the strings on an edge. The factorisation of the
piece A_i (`A` n i here), which is built from single bits, across rows (tr = false) or across
columns
(tr = true). This A_i is not the A_i of Definition 5, which is built from blocks of three bits. Its
labels are strings of n two-bit states with few positions off a frequent state, named by the codes
of StepMachines/Math/Sparse.lean with their number of bits; and its two
parts as functions of words, in the form in which the machine evaluates them: the top part is a
product over the n
positions, the bottom part a sum over all 2^n sets of positions, of which those with i elements
count. -/

@[expose] public section

namespace Groundwork.Grid

open Finset
open Groundwork.Prog (tb capW)

/-! ### λ-bit indices as words -/

/-- The index written by a word. -/
def bitsOf (n : ℕ) (w : List Bool) : Bits n := fun k => w.getD k false

/-- The words of n bits write the n-bit indices, one each. -/
theorem bitsOf_bijOn (n : ℕ) : Set.BijOn (bitsOf n) (words n) (univ : Finset (Bits n)) := by
  refine ⟨fun _ _ => mem_coe.2 (mem_univ _), fun w hw w' hw' h => ?_, fun x _ => ?_⟩
  · have l := mem_words.1 (mem_coe.1 hw)
    have l' := mem_words.1 (mem_coe.1 hw')
    refine List.ext_getElem (l.trans l'.symm) fun j hj hj' => ?_
    have h1 := congrFun h ⟨j, l ▸ hj⟩
    simpa only [bitsOf, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] using h1
  · refine ⟨List.ofFn x, mem_coe.2 (mem_words.2 (List.length_ofFn)), funext fun k => ?_⟩
    rw [bitsOf, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]

/-- The words of n bits name the n-bit indices. -/
def bitsC (n : ℕ) : Code (univ : Finset (Bits n)) n := (Code.word n).map (bitsOf n) univ (bitsOf_bijOn n)

theorem bitsC_full (n : ℕ) : (bitsC n).Full := rfl

/-- Two indices are equal iff their words are. -/
theorem bitsOf_inj {n : ℕ} {w w' : List Bool} (h : w.length = n) (h' : w'.length = n) :
    bitsOf n w = bitsOf n w' ↔ w = w' :=
  (bitsC n).dec_inj (mem_words.2 h) (mem_words.2 h')

/-- A word names the index 0…0 iff all its bits are false. -/
theorem bitsOf_eq_zero {n : ℕ} {w : List Bool} (h : w.length = n) :
    bitsOf n w = (fun _ => false) ↔ w.all (!·) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h0 b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
    have h1 := congrFun h0 ⟨j, h ▸ hj⟩
    simp only [bitsOf, List.getD_eq_getElem _ _ hj] at h1
    rw [h1]; rfl
  · intro h0
    funext k
    have hk : (k : ℕ) < w.length := h ▸ k.2
    have h1 := h0 _ (List.getElem_mem hk)
    rw [bitsOf, List.getD_eq_getElem _ _ hk]
    simpa using h1

/-! ### The cut of one rectangle -/

/-- The tables of one bit: rows or columns. -/
def sideBit (tr : Bool) : BitCut := if tr = true then colBit else rowBit

/-- The frequent state: the singlet for rows, Φ⁺ for columns. -/
def sideS0 (tr : Bool) : Bell := if tr = true then (false, false) else (true, true)

/-- The number of other states allowed in a label of A_i: n − i for rows, i for columns. -/
def sideCnt (tr : Bool) (n i : ℕ) : ℕ := if tr = true then i else n - i

/-- A_i cut across rows or columns, charged with the length of the names of its labels. -/
def sideCut (tr : Bool) (n i : ℕ) : Cut (Bits n) (Fin n → Bell) where
  lab := sparseLab (sideS0 tr) n (sideCnt tr n i)
  top x y β := (sideBit tr).Top β x y
  bot u v β := (sideBit tr).Bot i β u v
  cap := capW n (sideCnt tr n i)

/-- Across rows the cut is a factorisation of A_i. -/
theorem sideCut_factors_row {n i : ℕ} (h : i ≤ n) : (sideCut false n i).Factors (A n i) := by
  intro x y u v
  rw [A_rows, rowLabels_eq h]
  rfl

/-- Across columns the cut is a factorisation of A_i, its arguments in the order x, u | y, v. -/
theorem sideCut_factors_col (n i : ℕ) : (sideCut true n i).Factors fun x u y v => A n i x y u v := by
  intro x u y v
  change A n i x y u v = _
  rw [A_cols, colLabels_eq]
  rfl

/-- There are at most 2^cap labels. -/
theorem card_sideCut_lab (tr : Bool) (n i : ℕ) : #(sideCut tr n i).lab ≤ 2 ^ (sideCut tr n i).cap :=
  (Code.sparse (sideS0 tr) n (sideCnt tr n i)).card_le

/-- A name has at most 4n bits. -/
theorem sideCut_cap_le (tr : Bool) {n i : ℕ} (hn : 1 ≤ n) (h : i ≤ n) : (sideCut tr n i).cap ≤ 2 * 2 * n := by
  have hc : sideCnt tr n i ≤ n := by
    cases tr
    · exact Nat.sub_le n i
    · exact h
  have h4 := capW_le hn hc
  change capW n (sideCnt tr n i) ≤ 2 * 2 * n
  omega

/-- The top part is at most 2^n in absolute value. -/
theorem abs_sideCut_top (tr : Bool) (n i : ℕ) (x y : Bits n) (β : Fin n → Bell) : |(sideCut tr n i).top x y β| ≤ 2 ^ n := by
  have h1 : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  cases tr
  · exact (abs_rowTop_le β x y).trans h1
  · exact (abs_colTop_le β x y).trans h1

/-- The bottom part is at most 2^n in absolute value. -/
theorem abs_sideCut_bot (tr : Bool) (n i : ℕ) (u v : Bits n) (β : Fin n → Bell) : |(sideCut tr n i).bot u v β| ≤ 2 ^ n := by
  cases tr
  · exact abs_rowBot_le i β u v
  · exact abs_colBot_le i β u v

/-! ### The two parts on words. The length n is the length of the word x. -/

/-- One factor of the top part: position k. x, y are the words of the two ends, w the name of the
label. -/
def topTerm (tr : Bool) (x y w : List Bool) (k : ℕ) : ℤ :=
  (sideBit tr).top (symAt (sideS0 tr) x.length w k) (x.getD k false) (y.getD k false)

/-- One factor of the bottom part: position k in the term of the set of positions written by the
number s. -/
def botTerm (tr : Bool) (x y w : List Bool) (s k : ℕ) : ℤ :=
  if (toWord x.length s).getD k false = true then
    (sideBit tr).bot1 (symAt (sideS0 tr) x.length w k) (x.getD k false) (y.getD k false)
  else (sideBit tr).bot0 (symAt (sideS0 tr) x.length w k) (x.getD k false) (y.getD k false)

/-- The top part. -/
def topW (tr : Bool) (x y w : List Bool) : ℤ := ∏ k ∈ range x.length, topTerm tr x y w k

/-- The bottom part. -/
def botW (tr : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  ∑ s ∈ range (2 ^ x.length),
    if (toWord x.length s).count true = i then ∏ k ∈ range x.length, botTerm tr x y w s k else 0

/-- The part of the cut of A_i on one side (top or bottom), 0 at the words that name no label. -/
def cutW (tr top : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  if validW x.length (sideCnt tr x.length i) w = true then
    if top = true then topW tr x y w else botW tr i x y w
  else 0

/-- The positions 0, …, n − 1 as numbers. -/
private theorem val_bijOn (n : ℕ) :
    Set.BijOn (fun k : Fin n => (k : ℕ)) (univ : Finset (Fin n)) (range n : Finset ℕ) :=
  ⟨fun k _ => mem_coe.2 (mem_range.2 k.2), fun _ _ _ _ h => Fin.ext h,
    fun j hj => ⟨⟨j, mem_range.1 (mem_coe.1 hj)⟩, mem_coe.2 (mem_univ _), rfl⟩⟩

/-- A sum over the sets of i positions is a sum over all numbers s below 2^n, read as sets of
positions, of which those with
i elements count. -/
private theorem sum_powersetCard_eq_sum_range {n : ℕ} (i : ℕ) (f1 f0 : Fin n → ℤ) :
    ∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k
      = ∑ s ∈ range (2 ^ n), if (toWord n s).count true = i then
          ∏ k : Fin n, (if (toWord n s).getD k false = true then f1 k else f0 k) else 0 := by
  rw [sum_toWord n fun τ => if τ.count true = i then
    ∏ k : Fin n, (if τ.getD k false = true then f1 k else f0 k) else 0]
  rw [powersetCard_eq_filter, sum_filter, ← (Code.subsets univ n _ (val_bijOn n)).sum_dec]
  refine sum_congr rfl fun τ hτ => ?_
  rw [Code.card_dec_subsets univ n _ (val_bijOn n) (mem_words.1 hτ)]
  split_ifs
  · rw [prod_ite, ← compl_filter]
    rfl
  · rfl

/-- The top part on words is the top part of the string that w names. -/
theorem topW_eq (tr : Bool) {n : ℕ} (c : ℕ) {x y : List Bool} (w : List Bool) (hx : x.length = n) :
    topW tr x y w = (sideBit tr).Top ((Code.sparse (sideS0 tr) n c).dec w) (bitsOf n x) (bitsOf n y) := by
  subst hx
  rw [topW, prod_range]
  rfl

/-- The bottom part on words is the bottom part of the string that w names. -/
theorem botW_eq (tr : Bool) {n : ℕ} (i c : ℕ) {x y : List Bool} (w : List Bool) (hx : x.length = n) :
    botW tr i x y w = (sideBit tr).Bot i ((Code.sparse (sideS0 tr) n c).dec w) (bitsOf n x) (bitsOf n y) := by
  subst hx
  rw [botW, BitCut.Bot, sum_powersetCard_eq_sum_range]
  refine sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [prod_range]
    exact prod_congr rfl fun k _ => rfl
  · rfl

/-- What the machine evaluates is the part of the cut, read through the codes. -/
theorem cutW_eq (tr top : Bool) {n i : ℕ} {x y w : List Bool} (hx : x.length = n)
    (hw : w.length = capW n (sideCnt tr n i)) :
    cutW tr top i x y w =
      if w ∈ (Code.sparse (sideS0 tr) n (sideCnt tr n i)).D then
        if top = true then
          (sideCut tr n i).top (bitsOf n x) (bitsOf n y) ((Code.sparse (sideS0 tr) n (sideCnt tr n i)).dec w)
        else (sideCut tr n i).bot (bitsOf n x) (bitsOf n y) ((Code.sparse (sideS0 tr) n (sideCnt tr n i)).dec w)
      else 0 := by
  subst hx
  have hD : w ∈ (Code.sparse (sideS0 tr) x.length (sideCnt tr x.length i)).D ↔
      validW x.length (sideCnt tr x.length i) w = true := by
    change w ∈ (words _).filter _ ↔ _
    rw [mem_filter, mem_words]
    exact and_iff_right hw
  rw [cutW]
  by_cases hv : validW x.length (sideCnt tr x.length i) w = true
  · rw [if_pos hv, if_pos (hD.2 hv), topW_eq tr (sideCnt tr x.length i) w rfl,
      botW_eq tr i (sideCnt tr x.length i) w rfl]
    rfl
  · rw [if_neg hv, if_neg fun h => hv (hD.1 h)]

end Groundwork.Grid
