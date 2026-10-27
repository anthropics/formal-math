/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.SideCodes
public import StepMachines.Math.CodeSeq
public import StepMachines.Math.Pull
public import Groundwork.Grid.Size

/-! The network of a term Z_ι of one level of the recursion, with all rows merged (tr = false) or
all columns merged (tr = true),
on words; n is the paper's λ, a part is a merged row or column, and ι is written by the digits of
the number y.
A label of the parts a < b: g blocks of n bits (the edges between nodes of the same number), then
one chunk for each of
their rectangles, in the order κ = tri i i', each of rectLen bits (coded by Code.sparse). -/

@[expose] public section

namespace Groundwork.Grid

open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)

/-- ι at the rectangle number κ of the pair of parts number p. -/
def rectDig (g : ℕ) (tr : Bool) (n y p κ : ℕ) : ℕ := digit n y (rectIx g tr p κ)

/-- The length of the chunk of that rectangle. -/
def rectLen (g : ℕ) (tr : Bool) (n y p κ : ℕ) : ℕ := capW n (sideCnt tr n (rectDig g tr n y p κ))

/-- A label of a rectangle has at most n states other than the frequent one. -/
theorem sideCnt_rectDig_le (g : ℕ) (tr : Bool) (n y p κ : ℕ) : sideCnt tr n (rectDig g tr n y p κ) ≤ n := by
  have h : rectDig g tr n y p κ ≤ n := digit_le _ _ _
  unfold sideCnt
  split_ifs <;> omega

/-- A chunk has at most 3n + 1 bits. -/
theorem rectLen_le (g : ℕ) (tr : Bool) (n y p κ : ℕ) : rectLen g tr n y p κ ≤ 3 * n + 1 := by
  have h1 := sideCnt_rectDig_le g tr n y p κ
  have h2 := Prog.tb_le (sideCnt tr n (rectDig g tr n y p κ))
  unfold rectLen capW
  omega

/-- The cuts of the rectangles of the grid (of the transposed grid if tr). -/
def sideCuts (g : ℕ) (tr : Bool) (n y : ℕ) : Rect (Fin g) (Fin g) → Cut (Bits n) (Fin n → Bell) :=
  fun ω => sideCut tr n (rectDig g tr n y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))

/-- The default label of a rectangle. -/
def bell0 (n : ℕ) : Fin n → Bell := fun _ => (false, false)

/-- The network of the term, with states and labels as in `rowNet`, before they are written as
words. -/
def sideNet (g : ℕ) (tr : Bool) (n : ℕ) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) :
    Network (Fin g) (RowSt (Fin g) (Fin g) (Bits n)) (RowLab (Fin g) (Bits n) (Fin n → Bell)) :=
  rowNet R (sideCuts g tr n y) (bell0 n) n

/-- The code of the labels of the rectangle number κ of the pair of parts number p. -/
def rectC (g : ℕ) (tr : Bool) (n y p κ : ℕ) :
    Code (sparseLab (sideS0 tr) n (sideCnt tr n (rectDig g tr n y p κ))) (rectLen g tr n y p κ) :=
  Code.sparse (sideS0 tr) n (sideCnt tr n (rectDig g tr n y p κ))

/-- The code of the labels of the rectangles of the parts a, b: their chunks one after the other. -/
def rectsC (g : ℕ) (tr : Bool) (n y : ℕ) (a b : Fin g) :
    Code (tuples (fun k : Fin g × Fin g => k.1 < k.2) (fun k => (sideCuts g tr n y ((a, b), k)).lab) (bell0 n))
      (∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ) :=
  Code.seq _ (fun k : Fin g × Fin g => tri k.1 k.2) (c2 g) (tri_bijOn g) (rectLen g tr n y (tri a b))
    (fun k => (rectC g tr n y (tri a b) (tri k.1 k.2)).D) (fun k => (rectC g tr n y (tri a b) (tri k.1 k.2)).dec)
    (fun k _ w hw => (rectC g tr n y (tri a b) (tri k.1 k.2)).len w hw)
    (fun k _ => (rectC g tr n y (tri a b) (tri k.1 k.2)).bij) (bell0 n)

/-- A sum over the pairs i < i' is the sum over their numbers. -/
theorem sum_pairs_tri (g : ℕ) (f : ℕ → ℕ) :
    ∑ k : Fin g × Fin g with k.1 < k.2, f (tri k.1 k.2) = ∑ κ ∈ range (c2 g), f κ := by
  have hb := tri_bijOn g
  refine Finset.sum_nbij (fun k : Fin g × Fin g => tri k.1 k.2) (fun k hk => ?_) (fun k hk k' hk' h => ?_)
    (fun κ hκ => ?_) (fun k _ => rfl)
  · exact hb.mapsTo (by simpa using hk)
  · exact hb.injOn (by simpa using hk) (by simpa using hk') h
  · obtain ⟨k, hk, rfl⟩ := hb.surjOn hκ
    exact ⟨k, by simpa using hk, rfl⟩

/-- The capacity (number of label bits) of the parts a < b. -/
theorem sideNet_c_eq {g n : ℕ} (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ = (sideNet g tr n R y).c a b := by
  simp only [sideNet, rowNet, Fintype.card_fin, min_eq_left hab.le, max_eq_right hab.le]
  rw [← sum_pairs_tri]
  rfl

/-- The label set of the parts a < b: the edges between nodes of the same number, and a label for
each rectangle. -/
theorem sideNet_Θ {g n : ℕ} (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (univ : Finset (Fin g → Bits n)) ×ˢ
      tuples (fun k : Fin g × Fin g => k.1 < k.2) (fun k => (sideCuts g tr n y ((a, b), k)).lab) (bell0 n)
      = (sideNet g tr n R y).Θ a b := by
  simp [sideNet, rowNet, rowΘ, hab]

/-- Label sets are kept at a < b only. -/
theorem sideNet_Θ_empty {g n : ℕ} (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : ¬ a < b) :
    ∅ = (sideNet g tr n R y).Θ a b := by
  simp [sideNet, rowNet, hab]

/-- The code of the labels of two parts. -/
def sideCl (g : ℕ) (tr : Bool) (n : ℕ) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) (a b : Fin g) :
    Code ((sideNet g tr n R y).Θ a b) ((sideNet g tr n R y).c a b) :=
  if hab : a < b then ((vC g n).prod (rectsC g tr n y a b)).cast (sideNet_Θ tr R y hab) (sideNet_c_eq tr R y hab)
  else (Code.empty ((fun _ _ => false), fun _ => bell0 n) _).cast (sideNet_Θ_empty tr R y hab) rfl

/-- The network on words. -/
noncomputable def sideN (g : ℕ) (tr : Bool) : SideNet g := fun n Rm y =>
  (sideNet g tr n (sideR g tr n Rm) y).pull (fun _ => g ^ 3 * n) (fun _ => stC g tr n) (sideCl g tr n (sideR g tr n Rm) y)

/-- The term Z_ι, ι written by y. -/
noncomputable def sideZ (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) : ℤ :=
  ZG (sideR g false n Rm) fun ω => A n (patOf g n y ω)

/-- On words, the value Z is the sum of the terms Z_ι over all ι, each ι written by a number y. -/
theorem ZW_eq_sum (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    Inst.ZW n [] Rm = ∑ y ∈ range ((n + 1) ^ nRect g), sideZ g n Rm y := by
  rw [ZW_eq_Z n Rm (fun _ => false), Z_eq_ZG_X _ _ (gridE g false), ZG_cross_eq_sum, ← sum_patOf]
  rfl

/-- In each term all rows or all columns are merged (Step 2 of Section 2.3): either network on words
has the value Z_ι. -/
theorem value_sideN (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g tr n Rm y).value = sideZ g n Rm y := by
  refine (Network.value_pull _ _ _ _ (fun _ => stC_full g tr n)).trans ?_
  have hc : ZG (sideR g false n Rm) (fun ω => A n (digit n y (ixOf g ω))) = sideZ g n Rm y :=
    ZG_congr _ fun ω hω => by simp [patOf, hω]
  cases tr with
  | false =>
    rw [← hc]
    exact value_rowNet (G := fun ω => A n (digit n y (ixOf g ω))) (fun ω => sideCut_factors_row (digit_le _ _ _)) _ _ _
  | true =>
    rw [← hc, ← ZG_tr, sideR_true]
    exact value_rowNet (G := trG fun ω => A n (digit n y (ixOf g ω))) (fun ω => sideCut_factors_col _ _) _ _ _

/-- The network before words has size 2g³λ (at most 2^(2g³λ) states and 2g³λ label bits at a node),
and values of at most g·B + g²·λ bits. -/
theorem sideNet_sized {g n B : ℕ} (tr : Bool) (hn : 1 ≤ n) {R : Inst (Fin g × Fin g) (Bits n)}
    (hR : ∀ w h, |R w h| ≤ 2 ^ B) (y : ℕ) : (sideNet g tr n R y).Sized (2 * g ^ 3 * n) (g * B + g ^ 2 * n) := by
  have hα : Fintype.card (Bits n) = 2 ^ n := by simp
  rw [Nat.mul_assoc]
  cases tr with
  | false =>
    exact rowNet_sized' (m := 2) (by norm_num) (Fintype.card_fin g) (Fintype.card_fin g) hα R hR
      (G := fun ω => A n (rectDig g false n y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))) _ _
      (fun ω => sideCut_factors_row (digit_le _ _ _)) (fun ω => card_sideCut_lab _ _ _)
      (fun ω => sideCut_cap_le _ hn (digit_le _ _ _)) (fun ω => abs_sideCut_top _ _ _) (fun ω => abs_sideCut_bot _ _ _)
      (fun ω => abs_A_le _ _)
  | true =>
    exact rowNet_sized' (m := 2) (by norm_num) (Fintype.card_fin g) (Fintype.card_fin g) hα R hR
      (G := fun ω x u y' v => A n (rectDig g true n y (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2)) x y' u v) _ _
      (fun ω => sideCut_factors_col _ _) (fun ω => card_sideCut_lab _ _ _)
      (fun ω => sideCut_cap_le _ hn (digit_le _ _ _)) (fun ω => abs_sideCut_top _ _ _) (fun ω => abs_sideCut_bot _ _ _)
      (fun ω x u y' v => abs_A_le _ _ x y' u v)

/-- The network on words has size 2g³λ, and values of at most g·B + g²·λ bits. -/
theorem sideN_sized {g n B : ℕ} (tr : Bool) (hn : 1 ≤ n) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : BoundedInst n B Rm)
    (y : ℕ) : (sideN g tr n Rm y).Sized (2 * g ^ 3 * n) (g * B + g ^ 2 * n) :=
  Network.sized_pull_of_le _ _ _ _ (sideNet_sized tr hn (abs_sideR_le tr hR) y) fun _ => by
    rw [Nat.mul_assoc]; omega

/-- The number of bits on the wires of the row network (every wire counted twice): the straight
edges (inside a row or a column),
and the cost `priceRow` of the rectangles. -/
theorem U_sideN_row (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g false n Rm y).U = g ^ 2 * (g - 1) * n + priceRow g n y := by
  change (sideNet g false n (sideR g false n Rm) y).U = _
  unfold sideNet priceRow
  rw [U_rowNet (Fintype.card_fin g) (Fintype.card_fin g), ← sum_Ω_ixOf]
  rfl

/-- The number of bits on the wires of the column network (every wire counted twice). -/
theorem U_sideN_col (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g true n Rm y).U = g ^ 2 * (g - 1) * n + priceCol g n y := by
  change (sideNet g true n (sideR g true n Rm) y).U = _
  unfold sideNet priceCol
  rw [U_rowNet (Fintype.card_fin g) (Fintype.card_fin g), ← sum_Ω_ixOf]
  congr 2
  exact Finset.sum_equiv (Equiv.prodComm _ _) (fun ω => by simp [Ω, and_comm]) fun ω _ => rfl

/-- The length of the labels of the parts a, b. -/
def sideCap (g : ℕ) (tr : Bool) (n y a b : ℕ) : ℕ :=
  g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri (min a b) (max a b)) κ

/-- The capacity of two parts is the length of their labels. -/
theorem sideN_c (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {a b : Fin g} (hab : a ≠ b) :
    (sideN g tr n Rm y).c a b = sideCap g tr n y a b := by
  have hlt : min a b < max a b := min_lt_max.2 hab
  have h := sideNet_c_eq tr (sideR g tr n Rm) y hlt
  change (sideNet g tr n (sideR g tr n Rm) y).c a b = _
  have e : (sideNet g tr n (sideR g tr n Rm) y).c a b = (sideNet g tr n (sideR g tr n Rm) y).c (min a b) (max a b) := by
    simp only [sideNet, rowNet, min_eq_left hlt.le, max_eq_right hlt.le]
  rw [e, ← h]
  rfl

/-- The labels of two parts are all words of that length. -/
theorem sideN_lab (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {a b : Fin g} (hab : a ≠ b) :
    (sideN g tr n Rm y).lab a b = words (sideCap g tr n y a b) := by
  have hlt : min a b < max a b := min_lt_max.2 hab
  rw [← sideN_c g tr n Rm y hab]
  change words ((sideNet g tr n (sideR g tr n Rm) y).c (min a b) (max a b)) =
    words ((sideNet g tr n (sideR g tr n Rm) y).c a b)
  simp only [sideNet, rowNet, min_eq_left hlt.le, max_eq_right hlt.le]

/-- Labels have at most g·λ + 2g²·λ bits. -/
theorem sideCap_le {g n : ℕ} (tr : Bool) (hn : 1 ≤ n) (y a b : ℕ) : sideCap g tr n y a b ≤ g * n + 2 * g ^ 2 * n := by
  unfold sideCap
  have h1 : ∑ κ ∈ range (c2 g), rectLen g tr n y (tri (min a b) (max a b)) κ ≤ ∑ _κ ∈ range (c2 g), 2 * 2 * n :=
    Finset.sum_le_sum fun κ _ => sideCut_cap_le tr hn (digit_le _ _ _)
  rw [Finset.sum_const, card_range, smul_eq_mul] at h1
  have h2 := Nat.mul_le_mul_right (2 * n) (two_mul_c2_le g)
  have e1 : c2 g * (2 * 2 * n) = 2 * c2 g * (2 * n) := by ring
  have e2 : g ^ 2 * (2 * n) = 2 * g ^ 2 * n := by ring
  omega

end Groundwork.Grid
