/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.GridDefs
public import Coding.OccLists
import all StepMachines.Math.CodeMore
import PaddedDescent.F.Table
import Eight.SecLevel_GridWords
import Mathlib.Tactic.Ring

/-! # The strings at the grid points' own positions are padding

Proof of Proposition 3: «A setting of row a is the tuple (z_{(a,j)})_{j ∈ [g]} of the settings of
its g grid points; S_a is the set of these tuples, encoded by concatenation in g(g² − 1)λ ≤ P bits,
where P = g³λ.» Lean's settings have g³λ bits: for each grid point of the row a string of λ bits for
EVERY grid point, also for itself.
`stGridPadding`: Lean's network is the same network read at settings of g(g² − 1)λ bits, with
padding (`Coding.padRow`). Three of the seven fields have content:
* a padded setting has g³λ bits (`length_padRow`), and its string for the grid point at position u,
  held at the x-th grid point of the row, is `pieceRow` (`heG_padRow`);
* padding is one to one (`padRow_inj`): the strings at the other positions are those of z;
* a string of g³λ bits that has 0^λ at each grid point's own position is a padded setting
  (`exists_padRow`), and at all other strings W_a is 0 (`W_eq_zero`): this is the condition
  `if h w = d` of `Groundwork.Grid.onGrid`, read on words by `ClauseBound.Alg.GridNet.stC_dec`.
  `import all StepMachines.Math.CodeMore` gives access to `Groundwork.Code.block_ext`, which is not
  public. -/

public section

namespace Coding

open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level

/-! ### Concatenations of strings of one length -/

/-- A concatenation of n strings of c bits has n·c bits. -/
theorem length_flatMap_range (n c : ℕ) (f : ℕ → List Bool) (hf : ∀ j < n, (f j).length = c) : ((List.range n).flatMap f).length = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih fun j hj => hf j (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hf n (by omega), Nat.succ_mul]

/-- The j-th block of a concatenation of n strings of c bits is the j-th string. -/
theorem block_flatMap_range (n c : ℕ) (f : ℕ → List Bool) (hf : ∀ j < n, (f j).length = c) {j : ℕ} (hj : j < n) : block c j ((List.range n).flatMap f) = f j := by
  rw [List.flatMap_def, PaddedDescent.F.Table.block_flatten _ j (by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    exact hf i (List.mem_range.1 hi)) (by simpa using hj), List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-! ### The padded setting, string by string -/

variable {g : ℕ} {tr : Bool} {lam : ℕ}

/-- On the g × g grid, a row or a column has g grid points. -/
theorem nMemb_self (g : ℕ) (tr : Bool) : nMemb g g tr = g := by cases tr <;> rfl

/-- The string that the padded setting holds, at the x-th grid point of the row, for the grid point
at position u. -/
@[expose] def pieceRow (g : ℕ) (tr : Bool) (lam a : ℕ) (z : List Bool) (x u : ℕ) : List Bool :=
  if u = nodeG g tr a x then List.replicate lam false else block lam (if u < nodeG g tr a x then u else u - 1) (block ((g * g - 1) * lam) x z)

/-- `padRow` written with `pieceRow`. -/
theorem padRow_eq (g : ℕ) (tr : Bool) (lam a : ℕ) (z : List Bool) : padRow g tr lam a z = (List.range g).flatMap fun x => (List.range (g * g)).flatMap fun u => pieceRow g tr lam a z x u := rfl

/-- The position of the x-th grid point of a row or column is one of the g² positions. -/
theorem nodeG_lt' (a : Fin (nParts g g tr)) {x : ℕ} (hx : x < g) : nodeG g tr a.val x < g * g := nodeG_lt tr a.2 (by rw [nMemb_self]; exact hx)

/-- The part of z for the x-th grid point of the row has (g² − 1)λ bits. -/
theorem length_block_row {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x : ℕ} (hx : x < g) : (block ((g * g - 1) * lam) x z).length = (g * g - 1) * lam :=
  length_block (by rw [hz]; exact Nat.mul_le_mul_right _ hx)

/-- Each string of the padded setting has λ bits. -/
theorem length_pieceRow (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x u : ℕ} (hx : x < g) (hu : u < g * g) : (pieceRow g tr lam a.val z x u).length = lam := by
  have hnd := nodeG_lt' a hx
  unfold pieceRow
  by_cases h : u = nodeG g tr a.val x
  · rw [if_pos h, List.length_replicate]
  · rw [if_neg h]
    refine length_block ?_
    rw [length_block_row hz hx]
    refine Nat.mul_le_mul_right _ ?_
    split_ifs <;> omega

/-- The part of the padded setting for one grid point has g²λ bits. -/
theorem length_rowPart (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x : ℕ} (hx : x < g) :
    ((List.range (g * g)).flatMap fun u => pieceRow g tr lam a.val z x u).length = g * g * lam :=
  length_flatMap_range _ _ _ fun _ hu => length_pieceRow a hz hx hu

/-- A padded setting has g³λ bits. -/
theorem length_padRow (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) : (padRow g tr lam a.val z).length = g * (g * g * lam) := by
  rw [padRow_eq]
  exact length_flatMap_range _ _ _ fun _ hx => length_rowPart a hz hx

/-- The strings of the padded setting. -/
theorem heG_padRow (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x u : ℕ} (hx : x < g) (hu : u < g * g) :
    heG g g lam (padRow g tr lam a.val z) x u = pieceRow g tr lam a.val z x u := by
  rw [heG, padRow_eq, block_flatMap_range g (g * g * lam) _ (fun _ hx => length_rowPart a hz hx) hx, block_flatMap_range (g * g) lam _ (fun _ hu => length_pieceRow a hz hx hu) hu]

/-- At the positions other than its own, a grid point holds the strings of z. -/
theorem pieceRow_skip (a : ℕ) (z : List Bool) (x u' : ℕ) : pieceRow g tr lam a z x (if u' < nodeG g tr a x then u' else u' + 1) = block lam u' (block ((g * g - 1) * lam) x z) := by
  unfold pieceRow
  by_cases hlt : u' < nodeG g tr a x
  · rw [if_pos hlt, if_neg (by omega), if_pos hlt]
  · rw [if_neg hlt, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]

/-- Padding is one to one. -/
theorem padRow_inj (a : Fin (nParts g g tr)) {z z' : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) (hz' : z'.length = g * ((g * g - 1) * lam))
    (h : padRow g tr lam a.val z = padRow g tr lam a.val z') : z = z' := by
  refine Code.block_ext ((g * g - 1) * lam) g z z' hz hz' fun x hx => ?_
  refine Code.block_ext lam (g * g - 1) _ _ (length_block_row hz hx) (length_block_row hz' hx) fun u' hu' => ?_
  have hnd := nodeG_lt' a hx
  have hu : (if u' < nodeG g tr a.val x then u' else u' + 1) < g * g := by split_ifs <;> omega
  rw [← pieceRow_skip (tr := tr) a.val z x u', ← pieceRow_skip (tr := tr) a.val z' x u', ← heG_padRow a hz hx hu, ← heG_padRow a hz' hx hu, h]

/-- A string of g³λ bits with 0^λ at each grid point's own position is a padded setting. -/
theorem exists_padRow (a : Fin (nParts g g tr)) {y : List Bool} (hy : y.length = g * (g * g * lam)) (h0 : ∀ x < g, heG g g lam y x (nodeG g tr a.val x) = List.replicate lam false) :
    ∃ z : List Bool, z.length = g * ((g * g - 1) * lam) ∧ padRow g tr lam a.val z = y := by
  have hrow : ∀ x < g, (block (g * g * lam) x y).length = g * g * lam := fun x hx => length_block (by rw [hy]; exact Nat.mul_le_mul_right _ hx)
  have hlen : ∀ x < g, ∀ u < g * g, (heG g g lam y x u).length = lam := fun x hx u hu => length_block (by rw [hrow x hx]; exact Nat.mul_le_mul_right _ hu)
  have hskip : ∀ x < g, ∀ u' < g * g - 1, (heG g g lam y x (if u' < nodeG g tr a.val x then u' else u' + 1)).length = lam := fun x hx u' hu' => hlen x hx _ (by split_ifs <;> omega)
  have hpart : ∀ x < g, ((List.range (g * g - 1)).flatMap fun u' => heG g g lam y x (if u' < nodeG g tr a.val x then u' else u' + 1)).length = (g * g - 1) * lam :=
    fun x hx => length_flatMap_range _ _ _ (hskip x hx)
  have hz : ((List.range g).flatMap fun x => (List.range (g * g - 1)).flatMap fun u' => heG g g lam y x (if u' < nodeG g tr a.val x then u' else u' + 1)).length = g * ((g * g - 1) * lam) :=
    length_flatMap_range _ _ _ hpart
  refine ⟨_, hz, Code.block_ext (g * g * lam) g _ _ (length_padRow a hz) hy fun x hx => ?_⟩
  have hl : (block (g * g * lam) x (padRow g tr lam a.val _)).length = g * g * lam := length_block (by rw [length_padRow a hz]; exact Nat.mul_le_mul_right _ hx)
  refine Code.block_ext lam (g * g) _ _ hl (hrow x hx) fun u hu => ?_
  have hnd := nodeG_lt' a hx
  change heG g g lam (padRow g tr lam a.val _) x u = heG g g lam y x u
  rw [heG_padRow a hz hx hu]
  unfold pieceRow
  by_cases hu0 : u = nodeG g tr a.val x
  · rw [if_pos hu0, hu0, h0 x hx]
  · have hu' : (if u < nodeG g tr a.val x then u else u - 1) < g * g - 1 := by split_ifs <;> omega
    have e : (if (if u < nodeG g tr a.val x then u else u - 1) < nodeG g tr a.val x then (if u < nodeG g tr a.val x then u else u - 1) else (if u < nodeG g tr a.val x then u else u - 1) + 1) = u := by
      split_ifs <;> omega
    rw [if_neg hu0, block_flatMap_range g _ _ hpart hx, block_flatMap_range (g * g - 1) lam _ (hskip x hx) hu', e]

/-! ### W is 0 off the padded settings -/

/-- A string of λ bits that writes the index 0 is 0^λ. -/
theorem eq_replicate_of_bitsOf {w : List Bool} (hw : w.length = lam) (h : Grid.bitsOf lam w = fun _ => false) : w = List.replicate lam false := by
  refine ext_getD (by rw [hw, List.length_replicate]) fun i hi => ?_
  have h1 : w.getD i false = false := congrFun h ⟨i, hw ▸ hi⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

/-- W_a is 0 unless the string at each grid point's own position writes the index 0. -/
theorem W_eq_zero (yι : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (a : Fin (nParts g g tr)) (y : List Bool) (i : Fin (nMemb g g tr))
    (h : Grid.bitsOf lam (heG g g lam y i.val (nodeG g tr a.val i.val)) ≠ fun _ => false) : (levelNetP g tr lam yι Rm).W a y = 0 := by
  change rowW (gridR g g tr lam Rm) a ((stC g g tr lam).dec y) = 0
  have h1 : gridR g g tr lam Rm (a, i) ((stC g g tr lam).dec y i) = 0 := by
    simp only [gridR, onGrid]
    rw [if_neg]
    rw [GridNet.stC_dec]
    exact h
  unfold rowW
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h1, zero_mul]

/-! ### The statements -/

/-- **The strings at the grid points' own positions are padding**: «S_a is the set of these tuples,
encoded by concatenation in g(g² − 1)λ ≤ P bits, where P = g³λ» (proof of Proposition 3), where
Lean's settings have g³λ bits. -/
theorem stGridPadding : StGridPadding := by
  intro g tr lam yι Rm
  have e1 : g * (g ^ 2 - 1) * lam = g * ((g * g - 1) * lam) := by rw [pow_two, Nat.mul_assoc]
  have e2 : g ^ 3 * lam = g * (g * g * lam) := by ring
  refine ⟨fun a z hz => ?_, fun a z hz z' hz' h => ?_, fun a y hy hno => ?_, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  · change padRow g tr lam a.val z ∈ (netOfι g tr lam yι Rm).S a
    rw [Eight.Level.netOfι_S, mem_words, e2]
    exact length_padRow a ((mem_words.1 hz).trans e1)
  · exact padRow_inj a ((mem_words.1 hz).trans e1) ((mem_words.1 hz').trans e1) h
  · have hy' : y ∈ (netOfι g tr lam yι Rm).S a := hy
    rw [Eight.Level.netOfι_S, mem_words, e2] at hy'
    by_contra hW
    have hrow : ∀ x < g, (block (g * g * lam) x y).length = g * g * lam := fun x hx => length_block (by rw [hy']; exact Nat.mul_le_mul_right _ hx)
    obtain ⟨z, hz, hzy⟩ := exists_padRow a hy' fun x hx => by
      refine eq_replicate_of_bitsOf (length_block (by rw [hrow x hx]; exact Nat.mul_le_mul_right _ (nodeG_lt' a hx))) ?_
      by_contra hne
      exact hW (W_eq_zero yι Rm a y ⟨x, by rw [nMemb_self]; exact hx⟩ hne)
    exact hno z (mem_words.2 (hz.trans e1.symm)) hzy

/-- «g(g² − 1)λ ≤ P», P = g³λ (proof of Proposition 3). -/
theorem stGridLength : StGridLength := by
  intro g lam
  refine Nat.mul_le_mul_right _ ?_
  calc g * (g ^ 2 - 1) ≤ g * g ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = g ^ 3 := by ring

end Coding
