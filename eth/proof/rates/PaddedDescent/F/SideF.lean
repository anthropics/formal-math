/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.RebalG
public import PaddedDescent.F.Price
public import StepMachines.Prog.SidePresents
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff

/-! # The network of one term of one level of the recursion (Section 5), read off an explicit table (cutF = cutW, itemF = sideItem, StS, StChild)

`sideF` presents `Grid.sideN`; with `StRG` this gives the step for one term y, where the number y
names one choice of a piece for every rectangle (the ι in the proof of Proposition 3): the child has
Z = `sideZ` of y, and the
bounds `lamNext`, `bNext` hold for it. -/

public section

namespace PaddedDescent.F.SideF

open Groundwork Groundwork.Prog Groundwork.Grid Finset

/-- `cutF` is `cutW`, if the pad has at least 2^|x| units. -/
theorem cutF_eq {pad : U} (tr top : Bool) (i : ℕ) {x : List Bool} (y w : List Bool) (h : 2 ^ x.length ≤ pad.length) :
    cutF pad tr top i x y w = cutW tr top i x y w := by
  unfold cutF cutW topW botW botF
  rw [sumF_eq h]
  simp only [prodL_eq]

/-- `itemF` is `sideItem`, if the pad has at least 2^n units. -/
theorem itemF_eq {pad : U} (g : ℕ) (tr : Bool) {n : ℕ} (y a b : ℕ) (z θ : List Bool) (i i' : ℕ)
    (h : 2 ^ n ≤ pad.length) : itemF pad g tr n y a b z θ i i' = sideItem g tr n y a b z θ i i' :=
  cutF_eq _ _ _ _ _ ((Nat.pow_le_pow_right (by norm_num) (length_he_le g n z i _)).trans h)

/-- `StS`: `sideF` presents the network `Grid.sideN` of one term, if the pad is long enough. -/
theorem stS : StS := by
  intro pad gU tr ℓU y T h
  refine RebalF.presents sideF _ _ (fun a => rfl) (fun a b hab => sideN_c _ _ _ _ _ hab)
    (fun a b hab => sideN_lab _ _ _ _ _ hab) (fun a z hz => ?_) (fun a b z θ hab hz hθ => ?_)
  · change sideWF gU.length tr ℓU.length y T (a.val, z) = _
    rw [sideN_W_eq (lam := fun n : ℕ => n) (instOf (K := gU.length * gU.length) T) ℓU.length y a hz]
    unfold sideWF sideWv
    cases sideChk gU.length tr (fun n : ℕ => n) ((ℓU.length, y), (a.val, z)) with
    | false => simp
    | true =>
      simp only [cond_true, if_true, prodL_eq]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [dif_pos (node_lt tr a.2 (Finset.mem_range.1 hi)), instOf, map_range_eq_ofFn]
  · change sideFF pad gU.length tr ℓU.length y ((a.val, b.val), (z, θ)) = _
    rw [sideN_f_eq (lam := fun n : ℕ => n) (instOf (K := gU.length * gU.length) T) ℓU.length y hab hz hθ]
    unfold sideFF sideFv
    cases sideEdges gU.length tr (fun n : ℕ => n) ((ℓU.length, y), ((a.val, b.val), (z, θ))) with
    | false => simp
    | true =>
      simp only [cond_true, if_true, prodL_eq, itemF_eq _ _ _ _ _ _ _ _ _ h]

/-! ### The arithmetic of one level -/

/-- `Pn g` is monotone in the label length. -/
theorem Pn_mono {g a b : ℕ} (h : a ≤ b) : Pn g a ≤ Pn g b := Nat.mul_le_mul_left _ h

/-- `Ubar g` is monotone in the label length. -/
theorem Ubar_mono {g a b : ℕ} (h : a ≤ b) : Ubar g a ≤ Ubar g b := by
  unfold Ubar
  have h1 : g ^ 2 * (g - 1) * a ≤ g ^ 2 * (g - 1) * b := Nat.mul_le_mul_left _ h
  have h2 : 717 * g ^ 4 * a / 800 ≤ 717 * g ^ 4 * b / 800 := Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
  omega

/-- `capM g` is monotone in the label length. -/
theorem capM_mono {g a b : ℕ} (h : a ≤ b) : capM g a ≤ capM g b := by
  unfold capM
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h) (Nat.mul_le_mul_left _ h)

/-- `lamNext K g` is monotone in the label length. -/
theorem lamNext_mono {K g a b : ℕ} (h : a ≤ b) : lamNext K g a ≤ lamNext K g b := by
  unfold lamNext
  exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.add_le_add (Nat.mul_le_mul_left _ (Ubar_mono h))
    (Nat.mul_le_mul_left _ (capM_mono h)))) 1

/-- `bNext K g` is monotone in the label length. -/
theorem bNext_mono {K g a b B : ℕ} (h : a ≤ b) : bNext K g a B ≤ bNext K g b B := by
  unfold bNext
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (Pn_mono h))
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _)))

/-- x ≤ y·(x / y + 1) for y > 0. -/
theorem le_mul_div_succ (x : ℕ) {y : ℕ} (hy : 0 < y) : x ≤ y * (x / y + 1) :=
  (Nat.lt_mul_div_succ x hy).le

/-- One term: the core of `StE`. (The hypothesis y < (ℓ+1)^R of the statement is not used.) -/
theorem stChild : StChild := by
  intro pad L Λ B I y hK hcol hI hb _
  have hℓ1 : 1 ≤ I.1.length := hI.lam_pos
  have hℓΛ : I.1.length ≤ Λ := hI.lam_le
  have hg0 : 0 < L.2.length := RebalF.pos_of_colOK (by omega) hcol
  have two : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨tr, htr⟩ : ∃ tr, tr = decide (priceCol L.2.length I.1.length y < priceRow L.2.length I.1.length y) := ⟨_, rfl⟩
  have hU : (sideN L.2.length tr I.1.length (instOf (K := L.2.length * L.2.length) I.2) y).U ≤ Ubar L.2.length I.1.length := by
    rw [htr]; exact Price.U_side_le _ _ _ _
  have hlam : 2 ^ I.1.length ≤ pad.length := by
    refine (two ?_).trans hb.lab
    have h1 : 1 ≤ 2 * L.2.length ^ 3 := by
      have := Nat.pow_pos (n := 3) hg0
      omega
    calc I.1.length ≤ Λ := hℓΛ
      _ = 1 * Λ := (Nat.one_mul _).symm
      _ ≤ Pn L.2.length Λ := Nat.mul_le_mul_right _ h1
  have hN := stS pad L.2 tr I.1 y I.2 hlam
  have hS := sideN_sized tr hℓ1 (Table.stT3c _ _ _ _ hI) y
  have hD0 : 0 < Dcol * L.1.length ^ 2 := by
    have : 0 < Dcol := by unfold Dcol; positivity
    positivity
  have hM0 : 0 < capM L.2.length I.1.length := by unfold capM; positivity
  have hβ : Dcol * (sideN L.2.length tr I.1.length (instOf (K := L.2.length * L.2.length) I.2) y).U +
      3 * L.2.length ^ 2 * capM L.2.length I.1.length ≤ Dcol * L.1.length ^ 2 * lamNext L.1.length L.2.length I.1.length :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hU) _).trans (le_mul_div_succ _ hD0)
  obtain ⟨J, h1, h2, h3, h4⟩ := RebalF.stRG _ pad L.1.length L.2.length (lamNext L.1.length L.2.length I.1.length) sideF
    ((pad, L.2, tr), (I.1, y, I.2)) _ _ _ (capM L.2.length I.1.length) hK hcol hN hS hM0
    (fun a b hab => by rw [sideN_c _ _ _ _ _ hab]; exact sideCap_le tr hℓ1 y a b) (Nat.le_add_left 1 _) hβ hb.col
    ((two (Nat.mul_le_mul_right _ (Pn_mono hℓΛ))).trans hb.st) ((two (Pn_mono hℓΛ)).trans hb.lab)
    ((two (Nat.mul_le_mul_left _ (lamNext_mono hℓΛ))).trans hb.tab)
  refine ⟨J, ?_, by rw [h2, value_sideN], ?_⟩
  · unfold childF sideCtx
    rw [← htr]
    exact h1
  · exact ⟨h4.lam_pos, h4.lam_le.trans (lamNext_mono hℓΛ), h4.rows, h4.row_len,
      fun r hr z hz => (h4.abs_le r hr z hz).trans (two (bNext_mono hℓΛ))⟩

end PaddedDescent.F.SideF
