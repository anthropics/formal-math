/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The unitriangular group over F₂
-/

namespace Nc.Tower

open Matrix Finset

/-- The group SL_h(F₂) = GL_h(F₂). -/
abbrev SL2 (h : ℕ) : Type := Matrix.SpecialLinearGroup (Fin h) (ZMod 2)

theorem sl_pow_mem {G : Type*} [Group G] [Finite G] (S : Submonoid G) {a : G} (ha : a ∈ S) : a⁻¹ ∈ S := by
  have h : a⁻¹ = a ^ (orderOf a - 1) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
  rw [h]
  exact S.pow_mem ha _

/-- Upper unitriangular matrices. -/
def U (h : ℕ) : Subgroup (SL2 h) where
  carrier := {A | ∀ i j, (j < i → A.1 i j = 0) ∧ A.1 i i = 1}
  one_mem' := fun i j => ⟨fun hij => Matrix.one_apply_ne hij.ne', Matrix.one_apply_eq i⟩
  mul_mem' := by
    intro A B hA hB i j
    have h1 : ∀ i j k, j < i → A.1 i k * B.1 k j = 0 := by
      intro i j k hij
      rcases lt_or_ge k i with hk | hk
      · rw [(hA i k).1 hk, zero_mul]
      · rw [(hB k j).1 (lt_of_lt_of_le hij hk), mul_zero]
    refine ⟨fun hij => ?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => h1 i j k hij
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [(hA i i).2, (hB i i).2, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [(hA i k).1 h, zero_mul]
        · rw [(hB k i).1 h, mul_zero]
      · simp
  inv_mem' := by
    intro A hA
    let S : Submonoid (SL2 h) :=
      { carrier := {A | ∀ i j, (j < i → A.1 i j = 0) ∧ A.1 i i = 1}
        one_mem' := fun i j => ⟨fun hij => Matrix.one_apply_ne hij.ne', Matrix.one_apply_eq i⟩
        mul_mem' := by
          intro A B hA hB i j
          have h1 : ∀ i j k, j < i → A.1 i k * B.1 k j = 0 := by
            intro i j k hij
            rcases lt_or_ge k i with hk | hk
            · rw [(hA i k).1 hk, zero_mul]
            · rw [(hB k j).1 (lt_of_lt_of_le hij hk), mul_zero]
          refine ⟨fun hij => ?_, ?_⟩
          · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
            exact Finset.sum_eq_zero fun k _ => h1 i j k hij
          · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
            · rw [(hA i i).2, (hB i i).2, one_mul]
            · intro k _ hk
              rcases lt_or_gt_of_ne hk with h | h
              · rw [(hA i k).1 h, zero_mul]
              · rw [(hB k i).1 h, mul_zero]
            · simp }
    exact sl_pow_mem S hA

/-- The index j as a row. -/
def lo {h : ℕ} (j : Fin (h - 1)) : Fin h := ⟨j.1, by omega⟩

/-- The index j + 1 as a column. -/
def hi {h : ℕ} (j : Fin (h - 1)) : Fin h := ⟨j.1 + 1, by omega⟩

theorem lo_lt_hi {h : ℕ} (j : Fin (h - 1)) : lo j < hi j := by
  rw [Fin.lt_def]; simp [lo, hi]

theorem lo_ne_hi {h : ℕ} (j : Fin (h - 1)) : lo j ≠ hi j := (lo_lt_hi j).ne

/-- The simple root elements 1 + E_{j,j+1}. -/
def x (h : ℕ) (j : Fin (h - 1)) : U h :=
  ⟨⟨Matrix.transvection (lo j) (hi j) 1, Matrix.det_transvection_of_ne _ _ (lo_ne_hi j) 1⟩, by
    intro a b
    refine ⟨fun hab => ?_, ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne hab.ne', Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (lo_lt_hi j).not_gt
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨h1, h2⟩
      exact lo_ne_hi j (h1.trans h2.symm)⟩

theorem x_val (h : ℕ) (j : Fin (h - 1)) :
    ((x h j : SL2 h) : Matrix (Fin h) (Fin h) (ZMod 2)) = 1 + Matrix.single (lo j) (hi j) 1 := rfl

/-- The entries above the diagonal are free. -/
noncomputable def equivU (h : ℕ) : U h ≃ ({p : Fin h × Fin h // p.1 < p.2} → ZMod 2) where
  toFun A p := A.1.1 p.1.1 p.1.2
  invFun f := ⟨⟨Matrix.of fun i j => if hij : i < j then f ⟨(i, j), hij⟩ else if i = j then 1 else 0, by
      rw [Matrix.det_of_isUpperTriangular]
      · simp
      · intro i j hij
        have hij' : j < i := hij
        simp [not_lt_of_gt hij', hij'.ne']⟩, by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · simp [not_lt_of_gt hij, hij.ne']
    · simp⟩
  left_inv A := by
    refine Subtype.ext (Subtype.ext ?_)
    ext i j
    simp only [Matrix.of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [h2]; exact ((A.2 j j).2).symm
    · exact ((A.2 i j).1 (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hij' : i < j := hij
    simp [hij']

noncomputable instance (h : ℕ) : Fintype (U h) := Fintype.ofFinite _

theorem card_pairs (h : ℕ) : Fintype.card {p : Fin h × Fin h // p.1 < p.2} = h * (h - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
  have h1 : ∀ i : Fin h, (∑ j : Fin h, if i < j then 1 else 0) = h - 1 - i.1 := by
    intro i
    rw [← Finset.card_filter]
    have := Fin.card_Ioi i
    rw [← this]
    congr 1
    ext j
    simp
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => h - 1 - i),
    Finset.sum_range_reflect (fun i => i) h, Finset.sum_range_id]

/-- The order of U h. -/
theorem card_U (h : ℕ) : Fintype.card (U h) = 2 ^ (h * (h - 1) / 2) := by
  rw [Fintype.card_congr (equivU h), Fintype.card_fun, ZMod.card, card_pairs]

end Nc.Tower
