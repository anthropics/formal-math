/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Chain

/-!
# Coordinates
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

/-- Coordinates for the left action of a subgroup. -/
theorem exists_coord {P Q : Type*} [Group P] [Group Q] (φ : P →* Q) (hφ : Function.Injective φ) :
    ∃ co : Q → P, ∀ p q, co (φ p * q) = p * co q := by
  let r : Setoid Q :=
    { r := fun q q' => ∃ p, q' = φ p * q
      iseqv := ⟨fun q => ⟨1, by simp⟩, fun {q q'} ⟨p, hp⟩ => ⟨p⁻¹, by rw [hp, map_inv, inv_mul_cancel_left]⟩,
        fun {q q' q''} ⟨p, hp⟩ ⟨p', hp'⟩ => ⟨p' * p, by rw [hp', hp, map_mul, mul_assoc]⟩⟩ }
  have h1 : ∀ q : Q, ∃ p, q = φ p * (Quotient.mk r q).out := fun q => Quotient.exact (Quotient.out_eq (Quotient.mk r q))
  choose co hco using h1
  refine ⟨co, fun p q => ?_⟩
  apply hφ
  have h2 : Quotient.mk r (φ p * q) = Quotient.mk r q := (Quotient.sound (s := r) ⟨p, rfl⟩ : Quotient.mk r q = _).symm
  have h3 := hco (φ p * q)
  rw [h2] at h3
  have h4 := hco q
  have h5 : φ (co (φ p * q)) * (Quotient.mk r q).out = φ p * (φ (co q) * (Quotient.mk r q).out) := by
    rw [← h3, ← h4]
  rw [← mul_assoc] at h5
  rw [map_mul]
  exact mul_right_cancel h5

/-- One element of every pair of a free involution. -/
theorem exists_first {Q : Type*} [Finite Q] (i : Q → Q) (hi : ∀ q, i (i q) = q) (hne : ∀ q, i q ≠ q) :
    ∃ F : Q → Prop, ∀ q, F (i q) ↔ ¬ F q := by
  obtain ⟨N, ⟨φ⟩⟩ := Finite.exists_equiv_fin Q
  refine ⟨fun q => φ q < φ (i q), fun q => ?_⟩
  simp only [hi, not_lt]
  constructor
  · exact fun h => h.le
  · exact fun h => lt_of_le_of_ne h fun e => hne q (φ.injective e)

variable {h n : ℕ} [NeZero h]

/-- The image of the i-th unitriangular subgroup in SL_h(F₂). -/
noncomputable def thQ (i : Fin h) : U h →* SL2 h := (evG : G h 0 →* SL2 h).comp (th i)

theorem evG_th (i : Fin h) (u : U h) : evG (th i u : G h n) = thQ i u := by
  refine Subtype.ext ?_
  ext a b
  rw [thQ]
  change (evG (th0 i u.1 : G h n)).1 a b = (evG (th0 i u.1 : G h 0)).1 a b
  rw [evG_th0, evG_th0]

theorem thQ_injective (i : Fin h) : Function.Injective (thQ i : U h →* SL2 h) := by
  intro u v e
  exact Subtype.ext (evG_th0_injective (n := 0) i e)

/-- The coordinate of an element of SL_h(F₂) at its vertex of type i. -/
noncomputable def coQ (i : Fin h) : SL2 h → U h := (exists_coord (thQ i) (thQ_injective i)).choose

theorem coQ_mul (i : Fin h) (u : U h) (q : SL2 h) : coQ i (thQ i u * q) = u * coQ i q :=
  (exists_coord (thQ i) (thQ_injective i)).choose_spec u q

theorem x_ne_one (l : Fin (h - 1)) : x h l ≠ 1 := by
  intro e
  have h1 := congrFun (congrFun (congrArg (fun u : U h => u.1.1) e) (lo l)) (hi l)
  simp only [x_val] at h1
  rw [Matrix.add_apply, Matrix.single_apply_same] at h1
  have h2 : ((1 : U h).1.1 : Matrix (Fin h) (Fin h) (ZMod 2)) (lo l) (hi l) = 0 :=
    Matrix.one_apply_ne (lo_ne_hi l)
  rw [h2, Matrix.one_apply_ne (lo_ne_hi l)] at h1
  exact absurd h1 (by decide)

theorem x_mul_self (l : Fin (h - 1)) : x h l * x h l = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  refine (Matrix.transvection_mul_transvection_same _ _ (lo_ne_hi l) (1 : ZMod 2) 1).trans ?_
  rw [show (1 : ZMod 2) + 1 = 0 from rfl, Matrix.transvection_zero]
  rfl

theorem exists_other (h2 : 2 ≤ h) (k : Fin h) : ∃ i : Fin h, k ≠ i := by
  by_contra hc
  push Not at hc
  have h1 := hc (k - 1)
  exact sub_one_ne h2 k h1.symm

theorem gen_ne (h2 : 2 ≤ h) (k : Fin h) : evG (gen h2 k : G h n) ≠ 1 := by
  obtain ⟨i, hi⟩ := exists_other h2 k
  obtain ⟨l, rfl⟩ := exists_sh hi
  rw [← th_x h2 i l]
  intro e
  exact x_ne_one l (evG_th_eq_one e)

/-- The first chambers of the pairs of type k. -/
theorem exists_firstQ (h2 : 2 ≤ h) (k : Fin h) :
    ∃ F : SL2 h → Prop, ∀ q, F (evG (gen h2 k : G h 0) * q) ↔ ¬ F q := by
  refine exists_first _ (fun q => ?_) fun q e => ?_
  · rw [← mul_assoc, ← map_mul, gen_mul_self, map_one, one_mul]
  · exact gen_ne (n := 0) h2 k (by simpa using e)

/-- The first chambers of the pairs of type k. -/
def FQ (h2 : 2 ≤ h) (k : Fin h) : SL2 h → Prop := (exists_firstQ h2 k).choose

theorem evG_gen (h2 : 2 ≤ h) (k : Fin h) : evG (gen h2 k : G h n) = evG (gen h2 k : G h 0) := by
  obtain ⟨i, hi⟩ := exists_other h2 k
  obtain ⟨l, rfl⟩ := exists_sh hi
  rw [← th_x h2 i l, ← th_x h2 i l, evG_th, evG_th]

theorem FQ_iff (h2 : 2 ≤ h) (k : Fin h) (q : SL2 h) : FQ h2 k (evG (gen h2 k : G h n) * q) ↔ ¬ FQ h2 k q := by
  rw [evG_gen]
  exact (exists_firstQ h2 k).choose_spec q

theorem exists_firstU (l : Fin (h - 1)) : ∃ F : U h → Prop, ∀ u, F (x h l * u) ↔ ¬ F u := by
  refine exists_first _ (fun u => ?_) fun u e => ?_
  · rw [← mul_assoc, x_mul_self, one_mul]
  · exact x_ne_one l (by simpa using e)

/-- The first elements of the pairs {u, x_l u}. -/
def FU (l : Fin (h - 1)) : U h → Prop := (exists_firstU l).choose

theorem FU_iff (l : Fin (h - 1)) (u : U h) : FU l (x h l * u) ↔ ¬ FU l u := (exists_firstU l).choose_spec u

end Nc.Tower
