/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Ring
import Nc.Tower.UT

/-!
# The groups SL_h(F₂[s]/(s^{n+1})) and their h unitriangular subgroups
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable (h n : ℕ) [NeZero h]

/-- The group. -/
abbrev G : Type := Matrix.SpecialLinearGroup (Fin h) (R (n + 1))

/-- The unit t. -/
noncomputable def tu : (R (n + 1))ˣ := (isUnit_t (n + 1)).unit

theorem tu_val : ((tu n : (R (n + 1))ˣ) : R (n + 1)) = t (n + 1) := rfl

variable {h n}

/-- The weights of the shift by i: the places that were carried over. -/
noncomputable def wt (i a : Fin h) : (R (n + 1))ˣ := if a < i then (tu n)⁻¹ else 1

/-- Conjugation by the i-th power of the shift. -/
noncomputable def shMat (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) : Matrix (Fin h) (Fin h) (R (n + 1)) :=
  diagonal (fun a => ((wt i a : (R (n + 1))ˣ) : R (n + 1))) *
    ((A.map (cst (n + 1))).submatrix (Equiv.subRight i) (Equiv.subRight i) *
      diagonal (fun a => (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1))))

theorem shMat_apply (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (a b : Fin h) :
    (shMat i A : Matrix (Fin h) (Fin h) (R (n + 1))) a b =
      (wt i a : (R (n + 1))ˣ) * (cst (n + 1) (A (a - i) (b - i)) * ((wt i b)⁻¹ : (R (n + 1))ˣ)) := by
  rw [shMat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

theorem shMat_one (i : Fin h) : (shMat i 1 : Matrix (Fin h) (Fin h) (R (n + 1))) = 1 := by
  ext a b
  rw [shMat_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · have : a - i ≠ b - i := fun e => hab (sub_left_injective e)
    rw [Matrix.one_apply_ne this, Matrix.one_apply_ne hab]
    simp

theorem shMat_mul (i : Fin h) (A B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (shMat i (A * B) : Matrix (Fin h) (Fin h) (R (n + 1))) = shMat i A * shMat i B := by
  ext a b
  rw [shMat_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [shMat_apply]
  rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight i) _ _ fun c => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, map_mul]
  have := Units.inv_mul (wt i (c + i) : (R (n + 1))ˣ)
  linear_combination (-(wt i a : (R (n + 1))ˣ) * cst (n + 1) (A (a - i) c) *
    cst (n + 1) (B c (b - i)) * ((wt i b)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) * this

theorem det_shMat (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (shMat i A : Matrix (Fin h) (Fin h) (R (n + 1))).det = cst (n + 1) A.det := by
  rw [shMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have : (∏ a, ((wt i a : (R (n + 1))ˣ) : R (n + 1))) * ∏ a, (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => Units.mul_inv _
  linear_combination (cst (n + 1) A.det) * this

/-- The embedding of SL_h(F₂) shifted by i. -/
noncomputable def th0 (i : Fin h) : SL2 h →* G h n where
  toFun A := ⟨shMat i A.1, by rw [det_shMat, A.2, map_one]⟩
  map_one' := Subtype.ext (shMat_one i)
  map_mul' A B := Subtype.ext (shMat_mul i A.1 B.1)

theorem th0_val (i : Fin h) (A : SL2 h) : (th0 i A : G h n).1 = shMat i A.1 := rfl

/-- The value at s = 0. -/
noncomputable def evG : G h n →* SL2 h := Matrix.SpecialLinearGroup.map (ev n)

theorem evG_apply (g : G h n) (a b : Fin h) : (evG g).1 a b = ev n (g.1 a b) := rfl

theorem ev_wt (i a : Fin h) : ev n ((wt i a : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
  rw [wt]
  split_ifs
  · have h1 : ev n ((tu n : (R (n + 1))ˣ) : R (n + 1)) = 1 := ev_t n
    have h2 := congrArg (ev n) (Units.mul_inv (tu n))
    rw [map_mul, h1, one_mul, map_one] at h2
    exact h2
  · simp

theorem ev_wt_inv (i a : Fin h) : ev n (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
  have h2 := congrArg (ev n) (Units.mul_inv (wt i a : (R (n + 1))ˣ))
  rw [map_mul, ev_wt, one_mul, map_one] at h2
  exact h2

theorem evG_th0 (i : Fin h) (A : SL2 h) (a b : Fin h) : (evG (th0 i A : G h n)).1 a b = A.1 (a - i) (b - i) := by
  rw [evG_apply, th0_val, shMat_apply, map_mul, map_mul, ev_wt, ev_wt_inv, ev_cst, one_mul, mul_one]

theorem evG_th0_injective (i : Fin h) : Function.Injective fun A : SL2 h => evG (th0 i A : G h n) := by
  intro A B e
  refine Subtype.ext ?_
  ext a b
  have := congrFun (congrFun (congrArg Subtype.val e) (a + i)) (b + i)
  simp only at this
  rw [evG_th0, evG_th0, add_sub_cancel_right, add_sub_cancel_right] at this
  exact this

/-- The h unitriangular subgroups. -/
noncomputable def th (i : Fin h) : U h →* G h n := (th0 i).comp (U h).subtype

theorem th_injective (i : Fin h) : Function.Injective (th i : U h →* G h n) := by
  intro A B e
  exact Subtype.ext (evG_th0_injective (n := n) i (congrArg evG e))

theorem evG_th_eq_one {i : Fin h} {u : U h} (e : evG (th i u : G h n) = 1) : u = 1 := by
  refine Subtype.ext (evG_th0_injective (n := n) i ?_)
  simp only
  have h1 : (th i u : G h n) = th0 i u.1 := rfl
  rw [← h1, e]
  simp

variable (n) in
/-- The entry of the generators. -/
noncomputable def tt (k : Fin h) : R (n + 1) := if k = 0 then t (n + 1) else 1

theorem sub_one_ne (h2 : 2 ≤ h) (k : Fin h) : k - 1 ≠ k := by
  intro e
  have : (1 : Fin h) = 0 := by
    have := congrArg (fun x => k - x) e
    simpa using this
  have := congrArg Fin.val this
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The generators: involutions of type k. -/
noncomputable def gen (h2 : 2 ≤ h) (k : Fin h) : G h n :=
  ⟨transvection (k - 1) k (tt n k), det_transvection_of_ne _ _ (sub_one_ne h2 k) _⟩

theorem gen_val (h2 : 2 ≤ h) (k : Fin h) : (gen h2 k : G h n).1 = transvection (k - 1) k (tt n k) := rfl

theorem gen_mul_self (h2 : 2 ≤ h) (k : Fin h) : (gen h2 k : G h n) * gen h2 k = 1 := by
  refine Subtype.ext ((transvection_mul_transvection_same _ _ (sub_one_ne h2 k) (tt n k) (tt n k)).trans ?_)
  rw [add_self, transvection_zero]
  rfl

/-- The type i + 1 + l. -/
def sh (i : Fin h) (l : Fin (h - 1)) : Fin h := hi l + i

theorem sh_sub_one (h2 : 2 ≤ h) (i : Fin h) (l : Fin (h - 1)) : sh i l - 1 = lo l + i := by
  have : (hi l : Fin h) = lo l + 1 := by
    refine Fin.ext ?_
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
    have := l.2
    simp only [lo, hi]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [sh, this]
  abel

theorem sh_ne (i : Fin h) (l : Fin (h - 1)) : sh i l ≠ i := by
  intro e
  have h1 : (hi l : Fin h) = 0 := by simpa [sh] using e
  have := congrArg Fin.val h1
  simp [hi] at this

theorem sh_injective (i : Fin h) : Function.Injective (sh i) := by
  intro l l' e
  have h1 : (hi l : Fin h) = hi l' := by simpa [sh] using e
  have := congrArg Fin.val h1
  simp only [hi] at this
  exact Fin.ext (by omega)

theorem exists_sh {i k : Fin h} (hk : k ≠ i) : ∃ l, sh i l = k := by
  have h1 : (k - i).1 ≠ 0 := by
    intro e
    exact hk (sub_eq_zero.1 (Fin.ext e))
  have h3 := (k - i).2
  refine ⟨⟨(k - i).1 - 1, by omega⟩, ?_⟩
  have : (hi ⟨(k - i).1 - 1, by omega⟩ : Fin h) = k - i := by
    refine Fin.ext ?_
    simp only [hi]
    omega
  rw [sh, this, sub_add_cancel]

theorem wt_sub_one (h2 : 2 ≤ h) {i k : Fin h} (hk : k ≠ i) :
    ((wt i (k - 1) : (R (n + 1))ˣ) : R (n + 1)) * ((wt i k)⁻¹ : (R (n + 1))ˣ) = tt n k := by
  by_cases h0 : k = 0
  · subst h0
    have hi0 : (0 : Fin h) < i := Fin.pos_iff_ne_zero.2 hk.symm
    have hl : ¬ ((0 : Fin h) - 1 < i) := by
      intro hlt
      have h1 : ((0 : Fin h) - 1).1 = h - 1 := by
        rw [zero_sub, Fin.val_neg']
        rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega), Nat.mod_eq_of_lt (by omega)]
      have h2' := Fin.lt_def.1 hlt
      have := i.2
      omega
    rw [wt, wt, if_neg hl, if_pos hi0, tt, if_pos rfl, inv_inv, Units.val_one, one_mul, tu_val]
  · have h1 : (k - 1).1 = k.1 - 1 := by
      have hk0 : 0 < k.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
      have h3 : (1 : Fin h) ≤ k := by
        rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
        exact hk0
      rw [Fin.sub_val_of_le h3, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
    have hk0 : 0 < k.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
    have hki : k.1 ≠ i.1 := fun e => hk (Fin.ext e)
    have h2' : k - 1 < i ↔ k < i := by
      rw [Fin.lt_def, Fin.lt_def, h1]
      omega
    rw [wt, wt, tt, if_neg h0]
    by_cases hlt : k < i
    · rw [if_pos (h2'.2 hlt), if_pos hlt]
      exact Units.mul_inv _
    · rw [if_neg (fun e => hlt (h2'.1 e)), if_neg hlt]
      simp

/-- The simple root elements of the i-th unitriangular subgroup are generators. -/
theorem th_x (h2 : 2 ≤ h) (i : Fin h) (l : Fin (h - 1)) : (th i (x h l) : G h n) = gen h2 (sh i l) := by
  refine Subtype.ext ?_
  have e1 : (th i (x h l) : G h n).1 = shMat i (1 + Matrix.single (lo l) (hi l) 1) := rfl
  rw [e1, gen_val, transvection, sh_sub_one h2]
  ext a b
  rw [shMat_apply, Matrix.add_apply, Matrix.add_apply]
  by_cases hab : a = b
  · subst hab
    have h1 : ¬ (lo l = a - i ∧ hi l = a - i) := fun e => lo_ne_hi l (e.1.trans e.2.symm)
    have h3 : ¬ (lo l + i = a ∧ sh i l = a) := by
      rintro ⟨e1, e2⟩
      have : lo l + i = hi l + i := e1.trans e2.symm
      exact lo_ne_hi l (add_right_cancel this)
    rw [Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h3]
    simp
  · have h4 : a - i ≠ b - i := fun e => hab (sub_left_injective e)
    rw [Matrix.one_apply_ne h4, Matrix.one_apply_ne hab, zero_add, zero_add]
    by_cases h1 : lo l = a - i ∧ hi l = b - i
    · have ha : lo l + i = a := by rw [h1.1, sub_add_cancel]
      have hb : sh i l = b := by rw [sh, h1.2, sub_add_cancel]
      rw [h1.1, h1.2, Matrix.single_apply_same, map_one, one_mul, sub_add_cancel, hb, Matrix.single_apply_same]
      have := wt_sub_one (n := n) h2 (sh_ne i l)
      rw [sh_sub_one h2, ha, hb] at this
      exact this
    · have h3 : ¬ (lo l + i = a ∧ sh i l = b) := by
        rintro ⟨e1, e2⟩
        exact h1 ⟨by rw [← e1, add_sub_cancel_right], by rw [← e2, sh, add_sub_cancel_right]⟩
      rw [Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h3]
      simp

end Nc.Tower
