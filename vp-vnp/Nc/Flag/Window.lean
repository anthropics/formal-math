/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Act
import Nc.Flag.Walk

/-!
# Windows of the unitriangular group acting on a complete CAT(0) space
-/

open Finset Matrix

namespace Nc.Flag

open Cat
open Nc.Tower (U SL2 lo hi x)

variable {h : ℕ}

/-- A smaller window. -/
theorem win_win {p n p' n' : ℕ} (hp : p + n ≤ h) (hp' : p' + n' ≤ n) (hpp : p + p' + n' ≤ h)
    (A : U n') : win hp (win hp' A) = win hpp A := by
  apply mat_inj
  rw [mat_win, mat_win, mat_win]
  have e : wi hp * wi hp' = wi hpp := by
    ext i j
    simp only [Matrix.mul_apply, wi, Matrix.of_apply]
    rw [sum_eq_single (we hp' j)]
    · have : we hp (we hp' j) = we hpp j := by
        simp only [we, Fin.ext_iff]
        omega
      simp [this]
    · intro c _ hc
      simp [hc]
    · simp
  unfold wm
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, ← e, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  abel

theorem wi_disj {p n p' n' : ℕ} (hp : p + n ≤ h) (hp' : p' + n' ≤ h) (hd : p + n ≤ p') :
    (wi hp)ᵀ * wi hp' = 0 := by
  ext i j
  simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply, Matrix.zero_apply]
  refine sum_eq_zero fun k _ => ?_
  by_cases h1 : k = we hp i
  · have h2 : k ≠ we hp' j := by
      rw [h1]
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp [h2]
  · simp [h1]

/-- Disjoint windows commute. -/
theorem win_comm {p n p' n' : ℕ} (hp : p + n ≤ h) (hp' : p' + n' ≤ h) (hd : p + n ≤ p')
    (A : U n) (B : U n') : win hp A * win hp' B = win hp' B * win hp A := by
  apply mat_inj
  rw [mat_mul, mat_mul, mat_win, mat_win]
  have h1 := wi_disj hp hp' hd
  have h2 : (wi hp')ᵀ * wi hp = 0 := by
    rw [← Matrix.transpose_transpose (wi hp), ← Matrix.transpose_mul, h1, Matrix.transpose_zero]
  have z1 : ∀ (X : Matrix (Fin n) (Fin n) F2) (Y : Matrix (Fin n') (Fin n') F2),
      wi hp * X * (wi hp)ᵀ * (wi hp' * Y * (wi hp')ᵀ) = 0 := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp)ᵀ) (wi hp'), h1]
    simp
  have z2 : ∀ (X : Matrix (Fin n) (Fin n) F2) (Y : Matrix (Fin n') (Fin n') F2),
      wi hp' * Y * (wi hp')ᵀ * (wi hp * X * (wi hp)ᵀ) = 0 := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp')ᵀ) (wi hp), h2]
    simp
  unfold wm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, z1, z2]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- The homomorphism of a window (trivial if it doesn't fit). -/
def wh (h p n : ℕ) : U n →* U h := if hp : p + n ≤ h then win hp else 1

theorem wh_eq {p n : ℕ} (hp : p + n ≤ h) : wh h p n = win hp := dif_pos hp

variable {Z : Type*} [MetricSpace Z] (A : IsoAct (U h) Z)

namespace IsoAct

/-- The action of a window. -/
def W (p n : ℕ) : IsoAct (U n) Z := A.comap (wh h p n)

/-- The displacement by a generator. -/
noncomputable def e (j : ℕ) (z : Z) : ℝ :=
  if hj : j < h - 1 then dist z (A.act (x h ⟨j, hj⟩) z) else 0

theorem e_nonneg (j : ℕ) (z : Z) : 0 ≤ A.e j z := by
  unfold e
  split_ifs
  · exact dist_nonneg
  · exact le_rfl

theorem Fix.sub {p n p' n' : ℕ} {z : Z} (hz : (A.W p n).Fix z) (h1 : p ≤ p')
    (h2 : p' + n' ≤ p + n) (h3 : p + n ≤ h) : (A.W p' n').Fix z := by
  intro g
  have e1 : wh h p' n' g = wh h p n (win (p := p' - p) (n := n') (h := n) (by omega) g) := by
    rw [wh_eq (by omega), wh_eq h3, win_win h3 (by omega) (by omega)]
    have : p + (p' - p) = p' := by omega
    congr! 2
    exact this.symm
  show A.act (wh h p' n' g) z = z
  rw [e1]
  exact hz _

theorem wh_comm {p n p' n' : ℕ} (hd : p + n ≤ p') (hp' : p' + n' ≤ h) (a : U n) (b : U n') :
    wh h p n a * wh h p' n' b = wh h p' n' b * wh h p n a := by
  rw [wh_eq (by omega), wh_eq hp', win_comm _ _ hd]

theorem wh_x {j : ℕ} (hj : j < h - 1) : wh h j 2 (x 2 ⟨0, by omega⟩) = x h ⟨j, hj⟩ := by
  rw [wh_eq (by omega), win_x]
  rfl

theorem e_zero {p n j : ℕ} {z : Z} (hz : (A.W p n).Fix z) (h1 : p ≤ j) (h2 : j + 2 ≤ p + n)
    (h3 : p + n ≤ h) : A.e j z = 0 := by
  have hj : j < h - 1 := by omega
  have h4 := hz.sub A h1 h2 h3
  unfold e
  rw [dif_pos hj, ← wh_x hj]
  have := h4 (x 2 ⟨0, by omega⟩)
  rw [show A.act (wh h j 2 (x 2 ⟨0, by omega⟩)) z = z from this, dist_self]

theorem e_le {p n j : ℕ} {y : Z} (hy : (A.W p n).Fix y) (h1 : p ≤ j) (h2 : j + 2 ≤ p + n)
    (h3 : p + n ≤ h) (z : Z) : A.e j z ≤ 2 * dist z y := by
  have hj : j < h - 1 := by omega
  have h4 := hy.sub A h1 h2 h3 (x 2 ⟨0, by omega⟩)
  have h5 : A.act (x h ⟨j, hj⟩) y = y := by rw [← wh_x hj]; exact h4
  unfold e
  rw [dif_pos hj]
  refine (dist_triangle z y _).trans ?_
  conv_lhs => rw [← h5]
  rw [A.iso', h5, dist_comm y z]
  linarith

end IsoAct

end Nc.Flag
