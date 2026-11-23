/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Len

/-!
# Section "Flat or contracting": quadrangles in a metric on the matrices over F₂

Definitions and lemmas for the proof of Theorem thm:alt (Paper/Alternative.lean). `nn w a W` is the paper's
n_a(W) = |a, a+W|², `BB w a W W'` is its B_a(W, W'), and `X p q S` is the matrix p·dg(S)·q: the matrices `X p q S` for
disjoint sets S, in one frame (p, q), are the transversal families (Nc/Flag/Transversal.lean).
-/

open Finset Matrix

namespace Nc.Flag

variable {m : ℕ}

/-- Square matrices over F₂. -/
abbrev Mt (m : ℕ) := Matrix (Fin m) (Fin m) F2

variable {w : Mt m → Mt m → ℝ}

theorem madd_self (M : Mt m) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

/-- The squared sides minus the squared diagonals of the quadrangle a, a+M, a+M+N, a+N. -/
def defect (w : Mt m → Mt m → ℝ) (a M N : Mt m) : ℝ :=
  w a (a + M) ^ 2 + w (a + M) (a + M + N) ^ 2 + w (a + M + N) (a + N) ^ 2 + w a (a + N) ^ 2 -
    (w a (a + M + N) ^ 2 + w (a + M) (a + N) ^ 2)

/-- The squared distance n_a(M) from `a` to `a + M`. -/
def nn (w : Mt m → Mt m → ℝ) (a M : Mt m) : ℝ := w a (a + M) ^ 2

theorem sum_defect (hw : ∀ a b, w a b = w b a) (M N : Mt m) :
    ∑ a, defect w a M N = 2 * (∑ a, nn w a M + ∑ a, nn w a N - ∑ a, nn w a (M + N)) := by
  have h1 : ∑ a, w (a + M) (a + M + N) ^ 2 = ∑ a, nn w a N :=
    Equiv.sum_comp (Equiv.addRight M) (fun a => nn w a N)
  have h2 : ∑ a, w (a + M + N) (a + N) ^ 2 = ∑ a, nn w a M := by
    rw [← Equiv.sum_comp (Equiv.addRight N) (fun a => nn w a M)]
    refine sum_congr rfl fun a _ => ?_
    show w (a + M + N) (a + N) ^ 2 = w (a + N) (a + N + M) ^ 2
    rw [hw, add_right_comm]
  have h3 : ∑ a, w (a + M) (a + N) ^ 2 = ∑ a, nn w a (M + N) := by
    rw [← Equiv.sum_comp (Equiv.addRight M) (fun a => nn w a (M + N))]
    refine sum_congr rfl fun a _ => ?_
    show w (a + M) (a + N) ^ 2 = w (a + M) (a + M + (M + N)) ^ 2
    have : a + M + (M + N) = a + N := by
      rw [add_assoc, ← add_assoc M M N, madd_self, zero_add]
    rw [this]
  have h4 : ∑ a, w a (a + M + N) ^ 2 = ∑ a, nn w a (M + N) := by
    refine sum_congr rfl fun a _ => ?_
    rw [nn, add_assoc]
  unfold defect
  simp only [sum_sub_distrib, sum_add_distrib]
  rw [h1, h2, h3, h4]
  show ∑ a, nn w a M + _ + _ + ∑ a, nn w a N - _ = _
  ring

/-- The matrix of a set of indices in a frame. -/
def X (p q : GLM (Fin m)) (S : Finset (Fin m)) : Mt m := (p : Mt m) * dg S * (q : Mt m)

theorem X_one (S : Finset (Fin m)) : X 1 1 S = dg S := by
  simp [X]

theorem X_empty (p q : GLM (Fin m)) : X p q ∅ = 0 := by
  simp [X, dg_empty]

theorem X_union (p q : GLM (Fin m)) {S T : Finset (Fin m)} (h : Disjoint S T) :
    X p q (S ∪ T) = X p q S + X p q T := by
  rw [X, dg_union h, Matrix.mul_add, Matrix.add_mul]
  rfl

/-- Every matrix is diagonal with entries 0 and 1 in some frame. -/
theorem exists_factor (M : Mt m) :
    ∃ (p q : GLM (Fin m)) (S : Finset (Fin m)), M = (p : Mt m) * dg S * (q : Mt m) := by
  obtain ⟨L, L', D, hM⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hu : ∀ L : List (TransvectionStruct (Fin m) F2),
      ∃ u : GLM (Fin m), (u : Mt m) = (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, by simp⟩
    | cons t L ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩ * u, ?_⟩
      rw [Units.val_mul, hu, List.map_cons, List.prod_cons]
  obtain ⟨u, hu1⟩ := hu L
  obtain ⟨v, hv1⟩ := hu L'
  refine ⟨u, v, univ.filter fun i => D i ≠ 0, ?_⟩
  have hD : Matrix.diagonal D = dg (univ.filter fun i => D i ≠ 0) := by
    unfold dg
    congr 1
    funext i
    have h2 : ∀ a : F2, a = if a ≠ 0 then 1 else 0 := by decide
    simpa using h2 (D i)
  rw [hM, hu1, hv1, hD]

theorem exists_X (M : Mt m) : ∃ (p q : GLM (Fin m)) (S : Finset (Fin m)), M = X p q S := exists_factor M

/-- The sum of |a, a + p·E·q|² over all a and all invertible p, q. -/
noncomputable def MD (w : Mt m → Mt m → ℝ) (E : Mt m) : ℝ := ∑ a, DM (fun M => w a (a + M)) E

theorem MD_eq (S : Finset (Fin m)) : MD w (dg S) =
    ∑ p : GLM (Fin m), ∑ q : GLM (Fin m), ∑ a, nn w a (X p q S) := by
  unfold MD DM
  rw [sum_comm]
  exact sum_congr rfl fun p _ => sum_comm

/-- The defects of the quadrangles with sides W = X p q S and W' = X p q T, added over all frames and all a. -/
theorem sum_all_defect (hw : ∀ a b, w a b = w b a) {S T : Finset (Fin m)} (h : Disjoint S T) :
    ∑ p : GLM (Fin m), ∑ q : GLM (Fin m), ∑ a, defect w a (X p q S) (X p q T) =
      2 * (MD w (dg S) + MD w (dg T) - MD w (dg (S ∪ T))) := by
  simp only [sum_defect hw, MD_eq]
  rw [← sum_add_distrib, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_add_distrib, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [X_union p q h]

/-- The scalar product B_a(M, N) = ½(n_a(M+N) − n_a(M) − n_a(N)). -/
noncomputable def BB (w : Mt m → Mt m → ℝ) (a M N : Mt m) : ℝ := (nn w a (M + N) - nn w a M - nn w a N) / 2

theorem BB_comm (a M N : Mt m) : BB w a M N = BB w a N M := by
  unfold BB
  rw [add_comm]
  ring

theorem add_cancel_left (M N : Mt m) : M + (M + N) = N := by
  rw [← add_assoc, madd_self, zero_add]

end Nc.Flag
