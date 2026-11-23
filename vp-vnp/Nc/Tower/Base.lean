/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Diam

/-!
# The diameter of the first group; the diameter in general
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable {h n : ℕ} [NeZero h] {h2 : 2 ≤ h}

/-- A transvection as an element of the group. -/
def tSL (τ : TransvectionStruct (Fin h) (ZMod 2)) : SL2 h := ⟨τ.toMatrix, τ.det⟩

theorem tSL_prod (l : List (TransvectionStruct (Fin h) (ZMod 2))) :
    ((l.map tSL).prod : SL2 h).1 = (l.map TransvectionStruct.toMatrix).prod := by
  induction l with
  | nil => rfl
  | cons τ l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    rfl

theorem exists_transvections (A : SL2 h) : ∃ l : List (TransvectionStruct (Fin h) (ZMod 2)), A = (l.map tSL).prod := by
  obtain ⟨L, L', D, hD⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A.1
  have h1 : ∏ i, D i = 1 := by
    have h3 := A.2
    rw [hD, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod, TransvectionStruct.det_toMatrix_prod,
      det_diagonal, one_mul, mul_one] at h3
    exact h3
  have h3 : ∀ i, D i = 1 := by
    intro i
    have h4 : D i ≠ 0 := by
      intro h0
      rw [Finset.prod_eq_zero (mem_univ i) h0] at h1
      exact absurd h1 (by decide)
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact key _ h4
  have h5 : diagonal D = 1 := by
    have : D = fun _ => 1 := funext h3
    rw [this, diagonal_one]
  rw [h5, mul_one] at hD
  refine ⟨L ++ L', Subtype.ext ?_⟩
  rw [tSL_prod, List.map_append, List.prod_append]
  exact hD

theorem th0_tSL (τ : TransvectionStruct (Fin h) (ZMod 2)) : (th0 0 (tSL τ) : G h n) = El τ.i τ.j τ.hij (cst (n + 1) τ.c) := by
  refine Subtype.ext ?_
  ext a b
  have hw : ∀ a : Fin h, (wt 0 a : (R (n + 1))ˣ) = 1 := fun a => if_neg (Fin.not_lt_zero a)
  rw [th0_val, shMat_apply, hw, hw, sub_zero, sub_zero, El_val]
  have e : (tSL τ).1 = transvection τ.i τ.j τ.c := rfl
  rw [e, transvection, transvection, Matrix.add_apply, Matrix.add_apply, map_add, Matrix.single_apply,
    Matrix.single_apply]
  simp only [Units.val_one, inv_one, one_mul, mul_one]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, map_zero]
  · split_ifs
    · rfl
    · exact map_zero _

theorem WL.tSL (h3 : 3 ≤ h) (τ : TransvectionStruct (Fin h) (ZMod 2)) : ∃ N, WL h2 (th0 0 (tSL τ) : G h n) N := by
  rw [th0_tSL]
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases key τ.c with h0 | h1
  · refine ⟨0, ?_⟩
    have : (El τ.i τ.j τ.hij (cst (n + 1) τ.c) : G h n) = 1 := by
      refine Subtype.ext ?_
      rw [El_val, h0, map_zero, transvection_zero]
      rfl
    rw [this]
    exact WL.one
  · refine ⟨4 ^ (h + 3) * (2 * (n + 1)) ^ 3, ?_⟩
    rw [h1, map_one]
    exact WL.el_one h3 τ.i τ.j τ.hij

theorem WL.const (h3 : 3 ≤ h) (A : SL2 h) : ∃ N, WL h2 (th0 0 A : G h n) N := by
  obtain ⟨l, rfl⟩ := exists_transvections A
  induction l with
  | nil => exact ⟨0, by simpa using WL.one⟩
  | cons τ l ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := WL.tSL (n := n) (h2 := h2) h3 τ
    refine ⟨M + N, ?_⟩
    rw [List.map_cons, List.prod_cons, map_mul]
    exact hM.mul hN

theorem exists_base (h2 : 2 ≤ h) (h3 : 3 ≤ h) : ∃ C, ∀ g : G h 0, WL h2 g C := by
  have h1 : ∀ g : G h 0, ∃ N, WL h2 g N := by
    intro g
    obtain ⟨N, hN⟩ := WL.const (n := 0) (h2 := h2) h3 (evG g)
    refine ⟨N, ?_⟩
    have : g = th0 0 (evG g) := by
      apply evG_bijective_zero.1
      refine Subtype.ext ?_
      ext a b
      rw [evG_th0, sub_zero, sub_zero]
    rw [this]
    exact hN
  choose N hN using h1
  exact ⟨univ.sup N, fun g => (hN g).mono (Finset.le_sup (mem_univ g))⟩

/-- **The diameter.** -/
theorem exists_diam (h : ℕ) [NeZero h] (h2 : 2 ≤ h) (h3 : 3 ≤ h) :
    ∃ C, ∀ (n : ℕ) (g : G h n), WL h2 g (C * (n + 1) ^ 7) := by
  obtain ⟨C, hC⟩ := exists_base h2 h3
  let B := h * h * (5 * (4 ^ (h + 3) * 9 * 8))
  refine ⟨C + B, fun n => ?_⟩
  induction n with
  | zero => intro g; exact (hC g).mono (by simp)
  | succ n ih =>
    intro g
    refine (WL.lift h3 ih g).mono ?_
    have h4 : h * h * (5 * bQ h n) ≤ B * (n + 1) ^ 6 := by
      have h5 : (n + 2) ^ 3 ≤ 8 * (n + 1) ^ 3 := by
        calc (n + 2) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ = 8 * (n + 1) ^ 3 := by ring
      have h6 : bQ h n ≤ 4 ^ (h + 3) * 9 * 8 * (n + 1) ^ 6 := by
        unfold bQ
        calc 4 ^ (h + 3) * (9 * (n + 2) ^ 3) * (n + 1) ^ 3 ≤ 4 ^ (h + 3) * (9 * (8 * (n + 1) ^ 3)) * (n + 1) ^ 3 := by
              gcongr
          _ = _ := by ring
      calc h * h * (5 * bQ h n) ≤ h * h * (5 * (4 ^ (h + 3) * 9 * 8 * (n + 1) ^ 6)) := by gcongr
        _ = B * (n + 1) ^ 6 := by simp only [B]; ring
    have h7 : (n + 1) ^ 7 + (n + 1) ^ 6 ≤ (n + 1 + 1) ^ 7 := by
      have h8 : (n + 1) ^ 6 ≤ (n + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      calc (n + 1) ^ 7 + (n + 1) ^ 6 = (n + 1) ^ 6 * (n + 2) := by ring
        _ ≤ (n + 2) ^ 6 * (n + 2) := Nat.mul_le_mul_right _ h8
        _ = (n + 1 + 1) ^ 7 := by ring
    calc (C + B) * (n + 1) ^ 7 + h * h * (5 * bQ h n) ≤ (C + B) * (n + 1) ^ 7 + B * (n + 1) ^ 6 :=
          Nat.add_le_add_left h4 _
      _ ≤ (C + B) * (n + 1) ^ 7 + (C + B) * (n + 1) ^ 6 := by
          refine Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      _ = (C + B) * ((n + 1) ^ 7 + (n + 1) ^ 6) := by ring
      _ ≤ (C + B) * (n + 1 + 1) ^ 7 := Nat.mul_le_mul_left _ h7

end Nc.Tower
