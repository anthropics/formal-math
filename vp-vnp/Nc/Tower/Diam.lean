/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Words

/-!
# The diameter
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable {h n : ℕ} [NeZero h] {h2 : 2 ≤ h}

/-- A trace-zero matrix whose layer element is a product of at most N generators. -/
def PL (h2 : 2 ≤ h) (n : ℕ) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (N : ℕ) : Prop :=
  ∃ hA : A.trace = 0, WL h2 (lay (n := n) A hA) N

theorem lay_zero : lay (h := h) (n := n) 0 (trace_zero _ _) = 1 := by
  refine Subtype.ext ?_
  rw [lay_val, layMat]
  ext a b
  simp

theorem PL.zero (N : ℕ) : PL h2 n 0 N := ⟨trace_zero _ _, by rw [lay_zero]; exact WL.one.mono (Nat.zero_le _)⟩

theorem PL.add {A B : Matrix (Fin h) (Fin h) (ZMod 2)} {N M : ℕ} (hA : PL h2 n A N) (hB : PL h2 n B M) :
    PL h2 n (A + B) (N + M) := by
  obtain ⟨a1, a2⟩ := hA
  obtain ⟨b1, b2⟩ := hB
  exact ⟨by rw [trace_add, a1, b1, add_zero], by rw [← lay_mul A B a1 b1]; exact a2.mul b2⟩

theorem PL.sum {ι : Type*} (S : Finset ι) (M : ι → Matrix (Fin h) (Fin h) (ZMod 2)) (N : ℕ)
    (hM : ∀ p ∈ S, PL h2 n (M p) N) : PL h2 n (∑ p ∈ S, M p) (S.card * N) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PL.zero (h2 := h2) (n := n) 0
  | insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.card_insert_of_notMem hp]
    have h1 := (hM p (mem_insert_self _ _)).add (ih fun q hq => hM q (mem_insert_of_mem hq))
    rwa [show (S.card + 1) * N = N + S.card * N by ring]

/-- The bound for one elementary matrix of the layer. -/
def bQ (h n : ℕ) : ℕ := 4 ^ (h + 3) * (9 * (n + 2) ^ 3) * (n + 1) ^ 3

theorem WL.el_layer (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij (s (n + 2) ^ (n + 1)) : G h (n + 1)) (bQ h n) :=
  WL.el_pow h3 (fun i j hij => WL.el_s h3 i j hij) (n + 1) (by omega) i j hij

theorem lay_single (i j : Fin h) (hij : i ≠ j) (htr : (Matrix.single i j (1 : ZMod 2)).trace = 0) :
    lay (n := n) (Matrix.single i j 1) htr = El i j hij (s (n + 2) ^ (n + 1)) := by
  refine Subtype.ext ?_
  rw [lay_val, layMat, El_val, transvection]
  congr 1
  ext a b
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs
  · rw [map_one, mul_one]
  · rw [map_zero, mul_zero]

theorem trace_single_ne (i j : Fin h) (hij : i ≠ j) : (Matrix.single i j (1 : ZMod 2)).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.diag_apply, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij rfl

theorem PL.single (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) : PL h2 n (Matrix.single i j 1) (bQ h n) :=
  ⟨trace_single_ne i j hij, by rw [lay_single i j hij]; exact WL.el_layer h3 i j hij⟩

theorem trace_diag (i : Fin h) : (Matrix.single i i (1 : ZMod 2) + Matrix.single 0 0 1).trace = 0 := by
  rw [trace_add, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same]
  rfl

/-- The diagonal elements of the layer. -/
theorem lay_diag (i : Fin h) (hi : i ≠ 0) :
    lay (n := n) (Matrix.single i i 1 + Matrix.single 0 0 1) (trace_diag i) =
      El 0 i hi.symm (s (n + 2) ^ (n + 1)) * El i 0 hi 1 *
        (El 0 i hi.symm (s (n + 2) ^ (n + 1)) * El i 0 hi 1) * El i 0 hi (s (n + 2) ^ (n + 1)) := by
  refine Subtype.ext ?_
  have hs : s (n + 2) ^ (n + 1) * s (n + 2) ^ (n + 1) = 0 := by rw [← sq, s_sq]
  set σ := s (n + 2) ^ (n + 1) with hσ
  simp only [Matrix.SpecialLinearGroup.coe_mul, El_val, transvection]
  have hl : layMat n (Matrix.single i i 1 + Matrix.single 0 0 1) =
      1 + (Matrix.single i i σ + Matrix.single 0 0 σ) := by
    rw [layMat, ← hσ]
    congr 1
    ext a b
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply, Matrix.single_apply, Matrix.single_apply, smul_eq_mul, map_add, mul_add]
    congr 1
    · split_ifs
      · rw [map_one, mul_one]
      · rw [map_zero, mul_zero]
    · split_ifs
      · rw [map_one, mul_one]
      · rw [map_zero, mul_zero]
  rw [lay_val, hl]
  set a := Matrix.single (0 : Fin h) i σ with ha
  set b := Matrix.single i (0 : Fin h) (1 : R (n + 2)) with hb
  set c := Matrix.single i (0 : Fin h) σ with hc
  have haa : a * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi _
  have hbb : b * b = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi.symm _
  have hab : a * b = Matrix.single 0 0 σ := by rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have hba : b * a = Matrix.single i i σ := by rw [ha, hb, Matrix.single_mul_single_same, one_mul]
  have hbab : b * a * b = c := by rw [hba, hb, hc, Matrix.single_mul_single_same, mul_one]
  have haba : a * b * a = 0 := by rw [hab, ha, Matrix.single_mul_single_same, hs, Matrix.single_zero]
  have hac : a * c = 0 := by rw [ha, hc, Matrix.single_mul_single_same, hs, Matrix.single_zero]
  have hbc : b * c = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi.symm _
  have hcc : c * c = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi.symm _
  rw [← hab, ← hba]
  have e2 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + (b * a + c + a * b) := by
    have e3 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + ((a + b + a * b) + (a + b + a * b)) + (b * a + b * a * b +
      a * b) + (a * a + a * a * b + b * b + a * b * a + a * b * a * b + a * (b * b)) := by
      noncomm_ring
    rw [e3, two_nsmul_mat, haa, hbb, haba, hbab]
    simp
  have e4 : (1 + (b * a + c + a * b)) * (1 + c) = 1 + (b * a + a * b) + (c + c) +
      (b * (a * c) + c * c + a * (b * c)) := by noncomm_ring
  rw [e2, e4, two_nsmul_mat, hac, hcc, hbc]
  simp

theorem PL.diag (h3 : 3 ≤ h) (i : Fin h) : PL h2 n (Matrix.single i i 1 + Matrix.single 0 0 1) (5 * bQ h n) := by
  by_cases hi : i = 0
  · subst hi
    have : (Matrix.single 0 0 1 + Matrix.single 0 0 1 : Matrix (Fin h) (Fin h) (ZMod 2)) = 0 := by
      rw [← Matrix.single_add]
      exact Matrix.single_zero _ _
    rw [this]
    exact PL.zero _
  · refine ⟨trace_diag i, ?_⟩
    rw [lay_diag i hi]
    have p1 := WL.el_layer (n := n) (h2 := h2) h3 0 i (Ne.symm hi)
    have p2 := WL.el_one (n := n + 1) (h2 := h2) h3 i 0 hi
    have p3 := WL.el_layer (n := n) (h2 := h2) h3 i 0 hi
    refine (((p1.mul p2).mul (p1.mul p2)).mul p3).mono ?_
    have h4 : 4 ^ (h + 3) * (2 * (n + 1 + 1)) ^ 3 ≤ bQ h n := by
      unfold bQ
      have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      calc 4 ^ (h + 3) * (2 * (n + 1 + 1)) ^ 3 = 4 ^ (h + 3) * (8 * (n + 2) ^ 3) * 1 := by ring
        _ ≤ 4 ^ (h + 3) * (9 * (n + 2) ^ 3) * (n + 1) ^ 3 := by gcongr; omega
    omega

/-- The layer: a matrix as a sum of elementary ones. -/
theorem sum_layer (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) :
    ∑ p : Fin h × Fin h, A p.1 p.2 • (if p.1 = p.2 then Matrix.single p.1 p.1 1 + Matrix.single 0 0 1
      else Matrix.single p.1 p.2 1 : Matrix (Fin h) (Fin h) (ZMod 2)) = A := by
  ext a b
  rw [Matrix.sum_apply]
  have h1 : ∀ p : Fin h × Fin h, (A p.1 p.2 • (if p.1 = p.2 then Matrix.single p.1 p.1 1 + Matrix.single 0 0 1
      else Matrix.single p.1 p.2 1 : Matrix (Fin h) (Fin h) (ZMod 2))) a b =
      (if p = (a, b) then A p.1 p.2 else 0) + (if p.1 = p.2 then (if 0 = a ∧ 0 = b then A p.1 p.2 else 0) else 0) := by
    rintro ⟨i, j⟩
    simp only [Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, mul_add]
      congr 1
      · split_ifs <;> simp
      · split_ifs <;> simp
    · rw [if_neg hij, if_neg hij, Matrix.single_apply, add_zero]
      split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_add_distrib, Finset.sum_ite_eq' univ (a, b), if_pos (mem_univ _)]
  have h3 : (∑ p : Fin h × Fin h, if p.1 = p.2 then (if 0 = a ∧ 0 = b then A p.1 p.2 else 0) else 0) = 0 := by
    rw [Fintype.sum_prod_type]
    by_cases hab : 0 = a ∧ 0 = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [and_self, if_true, Finset.sum_ite_eq, mem_univ]
      exact hA
    · simp [hab]
  rw [h3, add_zero]

theorem PL.all (h3 : 3 ≤ h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) :
    PL h2 n A (h * h * (5 * bQ h n)) := by
  have h4 := PL.sum (h2 := h2) (n := n) (univ : Finset (Fin h × Fin h)) (fun p => A p.1 p.2 •
    (if p.1 = p.2 then Matrix.single p.1 p.1 1 + Matrix.single 0 0 1 else Matrix.single p.1 p.2 1)) (5 * bQ h n) (by
    rintro ⟨i, j⟩ -
    simp only
    have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases key (A i j) with h0 | h1
    · rw [h0, zero_smul]
      exact PL.zero _
    · rw [h1, one_smul]
      split_ifs with hij
      · exact PL.diag h3 i
      · obtain ⟨a1, a2⟩ := PL.single (h2 := h2) (n := n) h3 i j hij
        exact ⟨a1, a2.mono (by omega)⟩)
  rw [sum_layer A hA] at h4
  simpa using h4

theorem red_tt (k : Fin h) : red (n + 1) (tt (n + 1) k) = tt n k := by
  rw [tt, tt]
  split_ifs
  · exact red_t _
  · exact map_one _

theorem redG_gen (k : Fin h) : redG (gen h2 k : G h (n + 1)) = gen h2 k := by
  refine Subtype.ext ?_
  ext a b
  rw [redG_apply, gen_val, gen_val, transvection, transvection, Matrix.add_apply, Matrix.add_apply, map_add,
    Matrix.single_apply, Matrix.single_apply]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, map_zero]
  · split_ifs
    · exact red_tt k
    · exact map_zero _

/-- From level n to level n + 1. -/
theorem WL.lift (h3 : 3 ≤ h) {N : ℕ} (hN : ∀ g : G h n, WL h2 g N) (g : G h (n + 1)) :
    WL h2 g (N + h * h * (5 * bQ h n)) := by
  obtain ⟨l, h1, h4⟩ := hN (redG g)
  have h5 : redG ((l.map (Nc.Tower.gen h2)).prod : G h (n + 1)) = redG g := by
    rw [map_list_prod, List.map_map, ← h4]
    congr 1
    exact List.map_congr_left fun k _ => redG_gen k
  have h6 : redG (((l.map (Nc.Tower.gen h2)).prod : G h (n + 1))⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, h5, inv_mul_cancel]
  obtain ⟨A, hA, h7⟩ := exists_lay h6
  obtain ⟨hA', h8⟩ := PL.all (h2 := h2) (n := n) h3 A hA
  have h9 : g = (l.map (Nc.Tower.gen h2)).prod * lay A hA := by rw [← h7, mul_inv_cancel_left]
  rw [h9]
  exact (show WL h2 ((l.map (Nc.Tower.gen h2)).prod : G h (n + 1)) N from ⟨l, h1, rfl⟩).mul h8

end Nc.Tower
