/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Uni

/-!
# Elements `1 + uφᵀ` of the unitriangular group are short words
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

variable {n : ℕ}

/-- The total length of the generators. -/
noncomputable def Len.S (l : Len (U n)) : ℝ := ∑ j : Fin (n - 1), l.val (x n j)

theorem Len.S_nonneg (l : Len (U n)) : 0 ≤ l.S := sum_nonneg fun _ _ => l.nonneg _

theorem Len.x_le_S (l : Len (U n)) (j : Fin (n - 1)) : l.val (x n j) ≤ l.S :=
  single_le_sum (f := fun j => l.val (x n j)) (fun _ _ => l.nonneg _) (mem_univ j)

theorem x_mul_apply (j : Fin (n - 1)) (A : U n) (i k : Fin n) :
    mat (x n j * A) i k = mat A i k + if i = lo j then mat A (hi j) k else 0 := by
  rw [mat_mul, mat_x, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  congr 1
  by_cases h : i = lo j
  · subst h
    simp
  · rw [if_neg h]
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h]

theorem mul_x_apply (j : Fin (n - 1)) (A : U n) (i k : Fin n) :
    mat (A * x n j) i k = mat A i k + if k = hi j then mat A i (lo j) else 0 := by
  rw [mat_mul, mat_x, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases h : k = hi j
  · subst h
    simp
  · rw [if_neg h]
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h]

theorem f2_add_self (a : F2) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem lo_ne_hi' (j : Fin (n - 1)) : hi j ≠ lo j := (Nc.Tower.lo_ne_hi j).symm

theorem x_mul_x (j : Fin (n - 1)) : x n j * x n j = 1 := by
  apply mat_inj
  ext i k
  rw [x_mul_apply, mat_x, mat_one]
  by_cases h : i = lo j
  · subst h
    simp only [Matrix.add_apply, if_true, Matrix.single_apply]
    by_cases h2 : hi j = k
    · subst h2
      simp [lo_ne_hi', f2_add_self, (lo_ne_hi' j).symm]
    · simp [h2, (lo_ne_hi' j).symm, Matrix.one_apply]
  · simp [h, Matrix.single_apply, Ne.symm h]

/-- The sum of the lengths of the generators of types ≥ p. -/
noncomputable def Len.T (l : Len (U n)) (p : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin (n - 1) => p ≤ j.1), l.val (x n j)

theorem Len.T_zero (l : Len (U n)) : l.T 0 = l.S := by
  simp [Len.T, Len.S]

theorem Len.T_succ (l : Len (U n)) (j : Fin (n - 1)) : l.T j.1 = l.T (j.1 + 1) + l.val (x n j) := by
  unfold Len.T
  have : univ.filter (fun i : Fin (n - 1) => j.1 ≤ i.1) =
      insert j (univ.filter fun i : Fin (n - 1) => j.1 + 1 ≤ i.1) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp), add_comm]

theorem exists_col_aux (l : Len (U n)) (a : Fin n) (k : ℕ) : ∀ p : ℕ, p + k = a.1 →
    ∀ u : Fin n → F2, u a = 1 → (∀ i, a < i → u i = 0) → (∀ i : Fin n, i.1 < p → u i = 0) →
    ∃ c d : U n, (∀ i j : Fin n, (i.1 < p ∨ a ≤ i) → mat c i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ i j : Fin n, (i.1 < p ∨ a ≤ i) → mat d i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ i : Fin n, mat d i a = if p ≤ i.1 ∧ i ≤ a then 1 else 0) ∧
      (∀ i, mat (c * d) i a = u i) ∧ l.val c ≤ l.T p ∧ l.val d ≤ l.T p := by
  induction k with
  | zero =>
    intro p hp u hua hu1 hu2
    have hT : 0 ≤ l.T p := sum_nonneg fun _ _ => l.nonneg _
    refine ⟨1, 1, fun _ _ _ => rfl, fun _ _ _ => rfl, fun i => ?_, fun i => ?_, ?_, ?_⟩
    · rw [mat_one, Matrix.one_apply]
      by_cases h : i = a
      · subst h
        simp; omega
      · rw [if_neg h, if_neg]
        rintro ⟨h1, h2⟩
        exact h (le_antisymm h2 (Fin.le_def.2 (by omega)))
    · rw [mul_one, mat_one, Matrix.one_apply]
      rcases lt_trichotomy i a with h | h | h
      · rw [if_neg h.ne, hu2 i (by rw [Fin.lt_def] at h; omega)]
      · subst h
        rw [if_pos rfl, hua]
      · rw [if_neg h.ne', hu1 i h]
    · rw [l.one']; exact hT
    · rw [l.one']; exact hT
  | succ k ih =>
    intro p hp u hua hu1 hu2
    have hpa : p < a.1 := by omega
    have hpn : p < n - 1 := by have := a.2; omega
    set j : Fin (n - 1) := ⟨p, hpn⟩ with hj
    have hlo : (lo j).1 = p := rfl
    have hhi : (hi j).1 = p + 1 := rfl
    have hloa : lo j ≠ a := by
      intro h
      rw [← h, hlo] at hpa
      omega
    obtain ⟨c, d, hc, hd, hda, hcd, hlc, hld⟩ := ih (p + 1) (by omega)
      (Function.update u (lo j) 0) (by rw [Function.update_of_ne hloa.symm, hua])
      (fun i hi => by
        rw [Function.update_of_ne, hu1 i hi]
        rintro rfl
        rw [Fin.lt_def, hlo] at hi
        omega)
      (fun i hi => by
        by_cases h : i = lo j
        · rw [h, Function.update_self]
        · rw [Function.update_of_ne h]
          apply hu2
          have : i.1 ≠ p := fun h2 => h (Fin.ext h2)
          omega)
    have hT : l.T p = l.T (p + 1) + l.val (x n j) := l.T_succ j
    have hx0 := l.nonneg (x n j)
    have hclo : ∀ i, mat c i (lo j) = (1 : Matrix _ _ F2) i (lo j) := by
      intro i
      by_cases hi : i.1 < p + 1
      · exact hc i _ (Or.inl hi)
      · have h1 : lo j < i := by rw [Fin.lt_def, hlo]; omega
        rw [mat_lt c h1, Matrix.one_apply_ne h1.ne']
    have hrow : ∀ i : Fin n, (i.1 < p ∨ a ≤ i) → i ≠ lo j := by
      rintro i hi rfl
      rw [Fin.le_def, hlo] at hi
      omega
    have hrow' : ∀ i : Fin n, (i.1 < p ∨ a ≤ i) → (i.1 < p + 1 ∨ a ≤ i) := by
      rintro i (h | h)
      · left; omega
      · right; exact h
    have hd' : ∀ i k : Fin n, (i.1 < p ∨ a ≤ i) → mat (x n j * d) i k = (1 : Matrix _ _ F2) i k := by
      intro i k hi
      rw [x_mul_apply, if_neg (hrow i hi), add_zero, hd i k (hrow' i hi)]
    have hda' : ∀ i : Fin n, mat (x n j * d) i a = if p ≤ i.1 ∧ i ≤ a then 1 else 0 := by
      intro i
      rw [x_mul_apply, hda, hda]
      by_cases h : i = lo j
      · subst h
        rw [if_neg (by rw [hlo]; omega), if_pos rfl, if_pos, if_pos, zero_add]
        · exact ⟨hlo.ge, Fin.le_def.2 (by omega)⟩
        · exact ⟨hhi.ge, Fin.le_def.2 (by omega)⟩
      · rw [if_neg h, add_zero]
        have : i.1 ≠ p := fun h2 => h (Fin.ext h2)
        congr 1
        apply propext
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    have hld' : l.val (x n j * d) ≤ l.T p := by
      have := l.mul' (x n j) d
      linarith
    by_cases hu : u (lo j) = 0
    · refine ⟨c * x n j, x n j * d, fun i k hi => ?_, hd', hda', fun i => ?_, ?_, hld'⟩
      · rw [mul_x_apply, hclo, Matrix.one_apply_ne (hrow i hi), ite_self, add_zero,
          hc i k (hrow' i hi)]
      · rw [mul_assoc, ← mul_assoc (x n j), x_mul_x, one_mul, hcd]
        by_cases h : i = lo j
        · rw [h, Function.update_self, hu]
        · rw [Function.update_of_ne h]
      · have := l.mul' c (x n j)
        linarith
    · have hu' : u (lo j) = 1 := by
        have : ∀ a : F2, a ≠ 0 → a = 1 := by decide
        exact this _ hu
      refine ⟨c, x n j * d, fun i k hi => hc i k (hrow' i hi), hd', hda', fun i => ?_, ?_, hld'⟩
      · have e : mat (c * (x n j * d)) i a = mat (c * d) i a + mat c i (lo j) * mat d (hi j) a := by
          rw [mat_mul c (x n j * d), mat_mul c d, Matrix.mul_apply, Matrix.mul_apply]
          simp only [x_mul_apply, mul_add, sum_add_distrib]
          simp
        rw [e, hcd, hclo, hda, if_pos ⟨hhi.ge, Fin.le_def.2 (by omega)⟩, mul_one]
        by_cases h : i = lo j
        · rw [h, Function.update_self, hu', Matrix.one_apply_eq, zero_add]
        · rw [Function.update_of_ne h, Matrix.one_apply_ne h, add_zero]
      · linarith

theorem exists_col (l : Len (U n)) (a : Fin n) (u : Fin n → F2) (hua : u a = 1)
    (hu : ∀ i, a < i → u i = 0) :
    ∃ g : U n, (∀ i j : Fin n, a ≤ i → mat g i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ i, mat g i a = u i) ∧ l.val g ≤ 2 * l.S := by
  obtain ⟨c, d, hc, hd, -, hcd, hlc, hld⟩ := exists_col_aux l a a.1 0 (by omega) u hua hu
    (fun i hi => absurd hi (by omega))
  refine ⟨c * d, fun i j hi => ?_, hcd, ?_⟩
  · rw [mat_mul, Matrix.mul_apply]
    simp only [hc i _ (Or.inr hi)]
    rw [← hd i j (Or.inr hi), ← Matrix.mul_apply, Matrix.one_mul]
  · rw [Len.T_zero] at hlc hld
    have := l.mul' c d
    linarith

/-- Reflection in the antidiagonal. -/
def refl (A : U n) : U n :=
  mk (Matrix.of fun i j => mat A (Fin.rev j) (Fin.rev i))
    (fun i j hij => mat_lt A (Fin.rev_lt_rev.2 hij)) (fun i => mat_diag A _)

theorem refl_apply (A : U n) (i j : Fin n) : mat (refl A) i j = mat A (Fin.rev j) (Fin.rev i) := rfl

theorem refl_mul (A B : U n) : refl (A * B) = refl B * refl A := by
  apply mat_inj
  ext i j
  rw [refl_apply, mat_mul, mat_mul, Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun k _ => ?_
  rw [refl_apply, refl_apply, mul_comm]
  rfl

theorem refl_one : refl (1 : U n) = 1 := by
  apply mat_inj
  ext i j
  rw [refl_apply, mat_one, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.rev_inj, eq_comm]

theorem refl_inv (A : U n) : refl A⁻¹ = (refl A)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← refl_mul, mul_inv_cancel, refl_one]

theorem refl_x (j : Fin (n - 1)) : refl (x n j) = x n (Fin.rev j) := by
  apply mat_inj
  ext i k
  rw [refl_apply, mat_x, mat_x, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.one_apply, Matrix.single_apply, Matrix.single_apply]
  have h1 : lo j = Fin.rev k ↔ hi (Fin.rev j) = k := by
    simp only [lo, hi, Fin.ext_iff, Fin.val_rev]
    have := j.2; have := k.2
    omega
  have h2 : hi j = Fin.rev i ↔ lo (Fin.rev j) = i := by
    simp only [lo, hi, Fin.ext_iff, Fin.val_rev]
    have := j.2; have := i.2
    omega
  simp only [Fin.rev_inj, h1, h2, eq_comm (a := k), and_comm]

/-- The reflected length. -/
def Len.refl (l : Len (U n)) : Len (U n) where
  val A := l.val (Nc.Flag.refl A)
  one' := by rw [refl_one, l.one']
  inv' g := by rw [refl_inv, l.inv']
  mul' g h := by
    rw [refl_mul, add_comm]
    exact l.mul' _ _

theorem Len.refl_S (l : Len (U n)) : l.refl.S = l.S := by
  unfold Len.S
  rw [← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun j _ => ?_
  show l.val (Nc.Flag.refl _) = _
  rw [refl_x]
  simp

theorem exists_row (l : Len (U n)) (b : Fin n) (φ : Fin n → F2) (hb : φ b = 1)
    (hφ : ∀ i, i < b → φ i = 0) :
    ∃ g : U n, (∀ i j : Fin n, j ≤ b → mat g i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ j, mat g b j = φ j) ∧ l.val g ≤ 2 * l.S := by
  obtain ⟨g, h1, h2, h3⟩ := exists_col l.refl (Fin.rev b) (fun i => φ (Fin.rev i))
    (by simpa using hb) (fun i hi => hφ _ (by rw [← Fin.rev_lt_rev, Fin.rev_rev]; exact hi))
  refine ⟨refl g, fun i j hj => ?_, fun j => ?_, ?_⟩
  · rw [refl_apply, h1 _ _ (Fin.rev_le_rev.2 hj), Matrix.one_apply, Matrix.one_apply]
    simp [Fin.rev_inj, eq_comm]
  · rw [refl_apply, h2]
    simp
  · rw [Len.refl_S] at h3
    exact h3

theorem lead_le (l : Len (U n)) (j : Fin (n - 1)) (u φ : Fin n → F2) (hu1 : u (lo j) = 1)
    (hu : ∀ i, lo j < i → u i = 0) (hφ1 : φ (hi j) = 1) (hφ : ∀ i, i < hi j → φ i = 0)
    (A : U n) (hA : mat A = 1 + Matrix.vecMulVec u φ) : l.val A ≤ 9 * l.S := by
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_col l (lo j) u hu1 hu
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_row l (hi j) φ hφ1 hφ
  set Y : U n := k⁻¹ * x n j * k with hY
  have hlt := Nc.Tower.lo_lt_hi j
  have hkY : mat (k * Y) = mat k * (1 + Matrix.vecMulVec (Pi.single (lo j) 1) φ) := by
    have : k * Y = x n j * k := by rw [hY]; group
    rw [this]
    ext i m
    rw [x_mul_apply, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hk2, Matrix.mul_apply]
    congr 1
    simp only [Matrix.vecMulVec_apply]
    rw [sum_eq_single (lo j)]
    · rw [hk1 _ _ hlt.le, Matrix.one_apply, Pi.single_eq_same, one_mul]
      split_ifs <;> simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      simp
    · simp
  have hYm : mat Y = 1 + Matrix.vecMulVec (Pi.single (lo j) 1) φ := by
    have h1 : mat k⁻¹ * mat k = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
    rw [mat_mul] at hkY
    calc mat Y = mat k⁻¹ * mat k * mat Y := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hkY, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hAg : A * g = g * Y := by
    apply mat_inj
    rw [mat_mul, mat_mul, hA, hYm, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext i m
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply]
    have h1 : ∀ c, u i * φ c * mat g c m = u i * φ c * (1 : Matrix (Fin n) (Fin n) F2) c m := by
      intro c
      by_cases hc : c < hi j
      · rw [hφ c hc]; simp
      · rw [hg1 c m (hlt.le.trans (not_lt.1 hc))]
    rw [sum_congr rfl fun c _ => h1 c, sum_eq_single m, sum_eq_single (lo j)]
    · rw [hg2, Pi.single_eq_same, Matrix.one_apply_eq]
      ring
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      simp
    · simp
    · intro c _ hc
      rw [Matrix.one_apply_ne hc, mul_zero]
    · simp
  have hA2 : A = g * Y * g⁻¹ := by rw [← hAg]; group
  have h1 := l.conj g Y
  rw [← hA2] at h1
  have h2 := l.conj k⁻¹ (x n j)
  rw [inv_inv, ← hY, l.inv'] at h2
  have h3 := l.x_le_S j
  linarith

end Nc.Flag
