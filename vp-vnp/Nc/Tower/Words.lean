/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Layer

/-!
# Short words

Every element of the group is a product of at most C (n + 1)^7 generators.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

/-- The last index. -/
def last (h : ℕ) [NeZero h] : Fin h := ⟨h - 1, Nat.sub_lt (NeZero.pos h) Nat.one_pos⟩

variable {h n : ℕ} [NeZero h] (h2 : 2 ≤ h)

/-- The element is a product of at most N generators. -/
def WL (g : G h n) (N : ℕ) : Prop := ∃ l : List (Fin h), l.length ≤ N ∧ (l.map (gen h2)).prod = g

variable {h2}

theorem WL.mono {g : G h n} {N M : ℕ} (hg : WL h2 g N) (hM : N ≤ M) : WL h2 g M := by
  obtain ⟨l, h1, h3⟩ := hg
  exact ⟨l, h1.trans hM, h3⟩

theorem WL.one : WL h2 (1 : G h n) 0 := ⟨[], le_rfl, rfl⟩

theorem WL.gen (k : Fin h) : WL h2 (gen h2 k : G h n) 1 := ⟨[k], le_rfl, by simp⟩

theorem WL.mul {g g' : G h n} {N M : ℕ} (hg : WL h2 g N) (hg' : WL h2 g' M) : WL h2 (g * g') (N + M) := by
  obtain ⟨l, h1, rfl⟩ := hg
  obtain ⟨l', h3, rfl⟩ := hg'
  exact ⟨l ++ l', by simp; omega, by simp⟩

/-- Elementary matrices. -/
noncomputable def El (i j : Fin h) (hij : i ≠ j) (y : R (n + 1)) : G h n :=
  ⟨transvection i j y, det_transvection_of_ne _ _ hij y⟩

theorem El_val (i j : Fin h) (hij : i ≠ j) (y : R (n + 1)) : (El i j hij y).1 = transvection i j y := rfl

theorem El_add (i j : Fin h) (hij : i ≠ j) (y y' : R (n + 1)) :
    El i j hij y * El i j hij y' = El i j hij (y + y') :=
  Subtype.ext (transvection_mul_transvection_same _ _ hij y y')

theorem two_nsmul_mat (M : Matrix (Fin h) (Fin h) (R (n + 1))) : M + M = 0 := by
  ext a b
  exact add_self _ _

/-- The commutator. -/
theorem El_comm (i j k : Fin h) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (y y' : R (n + 1)) :
    El i k hik y * El k j hkj y' * (El i k hik y * El k j hkj y') = El i j hij (y * y') := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, El_val, transvection]
  set a := Matrix.single i k y with ha
  set b := Matrix.single k j y' with hb
  have haa : a * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hik.symm _
  have hbb : b * b = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm _
  have hba : b * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
  have hab : a * b = Matrix.single i j (y * y') := Matrix.single_mul_single_same _ _ _ _ _
  rw [← hab]
  have e1 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + a * b + ((a + b + a * b) + (a + b + a * b)) +
      (a * a + a * a * b + b * a + b * b + b * a * b + a * (b * a) + a * (b * b) + a * (b * a) * b) := by
    noncomm_ring
  rw [e1, two_nsmul_mat, haa, hba, hbb]
  simp

theorem WL.comm {i j k : Fin h} {hik : i ≠ k} {hkj : k ≠ j} (hij : i ≠ j) {y y' : R (n + 1)} {N M : ℕ}
    (h1 : WL h2 (El i k hik y) N) (h3 : WL h2 (El k j hkj y') M) : WL h2 (El i j hij (y * y')) (2 * (N + M)) := by
  rw [← El_comm i j k hik hkj hij]
  exact ((h1.mul h3).mul (h1.mul h3)).mono (by omega)

theorem gen_eq_El (k : Fin h) : (gen h2 k : G h n) = El (k - 1) k (sub_one_ne h2 k) (tt n k) := rfl

/-- Constant elementary matrices above the diagonal. -/
theorem WL.upper (d : ℕ) (i j : Fin h) (hij : i ≠ j) (hd : i.1 + (d + 1) = j.1) :
    WL h2 (El i j hij 1 : G h n) (4 ^ d) := by
  induction d generalizing j with
  | zero =>
    have hj : j ≠ 0 := by
      intro e
      rw [e] at hd
      simp at hd
    have h1 : j - 1 = i := by
      refine Fin.ext ?_
      have h3 : (1 : Fin h) ≤ j := by
        rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
        omega
      rw [Fin.sub_val_of_le h3, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
      omega
    have h3 := WL.gen (n := n) (h2 := h2) j
    rw [gen_eq_El, tt, if_neg hj] at h3
    subst h1
    exact h3
  | succ d ih =>
    let k : Fin h := ⟨j.1 - 1, by omega⟩
    have hk : k.1 = j.1 - 1 := rfl
    have hik : i ≠ k := by
      intro e
      have := congrArg Fin.val e
      omega
    have hkj : k ≠ j := by
      intro e
      have := congrArg Fin.val e
      omega
    have h1 := ih k hik (by omega)
    have h3 : WL h2 (El k j hkj 1 : G h n) 1 := by
      have hj : j ≠ 0 := by
        intro e
        rw [e] at hd
        simp at hd
      have h4 : j - 1 = k := by
        refine Fin.ext ?_
        have h5 : (1 : Fin h) ≤ j := by
          rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
          omega
        rw [Fin.sub_val_of_le h5, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
      have h6 := WL.gen (n := n) (h2 := h2) j
      rw [gen_eq_El, tt, if_neg hj] at h6
      have h7 : (El (j - 1) j (sub_one_ne h2 j) 1 : G h n) = El k j hkj 1 := by
        refine Subtype.ext ?_
        rw [El_val, El_val, h4]
      rwa [h7] at h6
    have h4 := h1.comm hij h3
    rw [one_mul] at h4
    refine h4.mono ?_
    have : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    omega

theorem WL.upper' (i j : Fin h) (hij : i < j) : WL h2 (El i j hij.ne 1 : G h n) (4 ^ h) := by
  have hlt := Fin.lt_def.1 hij
  refine (WL.upper (j.1 - i.1 - 1) i j hij.ne (by omega)).mono (Nat.pow_le_pow_right (by omega) ?_)
  have := j.2
  omega

theorem zero_sub_one (h2 : 2 ≤ h) : (0 : Fin h) - 1 = last h := by
  refine Fin.ext ?_
  rw [zero_sub, Fin.val_neg', Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

theorem lt_last {i : Fin h} (hi : i ≠ last h) : i < last h := by
  rw [Fin.lt_def]
  have h1 := i.2
  have h3 : i.1 ≠ h - 1 := fun e => hi (Fin.ext e)
  simp only [last]
  omega

theorem zero_ne_last (h2 : 2 ≤ h) : last h ≠ 0 := by
  intro e
  have := congrArg Fin.val e
  simp [last] at this
  omega

theorem exists_third (h3 : 3 ≤ h) (i j : Fin h) : ∃ k, i ≠ k ∧ k ≠ j := by
  by_contra hc
  push Not at hc
  have h1 : (univ : Finset (Fin h)) ⊆ {i, j} := by
    intro k _
    by_cases e : i = k
    · simp [e]
    · simp [hc k e]
  have h4 := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fin] at h4
  have h5 : ({i, j} : Finset (Fin h)).card ≤ 2 := Finset.card_le_two
  omega

/-- All elementary matrices with entry t. -/
theorem WL.el_t (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij (t (n + 1)) : G h n) (4 ^ (h + 3)) := by
  have hp : 1 ≤ 4 ^ h := Nat.one_le_pow _ _ (by omega)
  have e1 : 4 ^ (h + 1) = 4 * 4 ^ h := by ring
  have e2 : 4 ^ (h + 2) = 16 * 4 ^ h := by ring
  have e3 : 4 ^ (h + 3) = 64 * 4 ^ h := by ring
  have hL0 := zero_ne_last (h := h) h2
  have c1 : WL h2 (El (last h) 0 hL0 (t (n + 1)) : G h n) 1 := by
    have h6 := WL.gen (n := n) (h2 := h2) 0
    rw [gen_eq_El, tt, if_pos rfl] at h6
    have h7 : (El (0 - 1) 0 (sub_one_ne h2 0) (t (n + 1)) : G h n) = El (last h) 0 hL0 (t (n + 1)) := by
      refine Subtype.ext ?_
      rw [El_val, El_val, zero_sub_one h2]
    rwa [h7] at h6
  have c2 : ∀ j (hj : last h ≠ j), WL h2 (El (last h) j hj (t (n + 1)) : G h n) (4 ^ (h + 1)) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      exact c1.mono (by omega)
    · have h4 := c1.comm hj (WL.upper' (n := n) (h2 := h2) 0 j (Fin.pos_iff_ne_zero.2 h0))
      rw [mul_one] at h4
      exact h4.mono (by omega)
  have c3 : ∀ i j (hij : i ≠ j), i ≠ last h → j ≠ last h → WL h2 (El i j hij (t (n + 1)) : G h n) (4 ^ (h + 2)) := by
    intro i j hij hi hj
    have h4 := (WL.upper' (n := n) (h2 := h2) i (last h) (lt_last hi)).comm hij (c2 j hj.symm)
    rw [one_mul] at h4
    exact h4.mono (by omega)
  by_cases hi : i = last h
  · subst hi
    exact (c2 j hij).mono (by omega)
  · by_cases hj : j = last h
    · subst hj
      obtain ⟨k, hk1, hk2⟩ := exists_third h3 i (last h)
      have h4 := (c3 i k hk1 hi hk2).comm hij (WL.upper' (n := n) (h2 := h2) k (last h) (lt_last hk2))
      rw [mul_one] at h4
      exact h4.mono (by omega)
    · exact (c3 i j hij hi hj).mono (by omega)

/-- Powers of the entry. -/
theorem WL.el_pow (h3 : 3 ≤ h) {y : R (n + 1)} {B : ℕ} (hy : ∀ i j (hij : i ≠ j), WL h2 (El i j hij y : G h n) B)
    (m : ℕ) (hm : 1 ≤ m) (i j : Fin h) (hij : i ≠ j) : WL h2 (El i j hij (y ^ m) : G h n) (B * m ^ 3) := by
  induction m using Nat.strong_induction_on generalizing i j with
  | _ m ih =>
    rcases Nat.eq_or_lt_of_le hm with h1 | h1
    · subst h1
      simpa using hy i j hij
    · obtain ⟨k, hk1, hk2⟩ := exists_third h3 i j
      have hab : m / 2 + (m - m / 2) = m := by omega
      have p1 := ih (m / 2) (by omega) (by omega) i k hk1
      have p2 := ih (m - m / 2) (by omega) (by omega) k j hk2
      have p3 := p1.comm hij p2
      rw [← pow_add, hab] at p3
      refine p3.mono ?_
      generalize ha : m / 2 = a at *
      generalize hb : m - a = b at *
      have hab2 : b = a ∨ b = a + 1 := by omega
      rw [← hab]
      have : 2 * (a ^ 3 + b ^ 3) ≤ (a + b) ^ 3 := by
        have ha1 : 1 ≤ a := by omega
        rcases hab2 with rfl | rfl
        · ring_nf; omega
        · nlinarith [Nat.pow_le_pow_left ha1 2, Nat.pow_le_pow_left ha1 3]
      calc 2 * (B * a ^ 3 + B * b ^ 3) = B * (2 * (a ^ 3 + b ^ 3)) := by ring
        _ ≤ B * (a + b) ^ 3 := Nat.mul_le_mul_left _ this

theorem one_add_pow_two_pow (m : ℕ) (y : R m) (e : ℕ) : (1 + y) ^ 2 ^ e = 1 + y ^ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_mul, ih, pow_mul]
    have h2 := two_eq_zero m
    linear_combination (y ^ 2 ^ e) * h2

/-- All elementary matrices with entry 1. -/
theorem WL.el_one (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij 1 : G h n) (4 ^ (h + 3) * (2 * (n + 1)) ^ 3) := by
  obtain ⟨e, he1, he2⟩ : ∃ e, n + 1 ≤ 2 ^ e ∧ 2 ^ e ≤ 2 * (n + 1) := by
    refine ⟨Nat.clog 2 (n + 1), Nat.le_pow_clog (by omega) _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by omega) (show 1 < n + 1 by omega)
      have hc : 0 < Nat.clog 2 (n + 1) := Nat.clog_pos (by omega) (by omega)
      obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_lt hc
      rw [hc'] at this ⊢
      simp only [zero_add, Nat.pred_succ] at this ⊢
      rw [pow_succ]
      omega
  have h1 : t (n + 1) ^ 2 ^ e = 1 := by
    rw [t, one_add_pow_two_pow, s_pow_ge he1, add_zero]
  have h4 := WL.el_pow (n := n) (h2 := h2) h3 (fun i j hij => WL.el_t h3 i j hij) (2 ^ e)
    (Nat.one_le_pow _ _ (by omega)) i j hij
  rw [h1] at h4
  exact h4.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he2 3))

/-- All elementary matrices with entry s. -/
theorem WL.el_s (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij (s (n + 1)) : G h n) (4 ^ (h + 3) * (9 * (n + 1) ^ 3)) := by
  have h1 := (WL.el_one (n := n) (h2 := h2) h3 i j hij).mul (WL.el_t h3 i j hij)
  rw [El_add, ← s_eq] at h1
  refine h1.mono ?_
  have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  calc 4 ^ (h + 3) * (2 * (n + 1)) ^ 3 + 4 ^ (h + 3) = 4 ^ (h + 3) * (8 * (n + 1) ^ 3 + 1) := by ring
    _ ≤ 4 ^ (h + 3) * (9 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ (by omega)

end Nc.Tower
