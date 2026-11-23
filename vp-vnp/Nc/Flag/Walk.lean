/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Block
import Nc.Flag.Words

/-!
# Lengths on U n: quotients and the two diagonal blocks
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

theorem three_le {T : Type*} [Fintype T] (c f g k : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hf : ∀ t, 0 ≤ f t)
    (hg : ∀ t, 0 ≤ g t) (hk : ∀ t, 0 ≤ k t) (h : ∀ t, c t ≤ f t + (g t + k t)) :
    √(∑ t, c t ^ 2) ≤ √(∑ t, f t ^ 2) + (√(∑ t, g t ^ 2) + √(∑ t, k t ^ 2)) := by
  have h1 := sqrt_sum_le univ f (fun t => g t + k t) c hf (fun t => add_nonneg (hg t) (hk t)) hc h
  have h2 := sqrt_sum_le univ g k (fun t => g t + k t) hg hk
    (fun t => add_nonneg (hg t) (hk t)) fun t => le_rfl
  linarith

/-- Pull-back of a length along a homomorphism. -/
def Len.comap {G H : Type*} [Group G] [Group H] (l : Len H) (φ : G →* H) : Len G where
  val g := l.val (φ g)
  one' := by rw [map_one, l.one']
  inv' g := by rw [map_inv, l.inv']
  mul' g h := by rw [map_mul]; exact l.mul' _ _

theorem Contr.comap {G H : Type*} [Group G] [Group H] {l : Len H} {m : ℕ} {s : ℝ}
    (h : Contr l m s) (φ : G →* H) : Contr (l.comap φ) m s := by
  intro τ hτ i
  exact h (fun M => φ (τ M)) (fun M N => by rw [hτ, map_mul]) i

/-- The root mean square of a length. -/
noncomputable def Len.rms {G : Type*} [Group G] [Fintype G] (l : Len G) : ℝ :=
  √((∑ g : G, l.val g ^ 2) / Fintype.card G)

theorem Len.rms_nonneg {G : Type*} [Group G] [Fintype G] (l : Len G) : 0 ≤ l.rms :=
  Real.sqrt_nonneg _

theorem Len.rms_sq {G : Type*} [Group G] [Fintype G] (l : Len G) :
    l.rms ^ 2 = (∑ g : G, l.val g ^ 2) / Fintype.card G :=
  Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))

/-- The mean square along a surjective homomorphism. -/
theorem Len.rms_comap {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] (l : Len H)
    (φ : G →* H) (hφ : Function.Surjective φ) : (l.comap φ).rms = l.rms := by
  classical
  unfold Len.rms
  congr 1
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  rw [div_eq_div_iff hG.ne' hH.ne']
  have h1 : ∑ h : H, ∑ g : G, l.val (h * φ g) ^ 2 = Fintype.card G * ∑ h : H, l.val h ^ 2 := by
    rw [sum_comm]
    have e : ∀ g, ∑ h : H, l.val (h * φ g) ^ 2 = ∑ h : H, l.val h ^ 2 := fun g =>
      Equiv.sum_comp (Equiv.mulRight (φ g)) (fun h => l.val h ^ 2)
    rw [sum_congr rfl fun g _ => e g]
    simp
  have h2 : ∑ h : H, ∑ g : G, l.val (h * φ g) ^ 2 = Fintype.card H * ∑ g : G, l.val (φ g) ^ 2 := by
    have : ∀ h : H, ∑ g : G, l.val (h * φ g) ^ 2 = ∑ g : G, l.val (φ g) ^ 2 := by
      intro h
      obtain ⟨k, rfl⟩ := hφ h
      rw [← Equiv.sum_comp (Equiv.mulLeft k) (fun g => l.val (φ g) ^ 2)]
      exact sum_congr rfl fun g _ => by rw [Equiv.coe_mulLeft, map_mul]
    rw [sum_congr rfl fun h _ => this h]
    simp
  show (∑ g : G, l.val (φ g) ^ 2) * _ = _
  linarith

/-- The bound of Lemma lem:first for one n with the constant κ. -/
def Bd (m : ℕ) (s : ℝ) (n : ℕ) (κ : ℝ) : Prop :=
  ∀ l : Len (U n), Contr l m s → l.rms ≤ κ * l.S

theorem bd_one (m : ℕ) (s : ℝ) : Bd m s 1 0 := by
  intro l _
  have : ∀ g : U 1, g = 1 := by
    intro g
    apply mat_inj
    ext i j
    rw [Subsingleton.elim i j, mat_diag, mat_one, Matrix.one_apply_eq]
  have h : ∑ g : U 1, l.val g ^ 2 = 0 := sum_eq_zero fun g _ => by rw [this g, l.one']; simp
  rw [Len.rms, h]
  simp

theorem S_add_le {a b : ℕ} (l : Len (U (a + b))) :
    (l.comap (win (hl (a := a) (b := b)))).S + (l.comap (win (hr (a := a) (b := b)))).S ≤ l.S := by
  unfold Len.S
  have e1 : ∀ j, (l.comap (win (hl (a := a) (b := b)))).val (x a j) = l.val (x _ (wt hl j)) := by
    intro j
    show l.val (win hl (x a j)) = _
    rw [win_x]
  have e2 : ∀ j, (l.comap (win (hr (a := a) (b := b)))).val (x b j) = l.val (x _ (wt hr j)) := by
    intro j
    show l.val (win hr (x b j)) = _
    rw [win_x]
  rw [sum_congr rfl fun j _ => e1 j, sum_congr rfl fun j _ => e2 j]
  have i1 : Function.Injective (wt (hl (a := a) (b := b))) := by
    intro j j' h
    simpa [wt, Fin.ext_iff] using h
  have i2 : Function.Injective (wt (hr (a := a) (b := b))) := by
    intro j j' h
    simpa [wt, Fin.ext_iff] using h
  rw [← sum_image (s := univ) (g := wt (hl (a := a) (b := b))) (f := fun k => l.val (x _ k))
      (fun j _ j' _ h => i1 h),
    ← sum_image (s := univ) (g := wt (hr (a := a) (b := b))) (f := fun k => l.val (x _ k))
      (fun j _ j' _ h => i2 h), ← sum_union]
  · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => l.nonneg _
  · rw [disjoint_left]
    intro k h1 h2
    simp only [mem_image, mem_univ, true_and] at h1 h2
    obtain ⟨j, rfl⟩ := h1
    obtain ⟨j', h⟩ := h2
    simp only [wt, Fin.ext_iff] at h
    omega

/-- The upper left block. -/
def tr {n n' : ℕ} (h : n ≤ n') : U n' →* U n where
  toFun A := mk (Matrix.of fun i j => mat A (Fin.castLE h i) (Fin.castLE h j))
    (fun i j hij => mat_lt A (by simpa using hij)) (fun i => mat_diag A _)
  map_one' := by
    apply mat_inj
    ext i j
    show (1 : Matrix _ _ F2) (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix _ _ F2) i j
    simp [Matrix.one_apply, Fin.ext_iff]
  map_mul' A B := by
    apply mat_inj
    ext i j
    show mat (A * B) (Fin.castLE h i) (Fin.castLE h j) = _
    rw [mat_mul, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine sum_bij_ne_zero (fun k _ _ => Fin.castLE h k) (fun _ _ _ => mem_univ _)
      (fun k _ _ k' _ _ hk => by simpa [Fin.ext_iff] using hk) ?_ (fun _ _ _ => rfl)
    intro k _ hk
    have hkj : k ≤ Fin.castLE h j := by
      by_contra hlt
      rw [mat_lt B (not_le.1 hlt), mul_zero] at hk
      exact hk rfl
    have hkn : k.1 < n := lt_of_le_of_lt (Fin.le_def.1 hkj) j.2
    exact ⟨⟨k.1, hkn⟩, mem_univ _, hk, rfl⟩

theorem tr_apply {n n' : ℕ} (h : n ≤ n') (A : U n') (i j : Fin n) :
    mat (tr h A) i j = mat A (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem tr_surjective {n n' : ℕ} (h : n ≤ n') : Function.Surjective (tr h) := by
  intro A
  refine ⟨win (p := 0) (by omega : 0 + n ≤ n') A, ?_⟩
  apply mat_inj
  ext i j
  have e : ∀ i : Fin n, Fin.castLE h i = we (p := 0) (by omega : 0 + n ≤ n') i := by
    intro i
    simp [we, Fin.ext_iff]
  rw [tr_apply, mat_win, e, e, wm, Matrix.add_apply, Matrix.sub_apply, wi_mul_we, wi_mul_we,
    Matrix.one_apply, Matrix.one_apply]
  simp [we_inj]

theorem bd_mono {m : ℕ} {s : ℝ} {n n' : ℕ} (h : n ≤ n') {κ : ℝ} (hκ : 0 ≤ κ) (hB : Bd m s n' κ) :
    Bd m s n κ := by
  intro l hC
  have h1 := hB (l.comap (tr h)) (hC.comap _)
  rw [Len.rms_comap _ _ (tr_surjective h)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hκ)
  unfold Len.S
  have e : ∀ j : Fin (n' - 1), (l.comap (tr h)).val (x n' j) =
      if hj : j.1 < n - 1 then l.val (x n ⟨j.1, hj⟩) else 0 := by
    intro j
    show l.val (tr h (x n' j)) = _
    split_ifs with hj
    · congr 1
      apply mat_inj
      ext a b
      rw [tr_apply, mat_x, mat_x]
      simp [Matrix.one_apply, Matrix.single_apply, lo, hi, Fin.ext_iff]
    · have : tr h (x n' j) = 1 := by
        apply mat_inj
        ext a b
        rw [tr_apply, mat_x, mat_one]
        have : ¬ (j.1 = a.1 ∧ j.1 + 1 = b.1) := by
          have := b.2
          omega
        simp [Matrix.one_apply, Matrix.single_apply, lo, hi, Fin.ext_iff, this]
      rw [this, l.one']
  rw [sum_congr rfl fun j _ => e j]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin (n' - 1) => j.1 < n - 1)]
  rw [Finset.sum_eq_zero (s := univ.filter fun j : Fin (n' - 1) => ¬ j.1 < n - 1), add_zero]
  · refine le_of_eq ?_
    refine sum_bij' (fun j hj => ⟨j.1, by simpa using hj⟩)
      (fun j _ => ⟨j.1, by have := j.2; omega⟩) ?_ ?_ ?_ ?_ ?_
    · intro j _
      exact mem_univ _
    · intro j _
      simp
    · intro j _
      rfl
    · intro j _
      rfl
    · intro j hj
      have : j.1 < n - 1 := by simpa using hj
      simp [this]
  · intro j hj
    have : ¬ j.1 < n - 1 := by simpa using hj
    simp [this]

end Nc.Flag
