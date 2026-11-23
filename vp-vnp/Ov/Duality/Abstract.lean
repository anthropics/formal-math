/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Gauges on a commutative monoid with a covering relation

Let M be a commutative monoid (the tensors up to equivalence) with a relation "t is covered by the finite
family b" (t is a sum of restrictions of the members of b). A gauge is a function p ≥ 0 on M with p(1) = 1,
p(st) ≤ p(s)p(t), and p(t) ≤ ∑ p(b) whenever b covers t. This file has the definitions, infima of directed families of
gauges (`isPre_iInf`, `keeps_iInf`), and the first facts on the numbers a with p(tⁿ) ≤ C·aⁿ (`IsPre.rad`). The proof of
Proposition prop:gauge is in Paper/Gauges.lean.
-/

namespace Ov.Duality

variable {M : Type*} [CommMonoid M]

/-- A covering relation between elements and finite families of elements: reflexive, transitive,
and compatible with multiplication by an element. -/
structure Cover (M : Type*) [CommMonoid M] where
  /-- the element is covered by the family -/
  cov : ∀ {κ : Type} [Fintype κ], M → (κ → M) → Prop
  refl : ∀ t, cov t (fun _ : Unit => t)
  bind : ∀ {κ : Type} [Fintype κ] {μ : κ → Type} [∀ k, Fintype (μ k)] {t : M} {b : κ → M}
    {c : ∀ k, μ k → M}, cov t b → (∀ k, cov (b k) (c k)) → cov t (fun x : Σ k, μ k => c x.1 x.2)
  mul : ∀ {κ : Type} [Fintype κ] {t : M} {b : κ → M} (s : M), cov t b →
    cov (t * s) (fun k => b k * s)

/-- The function p is a gauge: p ≥ 0, p(1) = 1, submultiplicative,
and subadditive under covers. -/
structure IsPre (D : Cover M) (p : M → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ p t
  one : p 1 = 1
  mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b → p t ≤ ∑ k, p (b k)

/-- The inequality p(tx) ≤ c·p(ty) for all t. -/
def Keeps (p : M → ℝ) (x y : M) (c : ℝ) : Prop := ∀ t, p (t * x) ≤ c * p (t * y)

variable {D : Cover M} {p : M → ℝ}

omit [CommMonoid M] in
/-- For finitely many elements, one member of a directed family is close to its infimum. -/
theorem le_iInf_add {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    {q : M → ℝ} (hq : ∀ t, q t = ⨅ i, P i t) {ε : ℝ} (hε : 0 < ε) (b : Finset M) :
    ∃ i, ∀ t ∈ b, P i t ≤ q t + ε := by
  classical
  induction b using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert a b _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt (show ⨅ i, P i a < q a + ε by rw [← hq]; linarith)
    obtain ⟨k, hki, hkj⟩ := dir i j
    refine ⟨k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact (hkj t).trans hj.le
    · exact (hki t).trans (hi t ht)

/-- A directed infimum of functions P i is a gauge if each of them is, where instead of
P i (st) ≤ P i (s)·P i (t) it is enough that P j (st) ≤ P i (s)·P i (t) for some j. -/
theorem isPre_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (nonneg : ∀ i t, 0 ≤ P i t) (one : ∀ i, P i 1 = 1)
    (mul_le : ∀ i s t, ∃ j, P j (s * t) ≤ P i s * P i t)
    (le_sum : ∀ i, ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b →
      P i t ≤ ∑ k, P i (b k)) :
    IsPre D (fun t => ⨅ i, P i t) := by
  classical
  have bdd : ∀ t, BddBelow (Set.range fun i => P i t) := fun t =>
    ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩
  have hle : ∀ i t, ⨅ j, P j t ≤ P i t := fun i t => ciInf_le (bdd t) i
  have h0 : ∀ t, 0 ≤ ⨅ i, P i t := fun t => le_ciInf fun i => nonneg i t
  refine ⟨h0, ?_, ?_, ?_⟩
  · simp [one]
  · intro s t
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := ⨅ i, P i s with hA
    set B := ⨅ i, P i t with hB
    have hA0 : 0 ≤ A := h0 s
    have hB0 : 0 ≤ B := h0 t
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    obtain ⟨i, hi⟩ := le_iInf_add dir (q := fun t => ⨅ i, P i t) (fun _ => rfl) hε {s, t}
    have h1 := hi s (by simp)
    have h2 := hi t (by simp)
    obtain ⟨j, hj⟩ := mul_le i s t
    have h3 : P i s * P i t ≤ (A + ε) * (B + ε) :=
      mul_le_mul h1 h2 (nonneg _ _) (by positivity)
    have h4 := hle j (s * t)
    nlinarith
  · intro κ _ t b hb
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := δ / (Fintype.card κ + 1) with hεd
    have hε : 0 < ε := by positivity
    obtain ⟨i, hi⟩ := le_iInf_add dir (q := fun t => ⨅ i, P i t) (fun _ => rfl) hε
      (Finset.univ.image b)
    have h1 : ∑ k, P i (b k) ≤ ∑ k, ((⨅ i, P i (b k)) + ε) :=
      Finset.sum_le_sum fun k _ => hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : (Fintype.card κ : ℝ) * ε ≤ δ := by
      rw [hεd, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h3 := (hle i t).trans (le_sum i t b hb)
    linarith

theorem keeps_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (nonneg : ∀ i t, 0 ≤ P i t)
    {x y : M} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, Keeps (P i) x y c) :
    Keeps (fun t => ⨅ i, P i t) x y c := by
  intro t
  rw [Real.mul_iInf_of_nonneg hc]
  refine le_ciInf fun i => (ciInf_le ⟨0, ?_⟩ i).trans (h i t)
  rintro _ ⟨i, rfl⟩
  exact nonneg i _

namespace IsPre

theorem pow_le (h : IsPre D p) (t : M) (n : ℕ) : p (t ^ n) ≤ p t ^ n := by
  induction n with
  | zero => simp [h.one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (h.mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (h.nonneg _))

/-- The numbers a > 0 for which there is a C with p(t^m) ≤ C·a^m for all m. Their infimum is the
spectral radius of p at t. -/
def rad (p : M → ℝ) (t : M) : Set ℝ := {a | 0 < a ∧ ∃ C : ℝ, ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m}

theorem rad_const_pos (h : IsPre D p) {t : M} {a C : ℝ} (hC : ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m) :
    1 ≤ C := by simpa [h.one] using hC 0

theorem rad_mono (h : IsPre D p) {t : M} {a b : ℝ} (ha : a ∈ rad p t) (hab : a ≤ b) :
    b ∈ rad p t := by
  obtain ⟨ha0, C, hC⟩ := ha
  have hC1 := h.rad_const_pos hC
  refine ⟨ha0.trans_le hab, C, fun m => (hC m).trans ?_⟩
  gcongr

theorem rad_bdd (p : M → ℝ) (t : M) : BddBelow (rad p t) := ⟨0, fun _ ha => ha.1.le⟩

theorem mem_rad (h : IsPre D p) (t : M) {δ : ℝ} (hδ : 0 < δ) : p t + δ ∈ rad p t :=
  ⟨by linarith [h.nonneg t], 1, fun m => by
    rw [one_mul]
    exact (h.pow_le t m).trans (pow_le_pow_left₀ (h.nonneg t) (by linarith) m)⟩

theorem mem_rad_of_lt (h : IsPre D p) {t : M} {a : ℝ} (ha : sInf (rad p t) < a) :
    a ∈ rad p t := by
  obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt ⟨_, h.mem_rad t one_pos⟩ ha
  exact h.rad_mono hb hba.le

/-- The bound for a product of powers, by the bounds for the powers. -/
theorem prod_bound (h : IsPre D p) (S : Finset M) (a C : M → ℝ)
    (ha : ∀ y, 0 < a y) (hC : ∀ y, ∀ m : ℕ, p (y ^ m) ≤ C y * a y ^ m) (e : M → ℕ) :
    p (∏ y ∈ S, y ^ e y) ≤ (∏ y ∈ S, C y) * ∏ y ∈ S, a y ^ e y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [h.one]
  | insert y S hy ih =>
    rw [Finset.prod_insert hy, Finset.prod_insert hy, Finset.prod_insert hy]
    have h1 := mul_le_mul (hC y (e y)) ih (h.nonneg _)
      (mul_nonneg (zero_le_one.trans (h.rad_const_pos (hC y))) (pow_nonneg (ha y).le _))
    calc _ ≤ _ := (h.mul_le _ _).trans h1
      _ = _ := by ring

end IsPre

end Ov.Duality
