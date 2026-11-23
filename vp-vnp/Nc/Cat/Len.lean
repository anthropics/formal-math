/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Length functions on `ℤ²` with the crossing inequality

`Len N`: an even subadditive function on `ℤ²` with the inequality (Q). Its homogeneous version
satisfies (Q), too. (That a homogeneous one satisfies the law of the parallelogram is Lemma lem:means, in Paper/Means.lean.)
-/

open Filter Topology Finset

namespace Cat

/-- Even subadditive functions on `ℤ²` with the inequality (Q). -/
structure Len (N : ℤ × ℤ → ℝ) : Prop where
  nonneg : ∀ h, 0 ≤ N h
  zero : N 0 = 0
  neg : ∀ h, N (-h) = N h
  add : ∀ h h', N (h + h') ≤ N h + N h'
  q : ∀ X V Y U n n' k k' : ℤ × ℤ, ∀ τ : ℝ, 0 < τ →
    2 * (N (X - V) ^ 2 + N (Y - U) ^ 2) ≤
      N (X - V) * (N (X - n) + N (V - n') + N (X - k) + N (V - k'))
      + N (Y - U) * (N (Y - n) + N (U - n') + N (U - k) + N (Y - k'))
      + τ * (N (X - V) ^ 2 + N (Y - U) ^ 2) + (N (n - n') ^ 2 + N (k - k') ^ 2) / (2 * τ)

/-- Homogeneous along natural numbers. -/
def Homog (N : ℤ × ℤ → ℝ) : Prop := ∀ (m : ℕ) h, N (m • h) = m * N h

theorem Len.subadditive {N : ℤ × ℤ → ℝ} (hN : Len N) (h : ℤ × ℤ) :
    Subadditive fun S : ℕ => N (S • h) := by
  intro m n
  simp only [add_smul]
  exact hN.add _ _

/-- The homogeneous version of a length function. -/
theorem Len.exists_homog {N : ℤ × ℤ → ℝ} (hN : Len N) :
    ∃ N' : ℤ × ℤ → ℝ, Len N' ∧ Homog N' ∧ (∀ h, N' h ≤ N h) ∧
      ∀ h (c : ℝ), (∀ S : ℕ, 0 < S → c * S ≤ N (S • h)) → c ≤ N' h := by
  let N' : ℤ × ℤ → ℝ := fun h => (hN.subadditive h).lim
  have hbdd : ∀ h, BddBelow (Set.range fun S : ℕ => N (S • h) / S) := by
    intro h
    refine ⟨0, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact div_nonneg (hN.nonneg _) (Nat.cast_nonneg _)
  have hT : ∀ h, Tendsto (fun S : ℕ => N (S • h) / S) atTop (𝓝 (N' h)) := fun h =>
    (hN.subadditive h).tendsto_lim (hbdd h)
  have hhom : Homog N' := by
    intro m h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 := hT ((0 : ℕ) • h)
      simp only [zero_smul, smul_zero, hN.zero, zero_div] at h1
      rw [Nat.cast_zero, zero_mul, zero_smul]
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    · have h1 := hT (m • h)
      have h2 : Tendsto (fun S : ℕ => (m : ℝ) * (N ((S * m) • h) / (S * m : ℕ))) atTop
          (𝓝 (m * N' h)) :=
        ((hT h).comp (tendsto_id.atTop_mul_const' hm)).const_mul _
      refine tendsto_nhds_unique h1 (h2.congr fun S => ?_)
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [mul_smul]
      push_cast
      rcases Nat.eq_zero_or_pos S with rfl | hS
      · simp
      · have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
        field_simp
  refine ⟨N', ⟨?_, ?_, ?_, ?_, ?_⟩, hhom, ?_, ?_⟩
  · exact fun h => ge_of_tendsto' (hT h) fun S => div_nonneg (hN.nonneg _) (Nat.cast_nonneg _)
  · have := hhom 0 0
    simpa using this
  · intro h
    refine tendsto_nhds_unique (hT (-h)) ((hT h).congr fun S => ?_)
    rw [smul_neg, hN.neg]
  · intro h h'
    refine le_of_tendsto_of_tendsto' (hT _) ((hT h).add (hT h')) fun S => ?_
    rw [smul_add, ← add_div]
    exact div_le_div_of_nonneg_right (hN.add _ _) (Nat.cast_nonneg _)
  · intro X V Y U n n' k k' τ hτ
    have hl : Tendsto (fun S : ℕ => 2 * ((N (S • (X - V)) / S) ^ 2 + (N (S • (Y - U)) / S) ^ 2))
        atTop (𝓝 (2 * (N' (X - V) ^ 2 + N' (Y - U) ^ 2))) :=
      (((hT _).pow 2).add ((hT _).pow 2)).const_mul 2
    have hr : Tendsto (fun S : ℕ =>
        N (S • (X - V)) / S * (N (S • (X - n)) / S + N (S • (V - n')) / S
          + N (S • (X - k)) / S + N (S • (V - k')) / S)
        + N (S • (Y - U)) / S * (N (S • (Y - n)) / S + N (S • (U - n')) / S
          + N (S • (U - k)) / S + N (S • (Y - k')) / S)
        + τ * ((N (S • (X - V)) / S) ^ 2 + (N (S • (Y - U)) / S) ^ 2)
        + ((N (S • (n - n')) / S) ^ 2 + (N (S • (k - k')) / S) ^ 2) / (2 * τ)) atTop
        (𝓝 (N' (X - V) * (N' (X - n) + N' (V - n') + N' (X - k) + N' (V - k'))
          + N' (Y - U) * (N' (Y - n) + N' (U - n') + N' (U - k) + N' (Y - k'))
          + τ * (N' (X - V) ^ 2 + N' (Y - U) ^ 2)
          + (N' (n - n') ^ 2 + N' (k - k') ^ 2) / (2 * τ))) :=
      (((((hT _).mul ((((hT _).add (hT _)).add (hT _)).add (hT _)))).add
        ((hT _).mul ((((hT _).add (hT _)).add (hT _)).add (hT _)))).add
        ((((hT _).pow 2).add ((hT _).pow 2)).const_mul τ)).add
        ((((hT _).pow 2).add ((hT _).pow 2)).div_const _)
    refine le_of_tendsto_of_tendsto' hl hr fun S => ?_
    have h := hN.q (S • X) (S • V) (S • Y) (S • U) (S • n) (S • n') (S • k) (S • k') τ hτ
    simp only [← smul_sub] at h
    rcases Nat.eq_zero_or_pos S with rfl | hS
    · simp
    · have hS' : (0 : ℝ) < S := by exact_mod_cast hS
      have h2 := div_le_div_of_nonneg_right h (show 0 ≤ (S : ℝ) ^ 2 by positivity)
      refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_))
      · field_simp
      · field_simp
  · exact fun h => by
      have := (hN.subadditive h).lim_le_div (hbdd h) (n := 1) one_ne_zero
      simpa using this
  · intro h c hc
    refine ge_of_tendsto (hT h) ?_
    filter_upwards [eventually_gt_atTop 0] with S hS
    rw [le_div_iff₀ (by exact_mod_cast hS)]
    exact hc S hS

section par

variable {N : ℤ × ℤ → ℝ} (hN : Len N)

include hN in
theorem Len.sub_le (h h' : ℤ × ℤ) : N (h - h') ≤ N h + N h' := by
  rw [sub_eq_add_neg]
  exact (hN.add _ _).trans_eq (by rw [hN.neg])

include hN in
theorem Len.le_add_sub (h h' : ℤ × ℤ) : N h ≤ N (h - h') + N h' := by
  have := hN.add (h - h') h'
  rwa [sub_add_cancel] at this

include hN in
theorem Len.abs_sub_le (h h' : ℤ × ℤ) : |N h - N h'| ≤ N (h - h') := by
  rw [abs_le]
  constructor
  · have := hN.le_add_sub h' h
    rw [← hN.neg (h' - h), neg_sub] at this
    linarith
  · linarith [hN.le_add_sub h h']

end par

end Cat
