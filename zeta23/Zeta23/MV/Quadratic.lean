/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.MV.Spacing

/-!
# MV step 1 — the quadratic-form bound `U ≤ 73 V` (arXiv:2203.14950 Thm 1.2 shape)

`U := Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²  ≤  73 Σ t_n² ` for nonneg `t`:
Cauchy–Schwarz `U² ≤ V·W`; `W = S + T` (diagonal/off-diagonal of the expanded square);
`S ≤ 27V` (σ=4 spacing); `T ≤ 72U` (two-point lemma); the quadratic inequality gives `U ≤ 73V`.
-/

noncomputable section
open Real Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

/-- The quadratic form `U = Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²`. -/
def Uform (freq δ : ι → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ m, ∑ n ∈ Finset.univ.erase m,
    δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * t m * t n / (freq m - freq n) ^ 2

/-- Swap the two layers of an `erase`-nested double sum. -/
lemma sum_erase_comm {M : Type*} [AddCommMonoid M] (F : ι → ι → M) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, F m n = ∑ n, ∑ m ∈ Finset.univ.erase n, F m n := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun n => Finset.univ.erase n)]
  intro n m
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Swap the inner two layers of the distinct-triple sum (outer index `m` fixed). -/
lemma sum_erase_erase_comm {M : Type*} [AddCommMonoid M] (m : ι) (G : ι → ι → M) :
    ∑ n ∈ Finset.univ.erase m, ∑ l ∈ (Finset.univ.erase n).erase m, G n l
      = ∑ l ∈ Finset.univ.erase m, ∑ n ∈ (Finset.univ.erase l).erase m, G n l := by
  rw [Finset.sum_comm' (t' := Finset.univ.erase m)
    (s' := fun l => (Finset.univ.erase l).erase m)]
  intro n l
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, Ne.symm h3⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3, Ne.symm h2⟩

/-- **Step 1**: `U ≤ 73 Σ t²` for admissible `(freq, δ)` and nonneg `t`. -/
theorem Uform_le (h : Adm freq δ) (t : ι → ℝ) (ht : ∀ r, 0 ≤ t r) :
    Uform freq δ t ≤ 73 * ∑ n, t n ^ 2 := by
  classical
  set V : ℝ := ∑ n, t n ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun n _ => sq_nonneg _
  set f : ι → ι → ℝ := fun m n => δ m * Real.sqrt (δ m) * t m / (freq m - freq n) ^ 2 with hf
  have hf0 : ∀ m n, 0 ≤ f m n := by
    intro m n
    have := (h.pos m).le
    have := ht m
    rw [hf]
    positivity
  set B : ι → ℝ := fun n => ∑ m ∈ Finset.univ.erase n, f m n with hB
  have hU0 : 0 ≤ Uform freq δ t := by
    apply Finset.sum_nonneg
    intro m _
    apply Finset.sum_nonneg
    intro n _
    have h1 := (h.pos m).le
    have h2 := (h.pos n).le
    have h3 := ht m
    have h4 := ht n
    positivity
  have hUeq : Uform freq δ t = ∑ n, t n * (Real.sqrt (δ n) * B n) := by
    rw [Uform, sum_erase_comm (fun m n => δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * t m * t n
      / (freq m - freq n) ^ 2)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hB, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hf]
    ring
  set W : ℝ := ∑ n, δ n * B n ^ 2 with hW
  have hCS : Uform freq δ t ^ 2 ≤ V * W := by
    rw [hUeq]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ t (fun n => Real.sqrt (δ n) * B n)
    calc (∑ n, t n * (Real.sqrt (δ n) * B n)) ^ 2
        ≤ (∑ n, t n ^ 2) * ∑ n, (Real.sqrt (δ n) * B n) ^ 2 := hcs
      _ = V * W := by
          rw [hV, hW]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_pow, Real.sq_sqrt (h.pos n).le]
  -- expand W = S + T
  have hWeq : W = (∑ n, ∑ m ∈ Finset.univ.erase n, δ n * (f m n * f m n))
      + ∑ n, ∑ m ∈ Finset.univ.erase n, ∑ l ∈ (Finset.univ.erase n).erase m,
          δ n * (f m n * f l n) := by
    rw [hW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hB, sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum, ← Finset.add_sum_erase _ (fun l => δ n * (f m n * f l n)) hm]
  -- S ≤ 27 V
  have hS : (∑ n, ∑ m ∈ Finset.univ.erase n, δ n * (f m n * f m n)) ≤ 27 * V := by
    rw [← sum_erase_comm (fun m n => δ n * (f m n * f m n))]
    have hper : ∀ m ∈ (Finset.univ : Finset ι),
        ∑ n ∈ Finset.univ.erase m, δ n * (f m n * f m n) ≤ 27 * t m ^ 2 := by
      intro m _
      have hδm := h.pos m
      have hss : Real.sqrt (δ m) * Real.sqrt (δ m) = δ m := Real.mul_self_sqrt hδm.le
      have e2 : ∀ n, δ n * (f m n * f m n)
          = (δ m ^ 3 * t m ^ 2) * (δ n / (freq m - freq n) ^ 4) := by
        intro n
        rw [hf]
        have e3 : ((freq m - freq n) ^ 2) * ((freq m - freq n) ^ 2)
            = (freq m - freq n) ^ 4 := by ring
        field_simp
        rw [Real.sq_sqrt hδm.le]
      calc ∑ n ∈ Finset.univ.erase m, δ n * (f m n * f m n)
          = (δ m ^ 3 * t m ^ 2) * ∑ n ∈ Finset.univ.erase m, δ n / (freq m - freq n) ^ 4 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => e2 n
        _ ≤ (δ m ^ 3 * t m ^ 2) * (27 / δ m ^ 3) := by
            have hnn : 0 ≤ δ m ^ 3 * t m ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left (h.spacing_four m) hnn
        _ = 27 * t m ^ 2 := by field_simp
    calc ∑ m, ∑ n ∈ Finset.univ.erase m, δ n * (f m n * f m n)
        ≤ ∑ m, 27 * t m ^ 2 := Finset.sum_le_sum hper
      _ = 27 * V := by rw [hV, Finset.mul_sum]
  -- T ≤ 72 U
  have hT : (∑ n, ∑ m ∈ Finset.univ.erase n, ∑ l ∈ (Finset.univ.erase n).erase m,
        δ n * (f m n * f l n)) ≤ 72 * Uform freq δ t := by
    rw [← sum_erase_comm (fun m n => ∑ l ∈ (Finset.univ.erase n).erase m, δ n * (f m n * f l n))]
    have hswap : ∀ m : ι, ∑ n ∈ Finset.univ.erase m, ∑ l ∈ (Finset.univ.erase n).erase m,
        δ n * (f m n * f l n)
        = ∑ l ∈ Finset.univ.erase m, ∑ n ∈ (Finset.univ.erase l).erase m,
            δ n * (f m n * f l n) :=
      fun m => sum_erase_erase_comm m (fun n l => δ n * (f m n * f l n))
    calc ∑ m, ∑ n ∈ Finset.univ.erase m, ∑ l ∈ (Finset.univ.erase n).erase m,
          δ n * (f m n * f l n)
        = ∑ m, ∑ l ∈ Finset.univ.erase m, ∑ n ∈ (Finset.univ.erase l).erase m,
            δ n * (f m n * f l n) := Finset.sum_congr rfl fun m _ => hswap m
      _ ≤ ∑ m, ∑ l ∈ Finset.univ.erase m,
            (δ m * Real.sqrt (δ m) * t m) * (δ l * Real.sqrt (δ l) * t l)
              * (36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2)) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun l hl => ?_
          have hlm : l ≠ m := Finset.ne_of_mem_erase hl
          have hc1 : 0 ≤ δ m * Real.sqrt (δ m) * t m := by
            have := (h.pos m).le; have := ht m; positivity
          have hc2 : 0 ≤ δ l * Real.sqrt (δ l) * t l := by
            have := (h.pos l).le; have := ht l; positivity
          have hexp : ∑ n ∈ (Finset.univ.erase l).erase m, δ n * (f m n * f l n)
              = (δ m * Real.sqrt (δ m) * t m) * (δ l * Real.sqrt (δ l) * t l)
                * ∑ n ∈ (Finset.univ.erase l).erase m,
                    δ n / ((freq n - freq l) ^ 2 * (freq n - freq m) ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n hn => ?_
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            have hnl : n ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hn)
            have h1 : freq n - freq m ≠ 0 := sub_ne_zero.2 fun hh => hnm (h.inj hh)
            have h2 : freq n - freq l ≠ 0 := sub_ne_zero.2 fun hh => hnl (h.inj hh)
            simp only [hf]
            rw [show (freq m - freq n) ^ 2 = (freq n - freq m) ^ 2 by ring,
              show (freq l - freq n) ^ 2 = (freq n - freq l) ^ 2 by ring]
            field_simp
          rw [hexp]
          exact mul_le_mul_of_nonneg_left (h.two_point hlm) (mul_nonneg hc1 hc2)
      _ = ∑ m, ∑ l ∈ Finset.univ.erase m, 36 *
            (δ m * Real.sqrt (δ m) * Real.sqrt (δ l) * t m * t l / (freq m - freq l) ^ 2
              + δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m / (freq m - freq l) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l hl => ?_
          have hlm : l ≠ m := Finset.ne_of_mem_erase hl
          have hδl := h.pos l
          have hδm := h.pos m
          have hsl : Real.sqrt (δ l) * Real.sqrt (δ l) = δ l := Real.mul_self_sqrt hδl.le
          have hsm : Real.sqrt (δ m) * Real.sqrt (δ m) = δ m := Real.mul_self_sqrt hδm.le
          have hX : freq l - freq m ≠ 0 := sub_ne_zero.2 fun hh => hlm (h.inj hh)
          have hfe : (freq m - freq l) ^ 2 = (freq l - freq m) ^ 2 := by ring
          rw [hfe]
          field_simp
          ring
      _ = 36 * ((∑ m, ∑ l ∈ Finset.univ.erase m,
              δ m * Real.sqrt (δ m) * Real.sqrt (δ l) * t m * t l / (freq m - freq l) ^ 2)
            + ∑ m, ∑ l ∈ Finset.univ.erase m,
              δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m / (freq m - freq l) ^ 2) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 72 * Uform freq δ t := by
          have hsecond : (∑ m, ∑ l ∈ Finset.univ.erase m,
              δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m / (freq m - freq l) ^ 2)
              = Uform freq δ t := by
            rw [sum_erase_comm (fun m l => δ l * Real.sqrt (δ l) * Real.sqrt (δ m) * t l * t m
              / (freq m - freq l) ^ 2)]
            rw [Uform]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
            rw [show (freq m - freq l) ^ 2 = (freq l - freq m) ^ 2 by ring]
          rw [hsecond, Uform]
          ring
  -- assemble the quadratic inequality
  have hq : Uform freq δ t ^ 2 ≤ V * (27 * V + 72 * Uform freq δ t) := by
    calc Uform freq δ t ^ 2 ≤ V * W := hCS
      _ = V * ((∑ n, ∑ m ∈ Finset.univ.erase n, δ n * (f m n * f m n))
          + ∑ n, ∑ m ∈ Finset.univ.erase n, ∑ l ∈ (Finset.univ.erase n).erase m,
              δ n * (f m n * f l n)) := by rw [hWeq]
      _ ≤ V * (27 * V + 72 * Uform freq δ t) := by
          apply mul_le_mul_of_nonneg_left _ hV0
          exact add_le_add hS hT
  nlinarith [hU0, hV0, sq_nonneg (Uform freq δ t - 73 * V), sq_nonneg V,
    mul_nonneg hU0 hV0, mul_nonneg hV0 hV0]

end MV
end Zeta23
