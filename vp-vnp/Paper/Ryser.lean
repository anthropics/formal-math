/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.PermValiant
import Nc.Final.CClasses
import Nc.Hc.Vnp

/-!
# The permanent is in VNP, by Ryser's formula
-/

namespace Paper

open Finset MvPolynomial Nc

variable (F : Type) [Field F] (n : ℕ)

/-- Ryser's summand: the rows' sums over the chosen columns, with the sign of the number of columns that are left
out. -/
noncomputable def ryserWit : MvPolynomial ((Fin n × Fin n) ⊕ Fin n) F :=
  (∏ i, ∑ j, X (Sum.inr j) * X (Sum.inl (i, j))) * ∏ j, (C (-1) + C 2 * X (Sum.inr j))

open Classical in
/-- **Ryser's formula.** -/
theorem genPerm_eq_ryser : genPerm F n = ∑ e : Fin n → Bool, bits (ryserWit F n) e := by
  have h1 : ∀ e : Fin n → Bool, bits (ryserWit F n) e =
      ∑ f : Fin n → Fin n, (∏ i, X (i, f i)) * ∏ j, ((-1 + 2 * if e j then 1 else 0) *
        ∏ _i ∈ univ.filter (fun i => f i = j), (if e j then (1 : MvPolynomial (Fin n × Fin n) F) else 0)) := by
    intro e
    simp only [ryserWit, bits_mul, bits_prod, bits_sum, bits_inl, bits_inr, bits_add, bits_C]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_fiberwise univ f (fun i => if e (f i) then _ else _)]
    rw [Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]]
    rw [map_neg, map_one, map_ofNat]
    ring
  rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ f : Fin n → Fin n, (∑ e : Fin n → Bool, ∏ j, ((-1 + 2 * if e j then 1 else 0) *
      ∏ _i ∈ univ.filter (fun i => f i = j), (if e j then (1 : MvPolynomial (Fin n × Fin n) F) else 0))) =
      if Function.Bijective f then 1 else 0 := by
    intro f
    rw [← Fintype.prod_sum (fun j (b : Bool) => (-1 + 2 * if b then 1 else 0) *
      ∏ _i ∈ univ.filter (fun i => f i = j), (if b then (1 : MvPolynomial (Fin n × Fin n) F) else 0))]
    split_ifs with hf
    · refine Finset.prod_eq_one fun j _ => ?_
      obtain ⟨i, hi⟩ := hf.2 j
      rw [Fintype.sum_bool, Finset.prod_eq_zero (s := univ.filter (fun i => f i = j)) (i := i)
        (f := fun _ => if false = true then (1 : MvPolynomial (Fin n × Fin n) F) else 0) (by simp [hi]) (by simp)]
      simp
      ring
    · rw [← Finite.surjective_iff_bijective] at hf
      simp only [Function.Surjective, not_forall, not_exists] at hf
      obtain ⟨j, hj⟩ := hf
      refine Finset.prod_eq_zero (mem_univ j) ?_
      rw [filter_false_of_mem fun i _ => hj i, Fintype.sum_bool]
      simp
      ring
  simp only [h2]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  unfold genPerm Matrix.permanent
  simp only [Matrix.of_apply]
  symm
  refine Finset.sum_bij' (fun f hf => (Equiv.ofBijective f (mem_filter.1 hf).2).symm) (fun σ _ => ⇑σ.symm)
    (fun _ _ => mem_univ _) (fun σ _ => mem_filter.2 ⟨mem_univ _, σ.symm.bijective⟩) ?_ ?_ ?_
  · intro f hf
    rfl
  · intro σ _
    ext i
    simp
  · intro f hf
    refine Eq.symm ?_
    rw [← Equiv.prod_comp (Equiv.ofBijective f (mem_filter.1 hf).2)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Equiv.symm_apply_apply]
    rfl

theorem csize_ryser : CSize (ryserWit F n) (40 * (n + 1) ^ 4) (40 * (n + 1) ^ 4) := by
  have h1 := CSize.prod (univ : Finset (Fin n))
    (f := fun i => ∑ j : Fin n, X (Sum.inr j) * (X (Sum.inl (i, j)) : MvPolynomial ((Fin n × Fin n) ⊕ Fin n) F))
    fun i _ => CSize.sum univ fun j _ => (CSize.var (Sum.inr j)).mul (CSize.var (Sum.inl (i, j)))
  have h2 := CSize.prod (univ : Finset (Fin n))
    (f := fun j => C (-1) + C 2 * (X (Sum.inr j) : MvPolynomial ((Fin n × Fin n) ⊕ Fin n) F)) (s := 5) (d := 1)
    fun j _ => ((CSize.const (-1)).mono (s' := 1) (d' := 1) le_rfl (by norm_num)).add
      (((CSize.const 2).mul (CSize.var (Sum.inr j))).mono (s' := 3) le_rfl le_rfl)
  refine (h1.mul h2).mono ?_ ?_
  all_goals
    simp only [Finset.card_univ, Fintype.card_fin]
    nlinarith [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

/-- **The permanent is in VNP (Ryser's formula).** -/
theorem perm_mem_VNP : ({ X := fun n => Fin n × Fin n, poly := genPerm F } : Family F) ∈ VNP F := by
  refine ⟨id, ryserWit F, ⟨700, fun n => ?_⟩, genPerm_eq_ryser F⟩
  have hb := Hc.quartic_bound (n := n) (C := 700) le_rfl
  obtain ⟨h1, h2⟩ := csize_ryser F n
  refine ⟨le_trans ?_ hb, h2.trans hb, h1.mono hb⟩
  show Fintype.card ((Fin n × Fin n) ⊕ Fin n) ≤ _
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

end Paper
