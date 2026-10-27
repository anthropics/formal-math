/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import PartitionStatement

/-! # A recurrence for the number of partitions

Taking k copies of the part v away is a bijection from the partitions of E in which v occurs at
least k times to the partitions of E − kv (`card_count_ge`).
Summing the parts of all partitions of E in two ways then gives E·p(E) = Σ_{v ≥ 1} Σ_{k ≥ 1, kv ≤ E}
v·p(E − kv) (`mul_p_eq`): a partition in which v occurs c times
contributes c·v, and c is the number of k ≥ 1 with k ≤ c. -/

public section

namespace ClauseBound.Part

open Finset Partitions

/-- p(0) = 1. -/
theorem p_zero : p 0 = 1 := Fintype.card_unique

/-- p(E) ≥ 1. -/
theorem p_pos (E : ℕ) : 1 ≤ p E := Fintype.card_pos

/-- The partitions of E in which the part v occurs at least k times are as many as the partitions of
E − kv. -/
theorem card_count_ge {E v k : ℕ} (hv : 1 ≤ v) (h : k * v ≤ E) :
    #{π : Nat.Partition E | k ≤ π.parts.count v} = p (E - k * v) := by
  have hsum : (Multiset.replicate k v).sum = k * v := by rw [Multiset.sum_replicate, smul_eq_mul]
  rw [p, ← card_univ]
  refine card_bij'
    (fun π hπ => ⟨π.parts - Multiset.replicate k v, fun hi => π.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi), ?_⟩)
    (fun σ _ => ⟨σ.parts + Multiset.replicate k v, fun hi => ?_, ?_⟩) (fun _ _ => mem_univ _) (fun σ _ => ?_) (fun π hπ => ?_) (fun σ _ => ?_)
  · have hle : Multiset.replicate k v ≤ π.parts := Multiset.le_count_iff_replicate_le.1 (mem_filter.1 hπ).2
    have h1 := congrArg Multiset.sum (Multiset.sub_add_cancel hle)
    rw [Multiset.sum_add, hsum, π.parts_sum] at h1
    omega
  · rcases Multiset.mem_add.1 hi with hi | hi
    · exact σ.parts_pos hi
    · rw [Multiset.eq_of_mem_replicate hi]
      exact hv
  · rw [Multiset.sum_add, hsum, σ.parts_sum]
    omega
  · simp
  · exact Nat.Partition.ext (Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.1 (mem_filter.1 hπ).2))
  · exact Nat.Partition.ext Multiset.add_sub_cancel_right

/-- p is monotone. -/
theorem p_mono {E E' : ℕ} (h : E ≤ E') : p E ≤ p E' := by
  have h1 := card_count_ge (E := E') (v := 1) (k := E' - E) le_rfl (by omega)
  rw [show E' - (E' - E) * 1 = E by omega] at h1
  rw [← h1, p, ← card_univ]
  exact card_le_card (filter_subset _ _)

/-- E·p(E) = Σ_{v ≥ 1} Σ_{k ≥ 1, kv ≤ E} v·p(E − kv). -/
theorem mul_p_eq (E : ℕ) : E * p E = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), v * p (E - k * v) := by
  have h1 : ∀ π : Nat.Partition E, ∑ v ∈ Icc 1 E, π.parts.count v * v = E := by
    intro π
    have hsub : π.parts.toFinset ⊆ Icc 1 E := fun v hv =>
      mem_Icc.2 ⟨π.parts_pos (Multiset.mem_toFinset.1 hv), π.le_of_mem_parts (Multiset.mem_toFinset.1 hv)⟩
    have h := Finset.sum_multiset_count_of_subset π.parts (Icc 1 E) hsub
    rw [π.parts_sum] at h
    simpa only [smul_eq_mul] using h.symm
  have h2 : ∀ π : Nat.Partition E, ∀ v ∈ Icc 1 E, #{k ∈ Icc 1 (E / v) | k ≤ π.parts.count v} = π.parts.count v := by
    intro π v hv
    have hle : π.parts.count v * v ≤ E :=
      (single_le_sum (f := fun v => π.parts.count v * v) (fun _ _ => Nat.zero_le _) hv).trans (h1 π).le
    have hle' : π.parts.count v ≤ E / v := (Nat.le_div_iff_mul_le (mem_Icc.1 hv).1).2 hle
    have heq : {k ∈ Icc 1 (E / v) | k ≤ π.parts.count v} = Icc 1 (π.parts.count v) := by
      ext k
      simp only [mem_filter, mem_Icc]
      omega
    rw [heq, Nat.card_Icc, Nat.add_sub_cancel]
  calc E * p E = ∑ _π : Nat.Partition E, E := by rw [sum_const, card_univ, smul_eq_mul, mul_comm, p]
    _ = ∑ π : Nat.Partition E, ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), if k ≤ π.parts.count v then v else 0 := by
        refine sum_congr rfl fun π _ => (h1 π).symm.trans (sum_congr rfl fun v hv => ?_)
        rw [← sum_filter, sum_const, smul_eq_mul, h2 π v hv]
    _ = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), ∑ π : Nat.Partition E, if k ≤ π.parts.count v then v else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun v _ => sum_comm
    _ = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), v * p (E - k * v) := by
        refine sum_congr rfl fun v hv => sum_congr rfl fun k hk => ?_
        have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
        rw [← sum_filter, sum_const, smul_eq_mul, card_count_ge hv1 ((Nat.le_div_iff_mul_le hv1).1 (mem_Icc.1 hk).2), mul_comm]

end ClauseBound.Part
