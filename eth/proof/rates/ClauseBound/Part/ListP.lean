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
public import ClauseBound.Part.Rec

/-! # Partitions as lists

`partsLe E k` is the list of the partitions of E into parts of size at most k, each written as a
nonincreasing list of positive integers: first those with all parts < k, then those that begin
with k. `partsOf E = partsLe E E` lists all partitions of E (`mem_partsOf`), each once
(`nodup_partsOf`), so it has p(E) members (`length_partsOf`); `partsLe E k` is the same list for
every k ≥ E
(`partsLe_of_le`). As multisets the members are the multisets of positive integers with sum E, each
once (`mem_map_coe_partsOf`, `nodup_map_coe_partsOf`). A by-product is p(E) ≤ 2^E
(`p_le_two_pow`). The definitions use recursion on natural numbers and lists only. -/

public section

namespace ClauseBound.Part

open Finset Partitions

/-- The nonincreasing lists of positive integers ≤ k with sum E: first those with all parts < k,
then those that begin with k. -/
@[expose] def partsLe : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | _ + 1, 0 => []
  | E, k + 1 => partsLe E k ++ (if k + 1 ≤ E then (partsLe (E - (k + 1)) (k + 1)).map fun L => (k + 1) :: L else [])
termination_by E k => E + k

/-- The partitions of E, as nonincreasing lists of positive integers. -/
@[expose] def partsOf (E : ℕ) : List (List ℕ) := partsLe E E

/-- With no part allowed, only the empty list, for E = 0. -/
theorem partsLe_zero_right (E : ℕ) : partsLe E 0 = if E = 0 then [[]] else [] := by
  cases E <;> rw [partsLe] <;> simp

/-- The step of the recursion. -/
theorem partsLe_succ (E k : ℕ) :
    partsLe E (k + 1) = partsLe E k ++ (if k + 1 ≤ E then (partsLe (E - (k + 1)) (k + 1)).map fun L => (k + 1) :: L else []) := by
  rw [partsLe]

/-- The members of `partsLe E k`. -/
theorem mem_partsLe (E k : ℕ) (L : List ℕ) :
    L ∈ partsLe E k ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n ∧ n ≤ k) ∧ L.Pairwise (· ≥ ·) := by
  induction E using Nat.strong_induction_on generalizing k L with
  | _ E ihE =>
    induction k generalizing L with
    | zero =>
      rw [partsLe_zero_right]
      constructor
      · intro h
        split_ifs at h with hE
        · rw [List.mem_singleton.1 h, hE]
          simp
        · exact absurd h List.not_mem_nil
      · rintro ⟨hs, hp, _⟩
        cases L with
        | nil =>
          rw [if_pos (by simpa using hs.symm)]
          exact List.mem_singleton.2 rfl
        | cons n L =>
          have := hp n List.mem_cons_self
          omega
    | succ k ihk =>
      rw [partsLe_succ, List.mem_append, ihk]
      constructor
      · rintro (⟨hs, hp, hw⟩ | h)
        · exact ⟨hs, fun n hn => ⟨(hp n hn).1, (hp n hn).2.trans (Nat.le_succ k)⟩, hw⟩
        · split_ifs at h with hkE
          · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 h
            obtain ⟨hs, hp, hw⟩ := (ihE (E - (k + 1)) (by omega) (k + 1) L').1 hL'
            refine ⟨by rw [List.sum_cons, hs]; omega, ?_, List.pairwise_cons.2 ⟨fun n hn => (hp n hn).2, hw⟩⟩
            intro n hn
            rcases List.mem_cons.1 hn with rfl | hn
            · exact ⟨by omega, le_rfl⟩
            · exact hp n hn
          · exact absurd h List.not_mem_nil
      · rintro ⟨hs, hp, hw⟩
        cases L with
        | nil => exact Or.inl ⟨hs, fun n hn => absurd hn List.not_mem_nil, hw⟩
        | cons n L' =>
          have hn := hp n List.mem_cons_self
          obtain ⟨hw1, hw2⟩ := List.pairwise_cons.1 hw
          have hs' := hs
          rw [List.sum_cons] at hs'
          by_cases hnk : n = k + 1
          · subst hnk
            right
            rw [if_pos (by omega)]
            exact List.mem_map.2 ⟨L', (ihE _ (by omega) _ _).2 ⟨by omega, fun m hm => hp m (List.mem_cons_of_mem _ hm), hw2⟩, rfl⟩
          · left
            refine ⟨hs, ?_, hw⟩
            intro m hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact ⟨hn.1, by omega⟩
            · have h1 : n ≥ m := hw1 m hm
              exact ⟨(hp m (List.mem_cons_of_mem _ hm)).1, by omega⟩

/-- No list occurs twice in `partsLe E k`. -/
theorem nodup_partsLe (E k : ℕ) : (partsLe E k).Nodup := by
  induction E using Nat.strong_induction_on generalizing k with
  | _ E ihE =>
    induction k with
    | zero =>
      rw [partsLe_zero_right]
      split_ifs
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    | succ k ihk =>
      rw [partsLe_succ]
      refine List.nodup_append.2 ⟨ihk, ?_, ?_⟩
      · split_ifs with hkE
        · exact (ihE (E - (k + 1)) (by omega) (k + 1)).map (List.cons_injective)
        · exact List.nodup_nil
      · intro A hA B hB hAB
        subst hAB
        split_ifs at hB
        · obtain ⟨L', _, rfl⟩ := List.mem_map.1 hB
          have := (((mem_partsLe _ _ _).1 hA).2.1 (k + 1) List.mem_cons_self).2
          omega
        · exact absurd hB List.not_mem_nil

/-- Parts larger than E do not occur: the list is the same for all k ≥ E. -/
theorem partsLe_of_le {E k : ℕ} (h : E ≤ k) : partsLe E k = partsOf E := by
  induction k with
  | zero => rw [Nat.le_zero.1 h, partsOf]
  | succ k ih =>
    rcases Nat.lt_or_ge k E with hk | hk
    · rw [show E = k + 1 by omega, partsOf]
    · rw [partsLe_succ, if_neg (by omega), List.append_nil, ih hk]

/-- The list grows with k. -/
theorem length_partsLe_mono (E : ℕ) {k k' : ℕ} (h : k ≤ k') : (partsLe E k).length ≤ (partsLe E k').length := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hk | hk
    · rw [partsLe_succ, List.length_append]
      have := ih (by omega)
      omega
    · rw [show k = k' + 1 by omega]

namespace ListP

/-- A member of a list of natural numbers is at most the sum. -/
theorem le_sum_of_mem {L : List ℕ} {n : ℕ} (h : n ∈ L) : n ≤ L.sum := by
  induction L with
  | nil => exact absurd h List.not_mem_nil
  | cons a L ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- For E ≥ 1 there are at most 2^E − 2^(E−k) lists; for E = 0 there is one. -/
theorem length_partsLe_aux (E k : ℕ) : (partsLe E k).length ≤ 2 ^ E ∧ (1 ≤ E → (partsLe E k).length + 2 ^ (E - k) ≤ 2 ^ E) := by
  induction E using Nat.strong_induction_on generalizing k with
  | _ E ihE =>
    have key : 1 ≤ E → (partsLe E k).length + 2 ^ (E - k) ≤ 2 ^ E := by
      intro hE
      induction k with
      | zero => rw [partsLe_zero_right, if_neg (by omega)]; simp
      | succ k ihk =>
        rw [partsLe_succ, List.length_append]
        split_ifs with hkE
        · have h1 := (ihE (E - (k + 1)) (by omega) (k + 1)).1
          have h2 : 2 ^ (E - k) = 2 * 2 ^ (E - (k + 1)) := by
            rw [show E - k = (E - (k + 1)) + 1 by omega, pow_succ]; ring
          rw [List.length_map]
          omega
        · rw [show E - (k + 1) = E - k by omega]
          simpa using ihk
    refine ⟨?_, key⟩
    rcases Nat.eq_zero_or_pos E with rfl | hE
    · rw [partsLe_of_le (Nat.zero_le k), partsOf, partsLe_zero_right]
      simp
    · exact (Nat.le_add_right _ _).trans (key hE)

end ListP

open ListP

/-- The members of `partsOf E` are the nonincreasing lists of positive integers with sum E. -/
theorem mem_partsOf {E : ℕ} {L : List ℕ} : L ∈ partsOf E ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by
  rw [partsOf, mem_partsLe]
  constructor
  · rintro ⟨hs, hp, hw⟩
    exact ⟨hs, fun n hn => (hp n hn).1, hw⟩
  · rintro ⟨hs, hp, hw⟩
    exact ⟨hs, fun n hn => ⟨hp n hn, hs ▸ le_sum_of_mem hn⟩, hw⟩

/-- No list occurs twice in `partsOf E`. -/
theorem nodup_partsOf (E : ℕ) : (partsOf E).Nodup := nodup_partsLe E E

/-- As multisets, the members of `partsOf E` are the multisets of positive integers with sum E. -/
theorem mem_map_coe_partsOf {E : ℕ} {τ : Multiset ℕ} : τ ∈ (partsOf E).map (fun L : List ℕ => (L : Multiset ℕ)) ↔ τ.sum = E ∧ 0 ∉ τ := by
  rw [List.mem_map]
  constructor
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨hs, hp, _⟩ := mem_partsOf.1 hL
    refine ⟨by rw [Multiset.sum_coe, hs], fun h0 => ?_⟩
    have := hp 0 (Multiset.mem_coe.1 h0)
    omega
  · rintro ⟨hs, h0⟩
    refine ⟨τ.sort (· ≥ ·), mem_partsOf.2 ⟨?_, fun n hn => ?_, Multiset.pairwise_sort τ _⟩, Multiset.sort_eq τ _⟩
    · rw [← Multiset.sum_coe, Multiset.sort_eq, hs]
    · rw [Multiset.mem_sort] at hn
      exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hn)

/-- As multisets, the members of `partsOf E` are different from each other. -/
theorem nodup_map_coe_partsOf (E : ℕ) : ((partsOf E).map fun L : List ℕ => (L : Multiset ℕ)).Nodup := by
  refine List.Nodup.map_on (fun L hL L' hL' h => ?_) (nodup_partsOf E)
  exact (Multiset.coe_eq_coe.1 h).eq_of_pairwise' (mem_partsOf.1 hL).2.2 (mem_partsOf.1 hL').2.2

/-- There are p(E) of them. -/
theorem length_partsOf (E : ℕ) : (partsOf E).length = Partitions.p E := by
  have h1 : ((partsOf E).map fun L : List ℕ => (L : Multiset ℕ)).toFinset = (univ : Finset (Nat.Partition E)).image fun q => q.parts := by
    ext τ
    rw [List.mem_toFinset, mem_map_coe_partsOf, Finset.mem_image]
    constructor
    · rintro ⟨hs, h0⟩
      exact ⟨⟨τ, fun {i} hi => Nat.pos_of_ne_zero fun h => h0 (h ▸ hi), hs⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨q, _, rfl⟩
      exact ⟨q.parts_sum, fun h0 => absurd (q.parts_pos h0) (lt_irrefl 0)⟩
  have h2 := List.toFinset_card_of_nodup (nodup_map_coe_partsOf E)
  rw [h1, Finset.card_image_of_injective _ fun q q' h => Nat.Partition.ext h, Finset.card_univ, List.length_map] at h2
  exact h2.symm

/-- `partsLe E k` has at most p(E) members. -/
theorem length_partsLe_le (E k : ℕ) : (partsLe E k).length ≤ Partitions.p E := by
  rw [← length_partsOf, ← partsLe_of_le (le_max_right k E)]
  exact length_partsLe_mono E (le_max_left k E)

/-- p(E) ≤ 2^E. -/
theorem p_le_two_pow (E : ℕ) : Partitions.p E ≤ 2 ^ E := by
  rw [← length_partsOf]
  exact (length_partsLe_aux E E).1

end ClauseBound.Part
