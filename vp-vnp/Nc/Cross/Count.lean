/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cross.Near

/-!
# The number of states: lemmas

Lemmas for Paper.lem_count (Paper/States.lean): gluing `k` sets along the residues modulo `k`, and the sets of bounded
energy.
-/

namespace Nc.Cross

open Finset

/-- Glue `k` sets along the residues modulo `k`. -/
def glueSet (k : ℕ) (I : Fin k → Finset ℕ) : Finset ℕ :=
  univ.biUnion fun r => (I r).image fun i => k * i + r

theorem mem_glueSet {k : ℕ} (I : Fin k → Finset ℕ) (r : Fin k) (i : ℕ) :
    k * i + r ∈ glueSet k I ↔ i ∈ I r := by
  have hk : 0 < k := r.pos
  unfold glueSet
  simp only [mem_biUnion, mem_univ, true_and, mem_image]
  refine ⟨?_, fun h => ⟨r, i, h, rfl⟩⟩
  rintro ⟨r', i', hi', h⟩
  have h1 : (r' : ℕ) = r := by
    have := congrArg (· % k) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using this
  have h2 : r' = r := Fin.ext h1
  subst h2
  have h3 : i' = i := Nat.eq_of_mul_eq_mul_left hk (by omega)
  exact h3 ▸ hi'

theorem glueSet_injective {k : ℕ} : Function.Injective (glueSet k) := by
  intro I I' h
  funext r
  ext i
  rw [← mem_glueSet I r i, h, mem_glueSet]

theorem sum_glueSet {k : ℕ} (I : Fin k → Finset ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ glueSet k I, f n = ∑ r, ∑ i ∈ I r, f (k * i + r) := by
  unfold glueSet
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left r.pos (by simpa using hij)
  · intro r _ r' _ hrr'
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hn
    obtain ⟨i', -, h⟩ := mem_image.1 hn'
    apply hrr'
    have := congrArg (· % k) h
    refine Fin.ext ?_
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using this.symm

theorem card_glueSet {k : ℕ} (I : Fin k → Finset ℕ) : (glueSet k I).card = ∑ r, (I r).card := by
  have := sum_glueSet I fun _ => 1
  simpa using this

theorem en_glueSet {k : ℕ} (s : Fin k → Finset ℕ × Finset ℕ) (h : ∀ r, (s r).1.card = (s r).2.card) :
    en (glueSet k fun r => (s r).1) + en (glueSet k fun r => (s r.rev).2) =
      k * ∑ r, (en (s r).1 + en (s r).2) := by
  have e1 : en (glueSet k fun r => (s r.rev).2) = ∑ r : Fin k, ∑ i ∈ (s r).2, (2 * (k * i + (r.rev : Fin k)) + 1) := by
    rw [en, sum_glueSet]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun r => ?_
    simp
  rw [e1, en, sum_glueSet, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : ((r.rev : Fin k) : ℕ) + r + 1 = k := by
    rw [Fin.val_rev]
    omega
  have a1 : ∑ i ∈ (s r).1, (2 * (k * i + r) + 1) = k * ∑ i ∈ (s r).1, 2 * i + (s r).1.card * (2 * r + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a2 : ∑ i ∈ (s r).2, (2 * (k * i + (r.rev : Fin k)) + 1) =
      k * ∑ i ∈ (s r).2, 2 * i + (s r).2.card * (2 * (r.rev : Fin k) + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a3 : ∀ S : Finset ℕ, en S = ∑ i ∈ S, 2 * i + S.card := by
    intro S
    rw [en, Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  rw [a1, a2, a3, a3, ← h r]
  have : (2 * (r : ℕ) + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1) = 2 * k := by omega
  calc k * ∑ i ∈ (s r).1, 2 * i + (s r).1.card * (2 * ↑r + 1) +
        (k * ∑ i ∈ (s r).2, 2 * i + (s r).1.card * (2 * ((r.rev : Fin k) : ℕ) + 1))
      = k * ∑ i ∈ (s r).1, 2 * i + k * ∑ i ∈ (s r).2, 2 * i +
        (s r).1.card * ((2 * ↑r + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1)) := by ring
    _ = _ := by rw [this]; ring

theorem pairs_mono {E E' : ℕ} (h : E ≤ E') : pairs E ⊆ pairs E' := fun s hs => by
  rw [mem_pairs] at hs ⊢
  exact ⟨hs.1, hs.2.trans h⟩

theorem pairs_pos (E : ℕ) : 0 < (pairs E).card :=
  Finset.card_pos.2 ⟨(∅, ∅), mem_pairs.2 ⟨rfl, by simp [en]⟩⟩

theorem two_le_pairs : 2 ≤ (pairs 2).card := by
  have : ({(∅, ∅), ({0}, {0})} : Finset (Finset ℕ × Finset ℕ)) ⊆ pairs 2 := by
    intro s hs
    rw [mem_insert, mem_singleton] at hs
    rw [mem_pairs]
    rcases hs with rfl | rfl <;> simp [en]
  refine le_trans ?_ (card_le_card this)
  rw [card_insert_of_notMem, card_singleton]
  simp

/-- The sets of energy at most `E`. -/
def sets (E : ℕ) : Finset (Finset ℕ) := (range E).powerset.filter fun S => en S ≤ E

/-- "A state is a pair of such sets." -/
theorem card_pairs_le (E : ℕ) : (pairs E).card ≤ (sets E).card * (sets E).card := by
  rw [← card_product]
  refine card_le_card fun s hs => ?_
  unfold pairs at hs
  rw [mem_filter, mem_product] at hs
  rw [mem_product, sets, mem_filter, mem_filter]
  exact ⟨⟨hs.1.1, by omega⟩, hs.1.2, by omega⟩

/-- The logarithm of the number of states. -/
noncomputable def lp (E : ℕ) : ℝ := Real.log (pairs E).card

theorem lp_nonneg (E : ℕ) : 0 ≤ lp E := Real.log_natCast_nonneg _

theorem lp_zero : lp 0 = 0 := by
  have : pairs 0 = {(∅, ∅)} := by
    ext s
    rw [mem_pairs, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      have h1 : s.1 = ∅ := by
        by_contra hne
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
        exact absurd (lt_of_mem_en (E := 0) (by omega) hi) (by omega)
      have h2 : s.2 = ∅ := by
        by_contra hne
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
        exact absurd (lt_of_mem_en (E := 0) (by omega) hi) (by omega)
      exact Prod.ext h1 h2
    · rintro rfl
      simp [en]
  rw [lp, this]
  simp

theorem lp_mono {E E' : ℕ} (h : E ≤ E') : lp E ≤ lp E' :=
  Real.log_le_log (by exact_mod_cast pairs_pos E) (by exact_mod_cast card_le_card (pairs_mono h))

end Nc.Cross
