/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Net
public import StepMachines.Prog.Chunks

/-! Codes: finite sets named by words of a given length, and the first ways to make one (all words,
another way to write the set
or the length, a bijection, the empty set, pairs). -/

namespace Groundwork

open Finset

variable {X Y : Type*}

/-- A code of the finite set S by words of length n: the words of D name the elements of S, one
each, through dec. -/
public structure Code (S : Finset X) (n : ℕ) where
  D : Finset (List Bool)
  dec : List Bool → X
  len : ∀ w ∈ D, w.length = n
  bij : Set.BijOn dec D S

namespace Code

variable {S : Finset X} {n : ℕ}

/-- Every word of length n is a name. -/
@[expose] public def Full (c : Code S n) : Prop := c.D = words n

public theorem D_subset (c : Code S n) : c.D ⊆ words n := fun w hw => mem_words.2 (c.len w hw)

theorem image_dec [DecidableEq X] (c : Code S n) : c.D.image c.dec = S :=
  Finset.coe_injective (by rw [coe_image]; exact c.bij.image_eq)

public theorem card_D (c : Code S n) : #c.D = #S := by
  classical
  exact (card_image_of_injOn c.bij.injOn).symm.trans (congrArg card c.image_dec)

public theorem card_le (c : Code S n) : #S ≤ 2 ^ n := by
  rw [← c.card_D, ← card_words]
  exact card_le_card c.D_subset

/-- A sum over S is the sum over the names. -/
public theorem sum_dec {M : Type*} [AddCommMonoid M] (c : Code S n) (F : X → M) :
    ∑ w ∈ c.D, F (c.dec w) = ∑ x ∈ S, F x := by
  classical
  conv_rhs => rw [← c.image_dec]
  exact (sum_image c.bij.injOn).symm

/-- The same, over all words of length n. -/
public theorem sum_words {M : Type*} [AddCommMonoid M] (c : Code S n) (F : X → M) :
    ∑ w ∈ words n, (if w ∈ c.D then F (c.dec w) else 0) = ∑ x ∈ S, F x := by
  rw [sum_ite_mem, inter_eq_right.2 c.D_subset, c.sum_dec]

/-- The words of length n name themselves. -/
@[expose] public def word (n : ℕ) : Code (words n) n where
  D := words n
  dec := id
  len _ h := mem_words.1 h
  bij := Set.bijOn_id _

/-- The same names for another set and length, equal to the given ones. -/
@[expose] public def cast (c : Code S n) {S' : Finset X} {n' : ℕ} (hS : S = S') (hn : n = n') : Code S' n' where
  D := c.D
  dec := c.dec
  len := hn ▸ c.len
  bij := hS ▸ c.bij

/-- Names carried along a bijection φ of S with S'. -/
@[expose] public def map (c : Code S n) (φ : X → Y) (S' : Finset Y) (h : Set.BijOn φ S S') : Code S' n where
  D := c.D
  dec := φ ∘ c.dec
  len := c.len
  bij := h.comp c.bij

/-- No element. -/
@[expose] public def empty (x : X) (n : ℕ) : Code (∅ : Finset X) n where
  D := ∅
  dec _ := x
  len := by simp
  bij := by simp

/-- Pairs: the two names one after the other. -/
@[expose] public def prod {S₁ : Finset X} {S₂ : Finset Y} {n₁ n₂ : ℕ} (c₁ : Code S₁ n₁) (c₂ : Code S₂ n₂) :
    Code (S₁ ×ˢ S₂) (n₁ + n₂) where
  D := (words (n₁ + n₂)).filter fun w => w.take n₁ ∈ c₁.D ∧ w.drop n₁ ∈ c₂.D
  dec w := (c₁.dec (w.take n₁), c₂.dec (w.drop n₁))
  len w h := mem_words.1 (mem_filter.1 h).1
  bij := by
    refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun x hx => ?_⟩
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      exact mem_coe.2 (mem_product.2 ⟨c₁.bij.mapsTo hw.1, c₂.bij.mapsTo hw.2⟩)
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      have hw' := (mem_filter.1 (mem_coe.1 hw')).2
      rw [Prod.mk.injEq] at h
      rw [← List.take_append_drop n₁ w, c₁.bij.injOn hw.1 hw'.1 h.1, c₂.bij.injOn hw.2 hw'.2 h.2,
        List.take_append_drop]
    · obtain ⟨hx₁, hx₂⟩ := mem_product.1 (mem_coe.1 hx)
      obtain ⟨w₁, hw₁, e₁⟩ := c₁.bij.surjOn hx₁
      obtain ⟨w₂, hw₂, e₂⟩ := c₂.bij.surjOn hx₂
      have l₁ := c₁.len w₁ hw₁
      have l₂ := c₂.len w₂ hw₂
      have t : (w₁ ++ w₂).take n₁ = w₁ := by rw [← l₁, List.take_left]
      have d : (w₁ ++ w₂).drop n₁ = w₂ := by rw [← l₁, List.drop_left]
      refine ⟨w₁ ++ w₂, mem_coe.2 (mem_filter.2 ⟨mem_words.2 (by rw [List.length_append, l₁, l₂]), ?_, ?_⟩), ?_⟩
      · rw [t]; exact hw₁
      · rw [d]; exact hw₂
      · simp only [t, d, e₁, e₂]

public theorem full_cast (c : Code S n) {S' : Finset X} {n' : ℕ} (hS : S = S') (hn : n = n') (h : c.Full) :
    (c.cast hS hn).Full := by
  subst hn
  exact h

end Code

end Groundwork
