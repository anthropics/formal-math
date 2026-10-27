/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.Code

/-! `Network.pull`: a network carried to words of bits along codes (`Code`) of its states and
labels.
A network has nodes with finite sets of states and integer weights W, and for every
pair of nodes an interaction Ψ that is a sum over labels.
Pulling keeps the capacities, hence U; it keeps the value if every word names a state, and the
bounds `Sized P B` if the names
of the states have at most P bits. -/

namespace Groundwork

open Finset

namespace Network

variable {J σ τ : Type*}

/-- The network on words: states of a are the words of length n a, labels of {a,b} the words of
length c a b;
the factors vanish at the words that name no label. cl a b is read at a ≤ b only. -/
@[expose] public def pull [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
    (cl : ∀ a b, Code (N.Θ a b) (N.c a b)) : Network J (List Bool) (List Bool) where
  S a := words (n a)
  W a z := N.W a ((cs a).dec z)
  Θ a b := words (N.c a b)
  f a b z θ := if θ ∈ (cl (min a b) (max a b)).D then N.f a b ((cs a).dec z) ((cl (min a b) (max a b)).dec θ) else 0
  c := N.c

variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))

omit [Fintype J] in
public theorem Ψ_pull (a b : J) (z z' : List Bool) :
    (N.pull n cs cl).Ψ a b z z' = N.Ψ a b ((cs a).dec z) ((cs b).dec z') := by
  unfold Ψ
  simp only [lab, pull]
  rw [min_comm b a, max_comm b a, ← (cl (min a b) (max a b)).sum_words]
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs <;> simp

/-- A sum over tuples of elements is the sum over the tuples of their names. -/
theorem sum_pi_dec {S : J → Finset σ} (cs : ∀ a, Code (S a) (n a)) (F : (J → σ) → ℤ) :
    ∑ z ∈ Fintype.piFinset fun a => (cs a).D, F (fun a => (cs a).dec (z a)) = ∑ x ∈ Fintype.piFinset S, F x := by
  refine Finset.sum_nbij (fun z a => (cs a).dec (z a)) ?_ ?_ ?_ fun _ _ => rfl
  · intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    exact fun a => (cs a).bij.mapsTo (hz a)
  · intro z hz z' hz' h
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hz hz'
    funext a
    exact (cs a).bij.injOn (hz a) (hz' a) (congrFun h a)
  · intro x hx
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hx
    choose w hw hwx using fun a => (cs a).bij.surjOn (hx a)
    exact ⟨w, by rw [Finset.mem_coe, Fintype.mem_piFinset]; exact hw, funext hwx⟩

/-- If every word of length n a names a state of a (the codes cs are full), the pulled network has
the value of N. -/
public theorem value_pull (h : ∀ a, (cs a).Full) : (N.pull n cs cl).value = N.value := by
  unfold value
  simp only [Ψ_pull]
  rw [← sum_pi_dec n cs]
  have hS : (N.pull n cs cl).S = fun a => (cs a).D := funext fun a => (h a).symm
  rw [hS]
  rfl

public theorem lab_pull {P B : ℕ} (h : N.Sized P B) (a b : J) : (N.pull n cs cl).lab a b = words (N.c a b) := by
  simp only [lab, pull]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab, h.c_symm]

/-- The pulled network has the size of N as soon as the names of the states have at most P bits. -/
public theorem sized_pull_of_le {P B : ℕ} (h : N.Sized P B) (hn : ∀ a, n a ≤ P) : (N.pull n cs cl).Sized P B := by
  refine ⟨⟨fun a => ?_, h.c_symm, h.sum_c, fun a b _ => ?_⟩, fun a z => h.abs_W _ _, fun a b z θ => ?_,
    fun a b z z' hab => ?_⟩
  · change #(words (n a)) ≤ 2 ^ P
    rw [card_words]
    exact Nat.pow_le_pow_right (by norm_num) (hn a)
  · rw [lab_pull N n cs cl h, card_words]
    exact le_rfl
  · simp only [pull]
    split_ifs
    · exact h.abs_f _ _ _ _
    · simp
  · rw [Ψ_pull]
    exact h.abs_Ψ _ _ _ _ hab

end Network

end Groundwork
