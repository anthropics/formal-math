/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs
import Paper.Curvature

/-!
# The exponent of a unit tensor; hyperedges are convex

For a spectral point F over the parties I and a map π : A → I, the number `hexp F π` is the exponent g of the unit tensor
with one leg at π a for every a in A (a hyperedge): F has the value n ^ g at the one of size n. This file has the simple
facts on g (it depends only on the set of parties, it is a distance for two parties, legs can be moved along edges), and the
lemma "hyperedges are convex": if every leg is moved to the midpoint of two places, g is at most the mean of the two values.
-/

namespace Nc.Price

open Ov Finset

section Simple

variable {K : Type} [Field K] {I J A B : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- A spectral point has the value n ^ g at the unit tensor of size n ≥ 1 with
the legs at π. -/
theorem unit_eq_rpow_hexp [Nonempty I] (F : Spec K I) (π : A → I) {n : ℕ} (hn : 1 ≤ n) :
    F.F (Ten.push π (Ten.unit K A n)) = (n : ℝ) ^ hexp F π :=
  F.unit_eq π hn

/-- The case n = 2 of the definition of g. -/
theorem unit_two_eq_rpow_hexp [Nonempty I] (F : Spec K I) (π : A → I) :
    F.F (Ten.push π (Ten.unit K A 2)) = 2 ^ hexp F π := by
  have h := unit_eq_rpow_hexp F π (n := 2) (by norm_num)
  exact_mod_cast h

/-- The exponent of a unit tensor is not negative. -/
theorem hexp_nonneg [Nonempty I] (F : Spec K I) (π : A → I) : 0 ≤ hexp F π :=
  Real.logb_nonneg (by norm_num) (F.one_le_unit π (by norm_num))

/-- The exponent of a unit tensor depends only on the set of the parties that hold
a leg. -/
theorem hexp_congr_range (F : Spec K I) (π : A → I) (π' : B → I) (h : Set.range π = Set.range π') :
    hexp F π = hexp F π' := by
  rw [hexp, hexp, F.congr (Ten.Equi.push_unit_congr π π' h 2)]

/-- For two legs the exponent of the unit tensor is the distance. -/
theorem hexp_pair (F : Spec K I) (p q : I) : hexp F ![p, q] = F.e p q := rfl

/-- If all legs are at one party, the exponent of the unit tensor is at most 0. -/
theorem hexp_const_le (F : Spec K I) (q : I) : hexp F (fun _ : A => q) ≤ 0 :=
  Real.logb_nonpos (by norm_num) (F.nonneg _) (F.push_const_le q _)

/-- If all legs are at the two parties p and q, the exponent of the
unit tensor is at most the distance of p and q. -/
theorem hexp_le_of_two (F : Spec K I) (π : A → I) (p q : I) (h : ∀ a, π a = p ∨ π a = q) :
    hexp F π ≤ F.e p q := by
  by_cases hp : ∀ a, π a = p
  · rw [show π = fun _ => p from funext hp]
    exact (hexp_const_le F p).trans (F.e_nonneg p q)
  by_cases hq : ∀ a, π a = q
  · rw [show π = fun _ => q from funext hq]
    exact (hexp_const_le F q).trans (F.e_nonneg p q)
  push Not at hp hq
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  have ha' : π a = q := (h a).resolve_left ha
  have hb' : π b = p := (h b).resolve_right hb
  rw [← hexp_pair]
  refine (hexp_congr_range F π ![p, q] ?_).le
  ext x
  simp only [Set.mem_range, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact h c
  · rintro (rfl | rfl)
    · exact ⟨b, hb'⟩
    · exact ⟨a, ha'⟩

/-- If the leg a is moved from π' a to π a, the exponent of the unit tensor grows at most
by the sum of the distances. -/
theorem hexp_le_move [Nonempty I] (F : Spec K I) (π π' : A → I) :
    hexp F π ≤ hexp F π' + ∑ a, F.e (π a) (π' a) := by
  have h := F.push_le_move π π' (Ten.unit K A 2)
  have h1 : ∀ a : A, (Fintype.card ((Ten.unit K A 2).ι a) : ℝ) = 2 := fun a => by
    show (Fintype.card (Fin 2) : ℝ) = 2
    simp
  simp only [h1] at h
  rw [unit_two_eq_rpow_hexp, unit_two_eq_rpow_hexp, ← Real.rpow_sum_of_pos (by norm_num),
    ← Real.rpow_add (by norm_num)] at h
  have h2 := (Real.rpow_le_rpow_left_iff (by norm_num)).1 h
  linarith

/-- The exponents of unit tensors for a pull-back of a spectral point. -/
theorem hexp_pull (F : Spec K I) (f : J → I) (π : A → J) : hexp (F.pull f) π = hexp F (f ∘ π) := by
  rw [hexp, hexp, Spec.pull_F, F.congr (Ten.Equi.push_push f π _)]

end Simple

end Nc.Price
