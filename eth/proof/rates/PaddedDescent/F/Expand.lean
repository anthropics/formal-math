/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.SideF

/-! # One level (StE)

The children of an instance on g·g nodes have Z summing to its Z (the sum of the Z_ι over all ι, by
`ZW_eq_sum`), they are well-formed, and there are at most
(Λ+1)^R of them, where R = `nRect` of the side g is the number of rectangles of the g×g grid and Λ
is a given bound on the t of the pieces A_0, …, A_t. -/

public section

namespace PaddedDescent.F.Expand

open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem sum_map_range (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

/-- A filterMap all of whose values are `some`. -/
theorem filterMap_spec {α β : Type} {f : α → Option β} {z : β → ℤ} {v : α → ℤ} {Q : β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, f a = some b ∧ z b = v a ∧ Q b) →
      ((l.filterMap f).map z).sum = (l.map v).sum ∧ (∀ b ∈ l.filterMap f, Q b) ∧ (l.filterMap f).length = l.length
  | [], _ => by simp
  | a :: l, h => by
    obtain ⟨b, h1, h2, h3⟩ := h a List.mem_cons_self
    obtain ⟨i1, i2, i3⟩ := filterMap_spec l fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [List.filterMap_cons, h1]
    refine ⟨by simp [i1, h2], fun c hc => ?_, by simp [i3]⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h3
    · exact i2 c hc

/-- `StE`, one level of the recursion: the children of an instance on g·g nodes are well-formed,
their Z sum to its Z, and there are at most (Λ+1)^R of them (R and Λ as in the module docstring). -/
theorem stE : StE := by
  intro pad L Λ B I hK hg hI hb
  have hpat : (I.1.length + 1) ^ nRect L.2.length ≤ (Λ + 1) ^ nRect L.2.length :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hI.lam_le) _
  obtain ⟨h1, h2, h3⟩ := filterMap_spec (f := childF pad L I) (z := zval L.1.length)
    (v := sideZ L.2.length I.1.length (instOf (K := L.2.length * L.2.length) I.2))
    (Q := WF L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B))
    (List.range ((I.1.length + 1) ^ nRect L.2.length))
    fun y hy => SideF.stChild pad L Λ B I y hK hg hI hb (List.mem_range.1 hy)
  unfold expand
  rw [rng_eq (hpat.trans hb.pat)]
  refine ⟨?_, h2, by rw [h3, List.length_range]; exact hpat⟩
  rw [h1, sum_map_range, zval, ZW_eq_sum]

end PaddedDescent.F.Expand
