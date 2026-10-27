/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.Defs

/-! # Padding changes neither the value nor the total

Let the network N be the network N₀ with padded settings (`Coding.PaddingOf`,
proof/networks/Coding/Defs.lean). The value of a network (Section 3) is a sum over all choices of
one setting for each node. A choice for N in which some node has a setting that is not the padding
of any setting of N₀ contributes 0, because W is 0 there.
The other choices are, one to one, the choices for N₀ with each setting padded, and they contribute
the same term. The total is a sum of the numbers c_{a,b}, which are the same. -/

public section

namespace Coding

open Finset Groundwork Eight.SecNetworks

/-- **Padding changes neither the value nor the total.** Used for «A setting z_a of node a is a bit
string with one bit z_a[o] for each occurrence o in cluster a» (Section 6), where Lean's settings
have one bit for each place of a literal. -/
theorem stPaddingValue : StPaddingValue := by
  intro g N₀ N pad h
  constructor
  · classical
    unfold Net.value
    have hinj : Set.InjOn (fun (z : Fin g → List Bool) a => pad a (z a)) (Fintype.piFinset N₀.S) := by
      intro z hz z' hz' e
      funext a
      exact h.inj a (z a) (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz) a) (z' a) (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz') a) (congrFun e a)
    have hsub : (Fintype.piFinset N₀.S).image (fun z a => pad a (z a)) ⊆ Fintype.piFinset N.S := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact Fintype.mem_piFinset.2 fun a => h.maps a _ (Fintype.mem_piFinset.1 hz a)
    rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
    · refine Finset.sum_congr rfl fun z hz => ?_
      have hz' := Fintype.mem_piFinset.1 hz
      congr 1
      · exact Finset.prod_congr rfl fun a _ => h.W a _ (hz' a)
      · exact Finset.prod_congr rfl fun p hp => h.Ψ p.1 p.2 (ne_of_lt (Finset.mem_filter.1 hp).2) _ (hz' _) _ (hz' _)
    · intro y hy hny
      obtain ⟨a, ha⟩ : ∃ a, ∀ z ∈ N₀.S a, pad a z ≠ y a := by
        by_contra hcon
        push Not at hcon
        choose z hz hzy using hcon
        exact hny (Finset.mem_image.2 ⟨z, Fintype.mem_piFinset.2 hz, funext hzy⟩)
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (h.off a _ (Fintype.mem_piFinset.1 hy a) ha), zero_mul]
  · unfold Net.U
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => h.c a b (Finset.ne_of_mem_erase hb).symm

end Coding
