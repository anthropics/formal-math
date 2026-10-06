/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary39.GraphH.Build

/-!
# Corollary 39 in the light language: the number of pairs of parts

The three lists of pairs of parts together have (k choose 2) pairs: every pair of parts is counted
in exactly one of the three weight matrices of H.
-/

public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.KClique Finset

/-- The pairs in a union of a and b elements: within the first set, across, and within the second
set. -/
theorem add_choose_two (a b : ℕ) : (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_succ_succ b 1, ih, Nat.choose_one_right,
      Nat.choose_one_right]
    ring

/-- The number of indices above j. -/
theorem length_filter_lt {m : ℕ} (j : Fin m) :
    ((List.finRange m).filter fun j' => j < j').length = m - 1 - j := by
  have h := List.sum_filter_finRange (fun j' : Fin m => j < j') (fun _ => (1 : ℤ))
  have h2 : (univ.filter fun j' : Fin m => j < j') = Finset.Ioi j := by
    ext x; simp
  rw [h2] at h
  simp only [List.map_const', List.sum_replicate, Finset.sum_const, Fin.card_Ioi, nsmul_eq_mul,
    mul_one] at h
  exact_mod_cast h

/-- The number of pairs j < j' below m. -/
theorem length_upper {m : ℕ} {β : Type} (f : Fin m → Fin m → β) :
    ((List.finRange m).flatMap fun j =>
      ((List.finRange m).filter fun j' => j < j').map (f j)).length = m.choose 2 := by
  rw [List.length_flatMap]
  simp only [List.length_map, length_filter_lt]
  have h1 : ((List.finRange m).map fun j : Fin m => m - 1 - (j : ℕ)).sum =
      ∑ j : Fin m, (m - 1 - (j : ℕ)) :=
    (Fin.sum_univ_def _).symm
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => m - 1 - j) m, Finset.sum_range_reflect (fun j => j) m,
    Finset.sum_range_id, Nat.choose_two_right]

/-- The number of pairs of parts that contribute to the weight matrix number i of H. -/
theorem length_pairsH (k : ℕ) (i : Fin 3) :
    (pairsH k i).length = width k * width k + (width k).choose 2 + numFixed k * width k +
      if i = 0 then (numFixed k).choose 2 else 0 := by
  unfold pairsH
  rw [List.length_append, List.length_append, List.length_append,
    List.length_flatMap_finRange (k := width k) _ fun _ => by simp, length_upper,
    List.length_flatMap_finRange (k := width k) _ fun _ => by simp]
  split_ifs
  · rw [length_upper]
  · rfl

/-- Every pair of parts is counted once. -/
theorem lenH_eq_choose (k : ℕ) : lenH k = k.choose 2 := by
  unfold lenH
  rw [length_pairsH, length_pairsH, length_pairsH]
  conv_rhs =>
    rw [← three_width_add k,
      show numFixed k + 3 * width k = ((numFixed k + width k) + width k) + width k by ring]
  rw [add_choose_two, add_choose_two, add_choose_two]
  simp
  ring

end Light.Sec5
