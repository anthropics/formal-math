/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.RowMajor

/-!
# The input of a thin matrix product in the memory

The trusted layout of the data structures of Section 4 is N, D, further parameters, X, Y, written
from cell 0 on. This file says where each part stands (`thinPair_cellN`, `thinPair_cellD`,
`thinPair_matAt_X`, `thinPair_matAt_Y`), how long the input is
(`length_thinPair_input`), and that all its numbers fit in a word if N, D, the parameters and the
bound on the entries do (`abs_thinPair_input_le`).

The offline problems have the layout N, D, |W|, further parameters, X, Y, the rows of the wanted
positions, their columns. The lemmas `thinInstance_…` say the same about it.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

variable (x : ThinPair) (extra : List ℤ)

theorem length_thinPair_input :
    (x.input extra).length = 2 + extra.length + x.N * x.D + x.N * x.D := by
  have lX : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
  have lY : (rowMajor x.Y).length = x.D * x.N := length_rowMajor _
  simp only [ThinPair.input, List.length_append, List.length_cons, List.length_nil, lX, lY]
  rw [Nat.mul_comm x.D x.N]

theorem thinPair_cellN : memOf (x.input extra) 0 = x.N := rfl

theorem thinPair_cellD : memOf (x.input extra) 1 = x.D := rfl

/-- X stands behind the parameters. -/
theorem thinPair_matAt_X : MatAt (memOf (x.input extra)) (2 + extra.length) x.X :=
  matAt_of_seg (by
    have h := seg_memOf ([(x.N : ℤ), (x.D : ℤ)] ++ extra) (rowMajor x.X) (rowMajor x.Y)
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    exact h)

/-- Y stands behind X. -/
theorem thinPair_matAt_Y : MatAt (memOf (x.input extra)) (2 + extra.length + x.N * x.D) x.Y :=
  matAt_of_seg (by
    have lX : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
    have h := seg_memOf ([(x.N : ℤ), (x.D : ℤ)] ++ extra ++ rowMajor x.X) (rowMajor x.Y) []
    simp only [List.length_append, List.length_cons, List.length_nil, lX, List.append_nil] at h
    exact h)

variable {x extra}

/-- All numbers of the input fit in a word. -/
theorem abs_thinPair_input_le {w : ℤ} (hN : (x.N : ℤ) ≤ w) (hD : (x.D : ℤ) ≤ w) (hU : (x.U : ℤ) ≤ w)
    (hextra : ∀ v ∈ extra, |v| ≤ w) : ∀ v ∈ x.input extra, |v| ≤ w := by
  intro v hv
  simp only [ThinPair.input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (((rfl | rfl) | hv) | hv) | hv
  · rwa [abs_of_nonneg (by positivity)]
  · rwa [abs_of_nonneg (by positivity)]
  · exact hextra v hv
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    exact (x.boundX i j).trans hU
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    exact (x.boundY i j).trans hU

/-! ## The offline layout -/

section
variable (x : ThinInstance) (extra : List ℤ)

theorem length_thinInstance_input : (x.input extra).length
    = 3 + extra.length + x.N * x.D + x.N * x.D + x.W.length + x.W.length := by
  have lX : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
  have lY : (rowMajor x.Y).length = x.D * x.N := length_rowMajor _
  simp only [ThinInstance.input, List.length_append, List.length_cons, List.length_nil,
    List.length_map, lX, lY]
  rw [Nat.mul_comm x.D x.N]

/-- X stands behind the parameters. -/
theorem thinInstance_matAt_X : MatAt (memOf (x.input extra)) (3 + extra.length) x.X :=
  matAt_of_seg (by
    have h := seg_memOf ([(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra) (rowMajor x.X)
      (rowMajor x.Y ++ x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map (fun q => (q.2.val : ℤ)))
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    simpa only [ThinInstance.input, List.append_assoc] using h)

/-- Y stands behind X. -/
theorem thinInstance_matAt_Y : MatAt (memOf (x.input extra)) (3 + extra.length + x.N * x.D) x.Y :=
  matAt_of_seg (by
    have lX : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
    have h := seg_memOf ([(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra ++ rowMajor x.X)
      (rowMajor x.Y) (x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map (fun q => (q.2.val : ℤ)))
    simp only [List.length_append, List.length_cons, List.length_nil, lX] at h
    simpa only [ThinInstance.input, List.append_assoc] using h)

/-- The rows of the wanted positions stand behind Y. -/
theorem thinInstance_seg_rows : Seg (memOf (x.input extra))
    (3 + extra.length + x.N * x.D + x.N * x.D) (x.W.map fun q => ((q.1 : ℕ) : ℤ)) := by
  have lX : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
  have lY : (rowMajor x.Y).length = x.N * x.D := by rw [Nat.mul_comm]; exact length_rowMajor _
  have h := seg_memOf ([(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra ++ rowMajor x.X ++
    rowMajor x.Y) (x.W.map (fun q => (q.1.val : ℤ))) (x.W.map (fun q => (q.2.val : ℤ)))
  simp only [List.length_append, List.length_cons, List.length_nil, lX, lY] at h
  exact h

/-- Their columns stand behind the rows. -/
theorem thinInstance_seg_cols : Seg (memOf (x.input extra))
    (3 + extra.length + x.N * x.D + x.N * x.D + x.W.length) (x.W.map fun q => ((q.2 : ℕ) : ℤ)) := by
  have lX : (rowMajor x.X).length = x.N * x.D := length_rowMajor _
  have lY : (rowMajor x.Y).length = x.N * x.D := by rw [Nat.mul_comm]; exact length_rowMajor _
  have h := seg_memOf ([(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra ++ rowMajor x.X ++
    rowMajor x.Y ++ x.W.map (fun q => (q.1.val : ℤ))) (x.W.map (fun q => (q.2.val : ℤ))) []
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, lX, lY,
    List.append_nil] at h
  exact h

variable {x extra}

/-- All numbers of the input fit in a word. -/
theorem abs_thinInstance_input_le {w : ℤ} (hN : (x.N : ℤ) ≤ w) (hD : (x.D : ℤ) ≤ w)
    (hW : (x.W.length : ℤ) ≤ w) (hU : (x.U : ℤ) ≤ w) (hextra : ∀ v ∈ extra, |v| ≤ w) :
    ∀ v ∈ x.input extra, |v| ≤ w := by
  have hlt : ∀ i : Fin x.N, |((i : ℕ) : ℤ)| ≤ w := fun i => by
    rw [abs_of_nonneg (by positivity)]
    exact le_trans (by exact_mod_cast i.isLt.le) hN
  intro v hv
  simp only [ThinInstance.input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hv
  rcases hv with (((((rfl | rfl | rfl) | hv) | hv) | hv) | ⟨q, -, rfl⟩) | ⟨q, -, rfl⟩
  · rwa [abs_of_nonneg (by positivity)]
  · rwa [abs_of_nonneg (by positivity)]
  · rwa [abs_of_nonneg (by positivity)]
  · exact hextra v hv
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    exact (x.boundX i j).trans hU
  · obtain ⟨i, j, rfl⟩ := mem_rowMajor hv
    exact (x.boundY i j).trans hU
  · exact hlt q.1
  · exact hlt q.2

end

end Light.Sec4
