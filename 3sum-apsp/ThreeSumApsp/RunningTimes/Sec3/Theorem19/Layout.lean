/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Tasks

/-!
# Exact Triangle: from a solver of the task to a program for the layout of the end statement

Exact Triangle (Theorem 19).  `realized_exactTriangle`: if the task `etTask` is solved in
time T, then `EndStatement.ExactTriangle` is solved on the word RAM within a constant times T.

The input is n in cell 0 and the three matrices of weights from the cells 1, 1 + n² and 1 + 2n²; the
free pointer is 1 + 3n² (`triangleInst`).  The task speaks of the instance that is read from the
three lists, which is the instance itself (`triOf_rowMajor`).  So the input meets the task's
precondition (`pre_exactTriangle`), and the result of a solver is the right verdict
(`post_exactTriangle`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The instance that is read from the three lists is the instance. -/
theorem triOf_rowMajor {n : ℕ} (T : TriangleInstance ℤ n) :
    triOf n (rowMajor T.wAB) (rowMajor T.wBC) (rowMajor T.wAC) = T := by
  cases T with
  | mk wAB wBC wAC =>
    unfold triOf
    congr 1 <;> funext i j <;> exact getD_rowMajor _ i j

/-- The input: the size and the three matrices, row by row. -/
theorem input_exactTriangle (x : Bounded EndStatement.ExactTriangle) :
    (ofEnd EndStatement.ExactTriangle).input x =
      (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2) := by
  simp only [EndStatement.ExactTriangle, rowByRow_eq]

/-- The entries of the three matrices are within the bound. -/
theorem abs_le_of_mem_exactTriangle (x : Bounded EndStatement.ExactTriangle) {a : ℤ}
    (ha : a ∈ rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2) : |a| ≤ (x.U : ℤ) :=
  Bounded.abs_le (by simpa only [EndStatement.ExactTriangle, rowByRow_eq] using ha)

/-- The instance of the task: where the three matrices stand. -/
def triangleInst (x : Bounded EndStatement.ExactTriangle) : etTask.Inst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), rowMajor x.x.1, rowMajor x.x.2.1,
    rowMajor x.x.2.2⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_exactTriangle (x : Bounded EndStatement.ExactTriangle) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    etTask.Pre (triangleInst x) (memOf ((ofEnd EndStatement.ExactTriangle).input x))
      (1 + 3 * (x.n * x.n)) := by
  have hAB : (rowMajor x.x.1).length = x.n * x.n := length_rowMajor _
  have hBC : (rowMajor x.x.2.1).length = x.n * x.n := length_rowMajor _
  rw [input_exactTriangle]
  exact triPre_of_arrays (base := 1) hn hU
    { len := hAB
      seg := by
        have := seg_first (x.n : ℤ) (rowMajor x.x.1) (rowMajor x.x.2.1 ++ rowMajor x.x.2.2)
        rwa [← List.append_assoc] at this
      bound := fun a (ha : a ∈ rowMajor x.x.1) => abs_le_of_mem_exactTriangle x (by simp [ha]) }
    { len := hBC
      seg := by
        have := seg_memOf ((x.n : ℤ) :: rowMajor x.x.1) (rowMajor x.x.2.1) (rowMajor x.x.2.2)
        rwa [List.length_cons, hAB, Nat.add_comm] at this
      bound := fun a (ha : a ∈ rowMajor x.x.2.1) => abs_le_of_mem_exactTriangle x (by simp [ha]) }
    { len := length_rowMajor _
      seg := by
        have := seg_second (x.n : ℤ) (rowMajor x.x.1 ++ rowMajor x.x.2.1) (rowMajor x.x.2.2)
        rwa [List.length_append, hAB, hBC, ← Nat.two_mul] at this
      bound := fun a (ha : a ∈ rowMajor x.x.2.2) => abs_le_of_mem_exactTriangle x (by simp [ha]) }

/-- The result of a solver of the task is the right verdict of the end statement's Exact
Triangle. -/
theorem post_exactTriangle (x : Bounded EndStatement.ExactTriangle) (r : ℤ) (μ' : ℕ → ℤ)
    (h : etTask.Post (triangleInst x) (memOf ((ofEnd EndStatement.ExactTriangle).input x))
      (1 + 3 * (x.n * x.n)) r μ') :
    (ofEnd EndStatement.ExactTriangle).IsAnswer x (verdictOf true r) fun i =>
      μ' (((ofEnd EndStatement.ExactTriangle).input x).length + i) := by
  obtain ⟨rfl, -⟩ := h
  exact ⟨(verdictOf_flag _).trans (iff_of_eq (congrArg TriangleInstance.HasZeroTriangle
    (triOf_rowMajor ⟨x.x.1, x.x.2.1, x.x.2.2⟩))), trivial⟩

/-- What connects Exact Triangle in the layout of the end statement with the task. -/
noncomputable def wrapTriangle : Wrap EndStatement.ExactTriangle etTask true where
  args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k 3 *' v 3]
  inst := triangleInst
  fr x := 1 + 3 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [etTask, triangleInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
  zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨a, _⟩ => absurd a.isLt (by omega)⟩, trivial⟩
  pre := pre_exactTriangle
  post x r μ' _ h := post_exactTriangle x r μ' h

/-- **Exact Triangle**: if the task is solved in time T, then Exact Triangle is solved on the word
RAM within a constant times T. -/
theorem realized_exactTriangle (T : ℕ → ℝ → ℝ) (h : SolvedIn etTask T) :
    Realized EndStatement.ExactTriangle T :=
  wrapTriangle.realized h

end Light.Sec3
