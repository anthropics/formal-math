/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.Theorem21b.PathsAndWalks

/-!
# APSP: from a solver of the task to a program for the layout of the end statement

APSP (Theorem 22).  `realized_apsp`: if the task `apTask` is solved in time T, then
`EndStatement.APSP` is solved on the word RAM within a constant times T.

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n².  The
answer goes to the 2n² cells from 1 + 2n², and the free pointer is 1 + 4n² (`apspInst`).  The task
speaks of the graph with weights in `WithTop ℤ` that is read from the two lists, which is the graph
of the instance (`graphOf_apsp`).  So the input meets the task's precondition (`pre_apsp`), and what
a solver leaves in the output cells is what `EndStatement.APSP` asks for (`post_apsp`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The adjacency matrix of an instance, as it is written into the memory. -/
def apspAdj (x : Bounded EndStatement.APSP) : List ℤ :=
  rowMajor fun i j => if (x.x.1 i j).isSome then 1 else 0

/-- The weights of an instance, as they are written into the memory. -/
def apspWeights (x : Bounded EndStatement.APSP) : List ℤ := rowMajor fun i j => (x.x.1 i j).getD 0

/-- The input: the size and the two matrices, row by row. -/
theorem input_apsp (x : Bounded EndStatement.APSP) :
    (ofEnd EndStatement.APSP).input x = (x.n : ℤ) :: (apspAdj x ++ apspWeights x) := by
  simp only [EndStatement.APSP, rowByRow_eq, apspAdj, apspWeights]

/-- The graph that is read from the two lists is the graph of the instance. -/
theorem graphOf_apsp (x : Bounded EndStatement.APSP) :
    graphOf x.n (apspAdj x) (apspWeights x) = fun i j => toTop (x.x.1 i j) := by
  funext i j
  unfold graphOf apspAdj apspWeights
  rw [getD_rowMajor _ i j, getD_rowMajor _ i j]
  cases x.x.1 i j <;> simp [toTop]

/-- The weights are within the bound. -/
theorem abs_le_of_mem_apspWeights (x : Bounded EndStatement.APSP) {a : ℤ} (ha : a ∈ apspWeights x) :
    |a| ≤ (x.U : ℤ) :=
  Bounded.abs_le (by
    simpa only [EndStatement.APSP, rowByRow_eq, apspAdj, apspWeights] using
      List.mem_append_right (apspAdj x) ha)

/-- The instance of the task: where the two matrices and the answer stand. -/
def apspInst (x : Bounded EndStatement.APSP) : GraphInst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), apspAdj x, apspWeights x⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_apsp (x : Bounded EndStatement.APSP) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    apTask.Pre (apspInst x) (memOf ((ofEnd EndStatement.APSP).input x)) (1 + 4 * (x.n * x.n)) := by
  have hA : (apspAdj x).length = x.n * x.n := length_rowMajor _
  rw [input_apsp]
  exact
  { n_pos := hn
    U_pos := hU
    lenADJ := hA
    lenW := length_rowMajor _
    segADJ := seg_first _ _ _
    segW := by
      have := seg_second (x.n : ℤ) (apspAdj x) (apspWeights x)
      rwa [hA] at this
    zeroOne := by
      intro a ha
      obtain ⟨i, j, rfl⟩ := mem_rowMajor ha
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    leW := fun a ha => abs_le_of_mem_apspWeights x ha
    belowADJ := by simp only [apspInst]; omega
    belowW := by simp only [apspInst]; omega
    belowOut := by simp only [apspInst]; omega
    apartADJ := Or.inl (by simp only [apspInst]; omega)
    apartW := Or.inl (by simp only [apspInst]; omega)
    noNegativeCycle :=
      (congrArg NoNegativeCycle (graphOf_apsp x)).mpr (noNegativeCycle_toTop x.x.2) }

/-- What the task leaves in the output cells is a right answer of the end statement's APSP. -/
theorem post_apsp (x : Bounded EndStatement.APSP) (r : ℤ) (μ' : ℕ → ℤ)
    (h : apTask.Post (apspInst x) (memOf ((ofEnd EndStatement.APSP).input x))
      (1 + 4 * (x.n * x.n)) r μ') :
    (ofEnd EndStatement.APSP).IsAnswer x (verdictOf false 1) fun i =>
      μ' (((ofEnd EndStatement.APSP).input x).length + i) := by
  obtain ⟨⟨dist, hdist, hcells⟩, -⟩ := h
  have hdist' : IsDistanceMatrix (fun i j => toTop (x.x.1 i j)) dist :=
    (congrArg (fun w => IsDistanceMatrix w dist) (graphOf_apsp x)).mp hdist
  have hlen : ((ofEnd EndStatement.APSP).input x).length = 1 + 2 * (x.n * x.n) := by
    have hA : (apspAdj x).length = x.n * x.n := length_rowMajor _
    have hB : (apspWeights x).length = x.n * x.n := length_rowMajor _
    rw [input_apsp, List.length_cons, List.length_append, hA, hB]
    omega
  refine ⟨by simp [verdictOf, EndStatement.APSP], output_apsp x.x _ fun i j => ?_⟩
  rw [hlen]
  exact reachable_or_not hdist' (hcells i j).1 (hcells i j).2

/-- What connects APSP in the layout of the end statement with the task.  The program always
accepts: the answer is in the output cells. -/
def wrapApsp : Wrap EndStatement.APSP apTask false where
  args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k 4 *' v 3]
  inst := apspInst
  fr x := 1 + 4 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [apTask, apspInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
  zero x hn _ := ⟨⟨fun _ => trivial, fun _ => rfl⟩, fun i => absurd i.isLt (by omega)⟩
  pre := pre_apsp
  post x r μ' _ h := post_apsp x r μ' h

/-- **APSP**: if the task is solved in time T, then APSP is solved on the word RAM within a constant
times T. -/
theorem realized_apsp (T : ℕ → ℝ → ℝ) (h : SolvedIn apTask T) :
    Realized EndStatement.APSP T :=
  wrapApsp.realized h

end Light.Sec3
