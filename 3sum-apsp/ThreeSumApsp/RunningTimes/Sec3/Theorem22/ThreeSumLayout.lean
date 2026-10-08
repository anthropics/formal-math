/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Tasks

/-!
# 3SUM: from a solver of the task to a program for the layout of the end statement

3SUM (Theorem 22).  `realized_threeSum`: if the task `s3Task` is solved in time T, then
`EndStatement.ThreeSum` is solved on the word RAM within a constant times T.

The input is n in cell 0 and the n numbers in the cells 1, …, n; the free pointer is n + 1
(`threeSumInst`).  The task speaks of the vector that is read from the list of the numbers, which is
the vector of the instance (`vecOf_ofFn`).  So the input meets the task's precondition
(`pre_threeSum`), and the result of a solver is the right verdict (`post_threeSum`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The numbers of a list made from a function are the values of the function. -/
theorem vecOf_ofFn {n : ℕ} (x : Fin n → ℤ) : vecOf n (List.ofFn x) = x := by
  funext i
  simp [vecOf, List.getD_eq_getElem?_getD]

/-- The instance of the task: the numbers stand from cell 1 on. -/
def threeSumInst (x : Bounded EndStatement.ThreeSum) : s3Task.Inst := ⟨x.n, x.U, 1, List.ofFn x.x⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_threeSum (x : Bounded EndStatement.ThreeSum) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    s3Task.Pre (threeSumInst x) (memOf ((ofEnd EndStatement.ThreeSum).input x)) (x.n + 1) where
  N_pos := hn
  U_pos := hU
  len := List.length_ofFn (f := x.x)
  seg := by
    simpa [EndStatement.ThreeSum, threeSumInst] using seg_memOf [(x.n : ℤ)] (List.ofFn x.x) []
  le := fun _ ha => Bounded.abs_le ha
  below := (Nat.add_comm 1 x.n).le

/-- The result of a solver of the task is the right verdict of the end statement's 3SUM. -/
theorem post_threeSum (x : Bounded EndStatement.ThreeSum) (r : ℤ) (μ' : ℕ → ℤ)
    (h : s3Task.Post (threeSumInst x) (memOf ((ofEnd EndStatement.ThreeSum).input x)) (x.n + 1) r
      μ') :
    (ofEnd EndStatement.ThreeSum).IsAnswer x (verdictOf true r) fun i =>
      μ' (((ofEnd EndStatement.ThreeSum).input x).length + i) := by
  obtain ⟨rfl, -⟩ := h
  exact ⟨(verdictOf_flag _).trans (iff_of_eq (congrArg ThreeSum (vecOf_ofFn x.x))), trivial⟩

/-- What connects 3SUM in the layout of the end statement with the task. -/
noncomputable def wrap3Sum : Wrap EndStatement.ThreeSum s3Task true where
  args := [v 1, v 2, k 1, v 1 +' k 1]
  inst := threeSumInst
  fr x := x.n + 1
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by
    have := Nat.le_mul_self x.n
    omega
  vals x σ hn hU _ := by simp [s3Task, threeSumInst, hn, hU]
  safe x lim σ hn _ _ hw := by
    have hnn : (x.n : ℤ) ≤ (x.n : ℤ) * x.n := by exact_mod_cast Nat.le_mul_self x.n
    push_cast at hw
    simp [hn, abs_le]
    omega
  zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨i, _⟩ => absurd i.isLt (by omega)⟩, trivial⟩
  pre := pre_threeSum
  post x r μ' _ h := post_threeSum x r μ' h

/-- **3SUM**: if the task is solved in time T, then 3SUM is solved on the word RAM within a constant
times T. -/
theorem realized_threeSum (T : ℕ → ℝ → ℝ) (h : SolvedIn s3Task T) :
    Realized EndStatement.ThreeSum T :=
  wrap3Sum.realized h

end Light.Sec3
