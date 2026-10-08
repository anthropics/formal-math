/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem19.Graphs
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds

/-!
# Exact Triangle on n-vertex graphs on the word RAM

Theorem 2, first line: "Exact Triangle on n-vertex graphs in O(n^{2.9983}) time".

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n²; the
free pointer is 1 + 2n² (`graphInst`).  The input meets the precondition of the task `graphEtTask`
(`pre_graph`), so a solver of the task gives a program for the layout of the end statement
(`wrapGraph`).

The task is solved by the host that turns a graph into a tripartite instance (`isHost_graphEt`): the
weights grow from U to 3U + 1, and the host writes n² cells.  So its time is `graphTime T`, if T is
the time for the tripartite form (`solvedIn_graphEtTask`).  For U = n^κ and n ≥ 2 the new bound is
at most n^(κ + 2), so a bound O(n^a) with a ≥ 2 for the tripartite form, for every exponent, gives
the same bound for n-vertex graphs (`solvedInTime_graphs`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-! ## The layout of the end statement -/

open Classical in
/-- The weight of an edge is one of the numbers of the input. -/
theorem weight_mem_input {n : ℕ} (x : WeightedGraph n) {a b : Fin n} (hadj : x.G.Adj a b) :
    x.w a b ∈ GraphExactTriangle.input x := by
  have hmem := mem_rowMajor_self (fun a b => if x.G.Adj a b then x.w a b else 0) a b
  rw [if_pos hadj] at hmem
  exact List.mem_append_right _ hmem

/-- The instance of the task: where the two matrices stand. -/
def graphInst (x : Bounded GraphExactTriangle) : GrInst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, x.x.G, x.x.w⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_graph (x : Bounded GraphExactTriangle) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    graphEtTask.Pre (graphInst x) (memOf ((ofEnd GraphExactTriangle).input x))
      (1 + 2 * (x.n * x.n)) where
  n_pos := hn
  U_pos := hU
  segADJ := seg_first _ _ _
  segW := by
    have := seg_second (x.n : ℤ) (graphInst x).ADJ (graphInst x).W
    rwa [GrInst.length_ADJ] at this
  le := fun _ _ hadj => Bounded.abs_le (weight_mem_input x.x hadj)
  belowADJ := by simp only [graphInst]; omega
  belowW := by simp only [graphInst]; omega

/-- What connects Exact Triangle on n-vertex graphs in the layout of the end statement with the
task. -/
noncomputable def wrapGraph : Wrap GraphExactTriangle graphEtTask true where
  args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3]
  inst := graphInst
  fr x := 1 + 2 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [graphEtTask, graphInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := fun e he =>
    safe_fourAddresses (c := 2) (by omega) hnn hw e (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      tauto)
  zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨a, _⟩ => absurd a.isLt (by omega)⟩, trivial⟩
  pre := pre_graph
  post x r μ' _ h := by
    obtain ⟨rfl, -⟩ := h
    exact ⟨verdictOf_flag _, trivial⟩

/-! ## The running time -/

/-- The time for n-vertex graphs, if T is the time for the tripartite form: the host writes n²
cells, and the bound on the weights grows from u to 3u + 1, which is at most u n² for n ≥ 2. -/
noncomputable def graphTime (T : ℕ → ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  23 * (n : ℝ) ^ 2 + 26 + if 2 ≤ n then T n (u * (n : ℝ) ^ 2) else T n (3 * u + 1)

/-- The task for n-vertex graphs is solved in time `graphTime T`. -/
theorem solvedIn_graphEtTask {T : ℕ → ℝ → ℝ} (hT : SolvedIn etTask T) :
    SolvedIn graphEtTask (graphTime T) := by
  refine isHost_graphEt.solvedIn hT fun Tn hTn n U u hn hU hu => ?_
  have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hbound : ((3 * U + 1 : ℕ) : ℝ) ≤ 3 * u + 1 := by
    push_cast
    linarith
  unfold graphEtTime graphTime
  push_cast
  have hwrite : (23 : ℝ) * ((n : ℝ) * n) = 23 * (n : ℝ) ^ 2 := by ring
  split_ifs with h2
  · have hfour : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (n : ℝ) ^ 2 := by gcongr
    have hgrow : u * 4 ≤ u * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hfour (by linarith)
    linarith [hTn n (3 * U + 1) (u * (n : ℝ) ^ 2) hn (by omega) (by linarith)]
  · linarith [hTn n (3 * U + 1) (3 * u + 1) hn (by omega) hbound]

/-- A bound O(n^a), a ≥ 2, for the tripartite form of Exact Triangle gives the same bound for
n-vertex graphs on the word RAM. -/
theorem solvedInTime_graphs {a : ℝ} (ha : 2 ≤ a)
    (h : ∀ κ : ℝ, 0 ≤ κ →
      ∃ T : ℕ → ℝ → ℝ, SolvedIn etTask T ∧ UpperBigOPow (fun n => T n ((n : ℝ) ^ κ)) a) :
    SolvedInTime GraphExactTriangle a 0 := by
  intro κ
  obtain ⟨T, hT, C, hC⟩ := h ((κ : ℝ) + 2) (by positivity)
  refine FromClaims.solvedAt_of_realized (graphTime T) κ
    (wrapGraph.realized (solvedIn_graphEtTask hT)) (C := |C| + 49) ?_
  filter_upwards [hC, Filter.eventually_ge_atTop 2] with n hn h2
  have h2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  have hweights : (n : ℝ) ^ ((κ : ℕ) : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ ((κ : ℝ) + 2) := by
    rw [Real.rpow_add (by linarith), Real.rpow_two]
  have hsq : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ a := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) ha
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ a := Real.one_le_rpow (by linarith) (by linarith)
  have habs : C * (n : ℝ) ^ a ≤ |C| * (n : ℝ) ^ a :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  simp only [graphTime, if_pos h2, pow_zero, mul_one]
  rw [hweights]
  calc 23 * (n : ℝ) ^ 2 + 26 + T n ((n : ℝ) ^ ((κ : ℝ) + 2))
      ≤ 23 * (n : ℝ) ^ a + 26 * (n : ℝ) ^ a + |C| * (n : ℝ) ^ a := by linarith [hsq, hone, hn, habs]
    _ = (|C| + 49) * (n : ℝ) ^ a := by ring

/-- **Theorem 2**, first line, as printed: "Exact Triangle on n-vertex graphs in
O(n^{2.9983}) time", from the bound for the tripartite form. -/
theorem Theorem2.graphs_of (h : Claim.ExactTriangleIn lightModel 2.9983) :
    Items.Theorem_2_graphs :=
  solvedInTime_graphs (by norm_num) h

end Light.Sec3
