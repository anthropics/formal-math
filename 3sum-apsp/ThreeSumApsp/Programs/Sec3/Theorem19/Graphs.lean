/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.TripartiteOfGraph

/-!
# Exact Triangle on n-vertex graphs, from the tripartite form

Section 3.2: "an instance on an arbitrary n-vertex graph reduces to this form
by taking three copies of the vertex set and giving every missing edge the weight 3n^ν + 1, which
lies in no zero triangle". The host writes one n × n array, with the weight of an edge where there
is an edge and 3U + 1 where there is none, at the free pointer, and calls a solver of Exact Triangle
with this array as each of the three matrices of weights.

The route: how a cell of the new array is computed (`GrInst.getD_Z`); three copies of the array are
the tripartite instance of Section 3.2 (`GrInst.triOf_Z`, `GrInst.tri_pre`); one round of the loop
(`graphEtFill_spec`); the host (`graphEt_spec`); the result (`isHost_graphEt`).  The prefix graphEt
stands for Exact Triangle on graphs.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec

variable {lim : Limits}

/-! ## The task -/

/-- A graph on n vertices with weights on its edges, and the addresses of its adjacency matrix and
of the matrix of the weights. -/
structure GrInst : Type where
  n : ℕ
  U : ℕ
  adj : ℕ
  wa : ℕ
  G : SimpleGraph (Fin n)
  w : Fin n → Fin n → ℤ

open Classical in
/-- The adjacency matrix, row by row: 1 for an edge, 0 for none. -/
noncomputable def GrInst.ADJ (x : GrInst) : List ℤ :=
  rowMajor fun u v => if x.G.Adj u v then 1 else 0

open Classical in
/-- The weights, row by row: 0 where there is no edge. -/
noncomputable def GrInst.W (x : GrInst) : List ℤ :=
  rowMajor fun u v => if x.G.Adj u v then x.w u v else 0

/-- The two matrices lie below the free pointer, and the weights of the edges are bounded by U. -/
structure GrInst.Pre (x : GrInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  segADJ : Seg μ x.adj x.ADJ
  segW : Seg μ x.wa x.W
  le : ∀ u v, x.G.Adj u v → |x.w u v| ≤ (x.U : ℤ)
  belowADJ : x.adj + x.n * x.n ≤ fr
  belowW : x.wa + x.n * x.n ≤ fr

/-- **Exact Triangle on n-vertex graphs**: get(n, U, adj, w, fr) returns 1 if three pairwise
adjacent vertices have edge weights that sum to zero, and 0 if not. -/
noncomputable def graphEtTask : Task where
  Inst := GrInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.adj, x.wa]
  Pre := GrInst.Pre
  Post x μ fr r μ' := r = flag (GraphHasZeroTriangle x.G x.w) ∧ Kept μ μ' fr

/-! ## The pure side -/

/-- Every index below n · m is the index of a pair. -/
private theorem exists_fin_index {n m q : ℕ} (hq : q < n * m) :
    ∃ (i : Fin n) (j : Fin m), (i : ℕ) * m + (j : ℕ) = q := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul hq
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

/-- The weights of the tripartite instance, row by row. -/
noncomputable def GrInst.Z (x : GrInst) : List ℤ := rowMajor (tripartiteOfGraph x.G x.w x.U).wAB

theorem GrInst.length_Z (x : GrInst) : x.Z.length = x.n * x.n := length_rowMajor _

theorem GrInst.length_ADJ (x : GrInst) : x.ADJ.length = x.n * x.n := length_rowMajor _

theorem GrInst.length_W (x : GrInst) : x.W.length = x.n * x.n := length_rowMajor _

/-- How a cell of the new array is computed from the cells of the two given ones. -/
theorem GrInst.getD_Z (x : GrInst) {q : ℕ} (hq : q < x.n * x.n) :
    x.Z.getD q 0 = if x.ADJ.getD q 0 = 1 then x.W.getD q 0 else 3 * (x.U : ℤ) + 1 := by
  obtain ⟨i, j, rfl⟩ := exists_fin_index hq
  unfold GrInst.Z GrInst.ADJ GrInst.W
  rw [getD_rowMajor, getD_rowMajor, getD_rowMajor]
  by_cases h : x.G.Adj i j <;> simp [tripartiteOfGraph, h]

/-- The instance that is read from three copies of the new array is the tripartite instance of
Section 3.2. -/
theorem GrInst.triOf_Z (x : GrInst) : triOf x.n x.Z x.Z x.Z = tripartiteOfGraph x.G x.w x.U := by
  unfold triOf GrInst.Z
  have h : ∀ i j : Fin x.n,
      (rowMajor (tripartiteOfGraph x.G x.w x.U).wAB).getD ((i : ℕ) * x.n + (j : ℕ)) 0 =
      (tripartiteOfGraph x.G x.w x.U).wAB i j := fun i j => getD_rowMajor _ i j
  simp only [h]
  rfl

theorem GrInst.absLe_Z (x : GrInst) (hle : ∀ u v, x.G.Adj u v → |x.w u v| ≤ (x.U : ℤ)) :
    AbsLe x.Z ((3 * x.U + 1 : ℕ) : ℤ) := by
  intro a ha
  obtain ⟨i, j, rfl⟩ := mem_rowMajor ha
  push_cast
  by_cases h : x.G.Adj i j
  · have := hle i j h
    simp only [tripartiteOfGraph, h, if_true]
    omega
  · simp only [tripartiteOfGraph, h, if_false]
    rw [abs_of_nonneg (by positivity)]

/-! ## The host -/

namespace GraphTask

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the weights. -/
abbrev Bound : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The free pointer, where the new array is written. -/
abbrev Free : ℕ := 4
/-- n². -/
abbrev Cells : ℕ := 5
/-- The weight 3U + 1 of a missing edge. -/
abbrev Big : ℕ := 6
/-- The counter q. -/
abbrev Idx : ℕ := 7

end GraphTask

open GraphTask in
/-- The round for the cell number q: the weight of the edge, or 3U + 1 if there is none. -/
def graphEtFill : Stmt :=
  .ite (M (v AdjAt +' v Idx) =' k 1) (.store (v Free +' v Idx) (M (v WtsAt +' v Idx)))
    (.store (v Free +' v Idx) (v Big))

open GraphTask in
/-- get(n, U, adj, w, fr), Exact Triangle on a graph: the array of the weights of the tripartite
instance is written at the free pointer, and the solver is called with it as each of the three
matrices. -/
def graphEtBody (pET : ℕ) : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Big (k 3 *' v Bound +' k 1) ;;
  .for Idx (v Cells) graphEtFill ;;
  .call pET [v Verts, v Big, v Free, v Free, v Free, v Free +' v Cells] 0

/-- The time of the host: n² cells are written, and the solver runs with the bound 3U + 1. -/
def graphEtTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 23 * (n * n) + 26 + T n (3 * U + 1)

/-- The need of the host: n² cells more than the solver, one level of calls more. -/
def graphEtNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := (r n (3 * U + 1)).word + 3 * U + 4
  cells := n * n + (r n (3 * U + 1)).cells
  depth := (r n (3 * U + 1)).depth + 1

/-- The tripartite instance, with the new array as each of its three matrices. -/
noncomputable def GrInst.tri (x : GrInst) (fr : ℕ) : TriInst :=
  ⟨x.n, 3 * x.U + 1, fr, fr, fr, x.Z, x.Z, x.Z⟩

/-- The tripartite instance is as the task Exact Triangle prescribes. -/
theorem GrInst.tri_pre {x : GrInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hseg : Seg μ' fr x.Z) : (x.tri fr).Pre μ' (fr + x.n * x.n) where
  n_pos := hpre.n_pos
  U_pos := Nat.succ_pos _
  lenAB := x.length_Z
  lenBC := x.length_Z
  lenAC := x.length_Z
  segAB := hseg
  segBC := hseg
  segAC := hseg
  leAB := x.absLe_Z hpre.le
  leBC := x.absLe_Z hpre.le
  leAC := x.absLe_Z hpre.le
  belowAB := le_rfl
  belowBC := le_rfl
  belowAC := le_rfl

/-- **One round of the loop of get**, for the cells adj[j] = a and w[j] = b. -/
theorem graphEtFill_spec {P : Program} {d : ℕ} {μ : ℕ → ℤ} {adj wa fr j : ℕ} {n U nn big a b : ℤ}
    (ha : μ (adj + j) = a) (hb : μ (wa + j) = b) (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : adj + j < lim.space ∧ wa + j < lim.space ∧ fr + j < lim.space) :
    Ends lim P d graphEtFill ⟨frame [n, U, adj, wa, fr, nn, big, j], μ⟩ graphEtFill.blockCost
      fun σ' => σ' = ⟨frame [n, U, adj, wa, fr, nn, big, j],
        Function.update μ (fr + j) (if a = 1 then b else big)⟩ := by
  unfold graphEtFill
  -- if mem[AdjAt + Idx] = 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : a = 1 := by simpa [ha] using hc
    rw [if_pos hc']
    -- mem[Free + Idx] := mem[WtsAt + Idx]
    light_store (fr + j) b using hb
    rfl
  · have hc' : a ≠ 1 := by simpa [ha] using hc
    rw [if_neg hc']
    -- mem[Free + Idx] := Big
    light_store (fr + j) big
    rfl

/-- The invariant of the loop of get: the first j cells at the free pointer hold the weights of the
tripartite instance, and no other cell has changed. -/
def FillInv (x : GrInst) (μ : ℕ → ℤ) (fr j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  μ' = wrote μ fr (fun q => x.Z.getD q 0) j

/-- **The host is correct.** -/
theorem graphEt_spec {P R : Program} {pET : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hsol : Solves etTask P pET T r) (lim : Limits) (d : ℕ) (x : GrInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (graphEtNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P ++ R) d (graphEtBody pET) ⟨frame [(x.n : ℤ), x.U, x.adj, x.wa, fr], μ⟩
      (graphEtTime T x.n x.U) fun σ' =>
        σ'.loc 0 = flag (GraphHasZeroTriangle x.G x.w) ∧ Kept μ σ'.mem fr := by
  obtain ⟨hword, hcells, hw, hdepth⟩ := hok
  simp only [graphEtNeed] at hword hcells hdepth
  push_cast at hword
  have hADJ := hpre.belowADJ
  have hWT := hpre.belowW
  have hNN : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  unfold graphEtBody graphEtTime
  -- Cells := Verts * Verts ; Big := 3 * Bound + 1
  light_set (x.n * x.n : ℕ)
  light_set (3 * x.U + 1 : ℕ)
  -- for Idx < Cells: the new array
  refine Ends.next _ (Ends.forFrame (FillInv x μ fr) (x.n * x.n) wrote_zero.symm ?round ?done
    (hT := le_rfl)) (by simp [graphEtFill]; omega)
  case round =>
    rintro j _ hj rfl
    -- the cells adj[j] and w[j] are as at the start
    have hadj : wrote μ fr (fun q => x.Z.getD q 0) j (x.adj + j) = x.ADJ.getD j 0 :=
      (wrote_rest (by omega)).trans (hpre.segADJ.getD (x.length_ADJ ▸ hj) 0)
    have hwts : wrote μ fr (fun q => x.Z.getD q 0) j (x.wa + j) = x.W.getD j 0 :=
      (wrote_rest (by omega)).trans (hpre.segW.getD (x.length_W ▸ hj) 0)
    refine (graphEtFill_spec hadj hwts hw (by omega)).mono le_rfl ?_
    rintro _ rfl
    refine ⟨rfl, ?_⟩
    rw [FillInv, ← wrote_succ, x.getD_Z hj]
    push_cast
    rfl
  case done =>
    rintro _ rfl
    have hseg : Seg (wrote μ fr (fun q => x.Z.getD q 0) (x.n * x.n)) fr x.Z := fun i hi => by
      rw [wrote_done (x.length_Z ▸ hi), List.getD_eq_getElem _ _ hi]
    -- the result is pET(Verts, Big, Free, Free, Free, Free + Cells)
    refine Ends.callTo (hsol.meets R (x.tri fr) (fr + x.n * x.n) (x.tri_pre hpre hseg)
      ⟨by simp only [etTask, GrInst.tri]; omega, by simp only [etTask, GrInst.tri]; omega, hw,
        by simp only [etTask, GrInst.tri]; omega⟩) ?_
      (by light_side [etTask, GrInst.tri])
      (hT := by simp [etTask, GrInst.tri, graphEtFill]; omega)
    rintro res μ' ⟨hres, hkept⟩
    replace hres : res = flag (triOf x.n x.Z x.Z x.Z).HasZeroTriangle := hres
    rw [x.triOf_Z, flag_congr (hasZeroTriangle_tripartiteOfGraph_iff x.G x.w x.U hpre.le)] at hres
    exact ⟨hres, fun a ha => (hkept a (by omega)).trans (wrote_rest (Or.inl ha))⟩

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_graphEtNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (graphEtNeed r) := by
  unfold graphEtNeed
  poly_need [hr.word, hr.cells, hr.depth]

/-- **Exact Triangle on n-vertex graphs from the tripartite form**: the host makes a solver for
graphs from every solver of Exact Triangle. -/
theorem isHost_graphEt : IsHost etTask graphEtTask graphEtTime graphEtNeed := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_graphEtNeed hr⟩
  refine ⟨[graphEtBody p], P.length, graphEtBody p, by simp, ?_⟩
  intro R lim d x μ fr hpre hok
  rw [List.append_assoc]
  exact graphEt_spec hsol lim d x μ fr hpre hok

end Light.Sec3
