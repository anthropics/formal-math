/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline
public import ThreeSumApsp.Programs.Sec4.Theorem30.ThinLayout

/-!
# Section 4.4, the offline form: the main procedure for the layout of the statements

The input is N, D, |W|, X, Y, the rows of the wanted positions, their columns (the problem
`thinProduct []`); the output follows the input, and the free pointer follows the output. The text
`offlineMain32Body` serves all rational parameters c and θ: it reads the sizes, computes the
addresses of Y, of the two lists of indices and of the output and the free pointer, and calls
offline32 (`offlineMain32_meets`). The input in the statements of the corollaries
(`ThinInstance.input`) is laid out as the procedure expects (`offlineLayout32_input`). offline32
enters through its specification `OfflineSpec32`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-! ## The text -/

namespace OfflineMain32

/-- The locals of offlineMain32: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns and of the output, the free pointer,
and the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Count : ℕ := 4
@[inherit_doc Ans] abbrev Area : ℕ := 5
@[inherit_doc Ans] abbrev MatY : ℕ := 6
@[inherit_doc Ans] abbrev Rows : ℕ := 7
@[inherit_doc Ans] abbrev Cols : ℕ := 8
@[inherit_doc Ans] abbrev Out : ℕ := 9
@[inherit_doc Ans] abbrev Free : ℕ := 10
@[inherit_doc Ans] abbrev Res : ℕ := 11

end OfflineMain32

open OfflineMain32 in
/-- offlineMain32: read the sizes, compute the addresses, call offline32, answer 1. -/
def offlineMain32Body : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Count (M (k 2)) ;;
  .set Area (v Size *' v Dim) ;; .set MatY (k 3 +' v Area) ;; .set Rows (v MatY +' v Area) ;;
  .set Cols (v Rows +' v Count) ;; .set Out (v Cols +' v Count) ;; .set Free (v Out +' v Count) ;;
  .call Proc.offline32 [v Size, v Dim, v Count, k 0, k 3, v MatY, v Rows, v Cols, v Out, v Free]
    Res ;;
  .set Ans (k 1)

/-- The free pointer: behind the input and the output. -/
def offlineFree (N D₀ w : ℕ) : ℕ := 3 + 2 * (N * D₀) + 3 * w

/-- The answers of offline32 are the wanted entries. -/
theorem map_entryN {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (W : List (Fin N × Fin N)) :
    (((W.map fun q => (q.1 : ℕ)).zip (W.map fun q => (q.2 : ℕ))).map fun q => entryN X Y q.1 q.2)
      = W.map fun q => (X * Y) q.1 q.2 := by
  rw [List.zip_map', List.map_map]
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp, entryN]
  rw [dif_pos ⟨q.1.isLt, q.2.isLt⟩]

/-! ## What it does -/

/-- The memory holds the input of the offline problem, without further parameters, from cell 0 on.
-/
structure OfflineLayout32 (x : ThinInstance) (μ : ℕ → ℤ) : Prop where
  cellN : μ 0 = x.N
  cellD : μ 1 = x.D
  cellW : μ 2 = x.W.length
  matX : MatAt μ 3 x.X
  matY : MatAt μ (3 + x.N * x.D) x.Y
  rows : Seg μ (3 + x.N * x.D + x.N * x.D) (x.W.map fun q => ((q.1 : ℕ) : ℤ))
  cols : Seg μ (3 + x.N * x.D + x.N * x.D + x.W.length) (x.W.map fun q => ((q.2 : ℕ) : ℤ))

/-- The input in the statements is laid out in this way. -/
theorem offlineLayout32_input (x : ThinInstance) : OfflineLayout32 x (memOf (x.input [])) :=
  ⟨rfl, rfl, rfl, thinInstance_matAt_X x [], thinInstance_matAt_Y x [], thinInstance_seg_rows x [],
    thinInstance_seg_cols x []⟩

/-- In this layout the input of offline32 stands as its specification asks, with the output behind
the input and the free pointer behind the output. -/
theorem OfflineLayout32.taskInput {x : ThinInstance} {μ : ℕ → ℤ} (h : OfflineLayout32 x μ) :
    OfflineInput32 x.X x.Y 3 (3 + x.N * x.D) (3 + x.N * x.D + x.N * x.D)
      (3 + x.N * x.D + x.N * x.D + x.W.length)
      (3 + x.N * x.D + x.N * x.D + x.W.length + x.W.length) (offlineFree x.N x.D x.W.length)
      (x.W.map fun q => (q.1 : ℕ)) (x.W.map fun q => (q.2 : ℕ)) μ := by
  have hlenI : (x.W.map fun q => (q.1 : ℕ)).length = x.W.length := List.length_map _
  have hDN : x.D * x.N = x.N * x.D := Nat.mul_comm _ _
  have hfr : offlineFree x.N x.D x.W.length = 3 + 2 * (x.N * x.D) + 3 * x.W.length := rfl
  exact
    { matX := h.matX, matY := h.matY
      rows := by simpa [SegN, List.map_map, Function.comp_def] using h.rows
      cols := by simpa [SegN, List.map_map, Function.comp_def] using h.cols
      length_eq := by simp
      rows_lt := fun I hI => by obtain ⟨q, -, rfl⟩ := List.mem_map.mp hI; exact q.1.isLt
      cols_lt := fun J hJ => by obtain ⟨q, -, rfl⟩ := List.mem_map.mp hJ; exact q.2.isLt
      rows_le := by omega, cols_le := by omega, out_le := by omega
      out_matX := Or.inr (by omega), out_matY := Or.inr (by omega)
      out_rows := Or.inr (by omega), out_cols := Or.inr (by omega) }

/-- **The main procedure** leaves the wanted entries behind the input and returns 1. -/
theorem offlineMain32_meets {lim : Limits} {P : Program} {c : ℕ} {G : RatParams}
    (hP : P[Proc.offlineMain32]? = some offlineMain32Body) (htask : OfflineSpec32 lim P c G)
    (x : ThinInstance) (hD : 1 ≤ x.D) (hN : 1 ≤ x.N) {U : ℤ} (hX : ∀ i j, |x.X i j| ≤ U)
    (hY : ∀ i j, |x.Y i j| ≤ U) (hlim : Lim31 lim G x.N x.D (offlineFree x.N x.D x.W.length) U)
    (hd : G.L (logFour x.D) + 10 ≤ lim.depth) {μ : ℕ → ℤ} (hμ : OfflineLayout32 x μ) :
    Meets lim P Proc.offlineMain32 1 [0, 0] μ (tOffline32 c G x.N x.D x.W.length + 52) fun r μ' =>
      r = 1 ∧ Seg μ' (3 + x.N * x.D + x.N * x.D + x.W.length + x.W.length)
        (x.W.map fun q => (x.X * x.Y) q.1 q.2) := by
  refine Meets.of_body hP ?_
  have hw := hlim.std.space_le
  have hconst := hlim.std.const_le
  have hspace := hlim.space
  have hfr3 := add_three_le_structEnd G x.N x.D (offlineFree x.N x.D x.W.length)
  have htaskInput := hμ.taskInput
  -- a name for the product N D
  obtain ⟨area, harea⟩ : ∃ area, area = x.N * x.D := ⟨_, rfl⟩
  rw [← harea] at htaskInput ⊢
  have hmul : (x.N : ℤ) * (x.D : ℤ) = area := by rw [harea]; push_cast; rfl
  have hfr : offlineFree x.N x.D x.W.length
      = 3 + area + area + x.W.length + x.W.length + x.W.length := by
    rw [harea]
    unfold offlineFree
    omega
  -- Size := mem[0] ; Dim := mem[1] ; Count := mem[2] ; Area := Size * Dim
  light_set x.N using hμ.cellN
  light_set x.D using hμ.cellD
  light_set x.W.length using hμ.cellW
  light_set area using hmul
  -- MatY := 3 + Area ; Rows := MatY + Area ; Cols := Rows + Count ; Out := Cols + Count
  light_set (3 + area : ℕ)
  light_set (3 + area + area : ℕ)
  light_set (3 + area + area + x.W.length : ℕ)
  light_set (3 + area + area + x.W.length + x.W.length : ℕ)
  -- Free := Out + Count
  light_set (offlineFree x.N x.D x.W.length : ℕ) using hfr
  -- Res := offline32(Size, Dim, Count, 0, 3, MatY, Rows, Cols, Out, Free)
  have hDN : x.D * x.N = area := by rw [harea, Nat.mul_comm]
  have hspec := htask x.N x.D 3 (3 + area) (3 + area + area) (3 + area + area + x.W.length)
    (3 + area + area + x.W.length + x.W.length) (offlineFree x.N x.D x.W.length) x.X x.Y U 0 μ
    (x.W.map fun q => (q.1 : ℕ)) (x.W.map fun q => (q.2 : ℕ))
    { one_le_D := hD, one_le_N := hN, lim := hlim, absX := hX, absY := hY
      belowX := by omega, belowY := by omega } htaskInput
  simp only [List.length_map, map_entryN] at hspec
  light_call (hspec _ (by omega)) with r μ' ⟨hanswers, -⟩
  -- Ans := 1
  light_set 1
  exact ⟨by simp, hanswers⟩

end Light.Sec4
