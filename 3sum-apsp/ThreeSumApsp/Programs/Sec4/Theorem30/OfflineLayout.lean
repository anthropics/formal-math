/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline

/-!
# Theorem 30, the offline form: the main procedure for the trusted layout

The input is N, D, |W|, m, L, t, X, Y, the rows of the wanted positions, their columns (the problem
thinProduct [m, L, t]); the output follows the input, and the block of the data structure follows
the output.  The main procedure wantedMain reads the sizes, computes the six addresses and calls
wantedCore (`wantedMain_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

abbrev Proc.wantedMain : ℕ := 57

namespace WantedMain

/-- The locals of wantedMain: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns, of the output and of the block, and
the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Count : ℕ := 4
@[inherit_doc Ans] abbrev Area : ℕ := 5
@[inherit_doc Ans] abbrev MatY : ℕ := 6
@[inherit_doc Ans] abbrev Rows : ℕ := 7
@[inherit_doc Ans] abbrev Cols : ℕ := 8
@[inherit_doc Ans] abbrev Out : ℕ := 9
@[inherit_doc Ans] abbrev Block : ℕ := 10
@[inherit_doc Ans] abbrev Res : ℕ := 11

end WantedMain

open WantedMain in
/-- wantedMain: read the sizes, compute the addresses, call wantedCore, answer 1. -/
def wantedMainBody : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Count (M (k 2)) ;;
  .set Area (v Size *' v Dim) ;; .set MatY (k 6 +' v Area) ;; .set Rows (v MatY +' v Area) ;;
  .set Cols (v Rows +' v Count) ;; .set Out (v Cols +' v Count) ;; .set Block (v Out +' v Count) ;;
  .call Proc.wantedCore [M (k 4), M (k 3), M (k 5), v Size, v Dim, k 6, v MatY, v Rows, v Cols,
    v Count, v Out, v Block] Res ;;
  .set Ans (k 1)

/-- The memory holds the input of the offline form of Theorem 30, with D = 4^m, from cell 0 on. -/
structure WantedLayout {N : ℕ} (m L t : ℕ) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (W : List (Fin N × Fin N)) (μ : ℕ → ℤ) : Prop where
  cellN : μ 0 = N
  cellD : μ 1 = D m
  cellW : μ 2 = W.length
  cellm : μ 3 = m
  cellL : μ 4 = L
  cellt : μ 5 = t
  matX : MatAt μ 6 X
  matY : MatAt μ (6 + N * D m) Y
  rows : Seg μ (6 + N * D m + N * D m) (W.map fun q => ((q.1 : ℕ) : ℤ))
  cols : Seg μ (6 + N * D m + N * D m + W.length) (W.map fun q => ((q.2 : ℕ) : ℤ))

/-- The address of the output: the length of the input. -/
def wantedOut (N m w : ℕ) : ℕ := 6 + N * D m + N * D m + w + w

/-- The base address of the block of the data structure. -/
def wantedB0 (N m w : ℕ) : ℕ := wantedOut N m w + w

/-- **The main procedure** leaves the wanted entries behind the input and returns 1. -/
theorem wantedMain_meets {lim : Limits} {P : Program} {c : ℕ}
    (hP : P[Proc.wantedMain]? = some wantedMainBody) (hcore : WantedCoreSpec lim P c) {N m L t : ℕ}
    (hmL : m ≤ L) (ht : t ≤ m) {X : Matrix (Fin N) (Fin (D m)) ℤ} {Y : Matrix (Fin (D m)) (Fin N) ℤ}
    {W : List (Fin N × Fin N)} {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hlim : Lim30 lim ⟨L, m, N⟩ t (wantedB0 N m W.length) U) (hd : L + 9 ≤ lim.depth) {μ : ℕ → ℤ}
    (hμ : WantedLayout m L t X Y W μ) :
    Meets lim P Proc.wantedMain 1 [0, 0] μ (tWantedCore c ⟨L, m, N⟩ t W.length + 52) fun r μ' =>
      r = 1 ∧ Seg μ' (wantedOut N m W.length) (W.map fun q => (X * Y) q.1 q.2) := by
  refine Meets.of_body hP ?_
  light_facts hlim hlim.std
  have htop := base_le_top ⟨L, m, N⟩ t (wantedB0 N m W.length)
  -- a name for the product N D
  generalize harea : N * D m = area
  have hmul : (N : ℤ) * (D m : ℤ) = area := by rw [← harea]; push_cast; rfl
  have hb0 : wantedB0 N m W.length = 6 + area + area + W.length + W.length + W.length := by
    rw [← harea]; rfl
  -- Size := mem[0] ; Dim := mem[1] ; Count := mem[2]
  light_set N using hμ.cellN
  light_set (D m) using hμ.cellD
  light_set W.length using hμ.cellW
  -- Area := Size * Dim
  light_set area using hmul
  -- MatY := 6 + Area ; Rows := MatY + Area ; Cols := Rows + Count ; Out := Cols + Count
  light_set (6 + area : ℕ)
  light_set (6 + area + area : ℕ)
  light_set (6 + area + area + W.length : ℕ)
  light_set (6 + area + area + W.length + W.length : ℕ)
  -- Block := Out + Count
  light_set (wantedB0 N m W.length : ℕ) using hb0
  -- Res := wantedCore(mem[4], mem[3], mem[5], Size, Dim, 6, MatY, Rows, Cols, Count, Out, Block)
  have hin : WantedInput ⟨L, m, N⟩ 6 (6 + area) (6 + area + area) (6 + area + area + W.length)
      (6 + area + area + W.length + W.length) (wantedB0 N m W.length) X Y W μ := by
    subst harea
    exact ⟨hμ.matX, hμ.matY, hμ.rows, hμ.cols, by change 6 + N * D m ≤ _; omega,
      by change 6 + N * D m + D m * N ≤ _; rw [Nat.mul_comm (D m) N]; omega, by omega, by omega,
      by omega, Or.inr (by omega), Or.inr (by omega)⟩
  light_call (hcore ⟨L, m, N⟩ t hmL _ _ _ _ _ _ X Y U μ W ht hlim hX hY hin _
    (by change 2 + (L + 7) ≤ lim.depth; omega))
    using hμ.cellm, hμ.cellL, hμ.cellt, Sec2.Par.D with r μ' ⟨hanswers, -⟩
  -- Ans := 1
  light_set 1
  refine ⟨by simp, ?_⟩
  subst harea
  exact hanswers

end Light.Sec4
