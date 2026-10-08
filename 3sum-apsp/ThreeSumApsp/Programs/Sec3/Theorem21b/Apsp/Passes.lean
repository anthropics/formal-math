/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem21b.RepeatedSquaring

/-!
# APSP by repeated squaring: the three passes over the matrix

For Theorem 21(b).  The host for APSP keeps the current matrix as a list of
`n²` integers, in which a large number `INF` stands for `+∞`.  This file has its three simple
passes, each with its specification (`clip_meets`, `apInit_meets`, `apOut_meets`).

* clip(len, thr, INF, src, dst) copies `len` cells from `src` to `dst` and replaces every number
  above `thr` by `INF`.
* apInit(n, INF, adj, w, A) writes the weight matrix of the graph to `A`: 0 on the diagonal, the
  weight where there is an edge, `INF` elsewhere.
* apOut(len, INF, A, out) writes two cells for each cell of `A`: (0, 0) for `INF`, and (1, x) for
  any other number `x`.

In each proof the memory after j rounds is written down (`wrote`, `zeroedDiag`), one lemma says what
a round does to the state, and the loop rule does the rest.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## clip -/

namespace Clip

/-- The number of cells. -/
abbrev Len : ℕ := 0
/-- The threshold. -/
abbrev Thresh : ℕ := 1
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 2
/-- The address of the source. -/
abbrev Src : ℕ := 3
/-- The address of the destination. -/
abbrev Dst : ℕ := 4
/-- The counter q. -/
abbrev Idx : ℕ := 5

end Clip

open Clip in
/-- clip(len, thr, INF, src, dst): for q < len, dst[q] := INF if src[q] > thr, and src[q]
otherwise. -/
def clipBody : Stmt :=
  .for Idx (v Len) (
    .ite (v Thresh <' M (v Src +' v Idx))
      (.store (v Dst +' v Idx) (v Big))
      (.store (v Dst +' v Idx) (M (v Src +' v Idx))))

/-- **clip** writes the clipped list to dst, changes nothing else, and takes at most 23 len + 6
steps. -/
theorem clip_meets {p : ℕ} (hp : P[p]? = some clipBody) {μ : ℕ → ℤ} {src dst : ℕ} {thr INF : ℤ}
    {L : List ℤ} (hL : Seg μ src L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + L.length ≤ lim.space) (hdst : dst + L.length ≤ lim.space)
    (hsep : src + L.length ≤ dst ∨ dst + L.length ≤ src) :
    Meets lim P p d [L.length, thr, INF, src, dst] μ (23 * L.length + 6) fun _ μ' =>
      Seg μ' dst (L.map (clip thr INF)) ∧ SameOutside μ μ' dst L.length := by
  refine .of_body hp ?_
  refine Ends.forFrame (fun j μ' => μ' = wrote μ dst (fun i => clip thr INF (L.getD i 0)) j)
    L.length wrote_zero.symm ?round ?done (hT := by simp; omega)
  case round =>
    intro j μ' hj hμ
    have hread : μ' (src + j) = L.getD j 0 :=
      hμ ▸ (wrote_rest (by omega)).trans (hL.getD hj 0)
    have hnext : Function.update μ' (dst + j) (clip thr INF (L.getD j 0)) = _ := hμ ▸ wrote_succ
    -- from here on x = src[j]
    generalize L.getD j 0 = x at hread hnext
    -- if Thresh < mem[Src + Idx]
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · have hc' : thr < x := by simpa [hread] using hc
      rw [clip, if_pos hc'] at hnext
      -- mem[Dst + Idx] := Big
      light_store (dst + j) INF
      exact ⟨rfl, hnext⟩
    · have hc' : ¬ thr < x := by simpa [hread] using hc
      rw [clip, if_neg hc'] at hnext
      -- mem[Dst + Idx] := mem[Src + Idx]
      light_store (dst + j) x using hread
      exact ⟨rfl, hnext⟩
  case done =>
    rintro _ rfl
    dsimp only
    exact ⟨seg_wrote_map _ L, sameOutside_wrote le_rfl⟩

/-! ## apInit -/

namespace ApInit

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The address of A. -/
abbrev Mat : ℕ := 4
/-- The counter of both passes. -/
abbrev Idx : ℕ := 5
/-- n², in the first pass. -/
abbrev Cells : ℕ := 6
/-- The address of the diagonal cell, in the second pass. -/
abbrev Diag : ℕ := 6

end ApInit

open ApInit in
/-- The round of the first pass: A[q] := w[q] if adj[q] = 1, and INF otherwise. -/
def apInitFill : Stmt :=
  .ite (M (v AdjAt +' v Idx) =' k 1) (.store (v Mat +' v Idx) (M (v WtsAt +' v Idx)))
    (.store (v Mat +' v Idx) (v Big))

open ApInit in
/-- The round of the second pass: the diagonal cell becomes 0; the next one is n + 1 cells on. -/
def apInitDiag : Stmt := .store (v Diag) (k 0) ;; .set Diag (v Diag +' v Verts +' k 1)

open ApInit in
/-- apInit(n, INF, adj, w, A): the first pass fills the n² cells of A, the second pass puts 0 on the
diagonal. -/
def apInitBody : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .for Idx (v Cells) apInitFill ;;
  .set Diag (v Mat) ;;
  .for Idx (v Verts) apInitDiag

/-- The entry number q of the weight matrix, the diagonal apart. -/
def apInitCell (INF : ℤ) (ADJ W : List ℤ) (q : ℕ) : ℤ :=
  if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The memory μ after the first j diagonal cells of the matrix at A have become 0. -/
def zeroedDiag (μ : ℕ → ℤ) (A n j : ℕ) : ℕ → ℤ :=
  fun a => if ∃ i < j, a = A + i * (n + 1) then 0 else μ a

private theorem zeroedDiag_zero {μ : ℕ → ℤ} {A n : ℕ} : zeroedDiag μ A n 0 = μ := by
  funext a
  simp [zeroedDiag]

/-- What round j of the second pass writes. -/
private theorem zeroedDiag_succ {μ : ℕ → ℤ} {A n : ℕ} (j : ℕ) :
    Function.update (zeroedDiag μ A n j) (A + j * (n + 1)) 0 = zeroedDiag μ A n (j + 1) := by
  funext a
  simp only [zeroedDiag, Nat.exists_lt_succ_right, Function.update_apply]
  by_cases h : a = A + j * (n + 1) <;> simp [h]

/-- After both passes the weight matrix stands at A. -/
private theorem seg_zeroedDiag_wrote {μ : ℕ → ℤ} {A n : ℕ} {INF : ℤ} {ADJ W : List ℤ} :
    Seg (zeroedDiag (wrote μ A (apInitCell INF ADJ W) (n * n)) A n n) A
      (weightList n INF ADJ W) := by
  intro q hq
  have hq' : q < n * n := by simpa [weightList] using hq
  have hdiag : (∃ i < n, A + q = A + i * (n + 1)) ↔ q / n = q % n :=
    ⟨fun ⟨i, hi, h⟩ => by
      obtain ⟨h1, h2⟩ := (Nat.eq_mul_succ_iff hi).1 (Nat.add_left_cancel h)
      rw [h1, h2],
    fun h => ⟨q % n, Nat.mod_lt_of_lt_mul hq', congrArg (A + ·)
      ((Nat.eq_mul_succ_iff (Nat.mod_lt_of_lt_mul hq')).2 ⟨h, rfl⟩)⟩⟩
  simp only [zeroedDiag, hdiag, wrote_done hq', weightList, List.getElem_map, List.getElem_range,
    apInitCell]

/-- Both passes change the n² cells of A only. -/
private theorem sameOutside_zeroedDiag {μ μ' : ℕ → ℤ} {A n j : ℕ} (h : SameOutside μ μ' A (n * n))
    (hj : j ≤ n) : SameOutside μ (zeroedDiag μ' A n j) A (n * n) := by
  intro a ha
  have hno : ¬ ∃ i < j, a = A + i * (n + 1) := by
    rintro ⟨i, hi, rfl⟩
    have := Nat.mul_add_lt_mul (show i < n by omega) (show i < n by omega)
    rw [Nat.mul_succ] at ha
    simp only [Outside] at ha
    omega
  rw [zeroedDiag, if_neg hno]
  exact h a ha

/-- The invariant of the second pass of apInit before round j; μ is the memory after the first
pass. -/
def ApInitInv (μ : ℕ → ℤ) (n adj w A : ℕ) (INF : ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [n, INF, adj, w, A, j, (A + j * (n + 1) : ℕ)], zeroedDiag μ A n j⟩

/-- **One round of the first pass of apInit**, for the cells adj[j] = x and w[j] = y: the weight y
where there is an edge, and INF where there is none. -/
private theorem apInitFill_spec {μ : ℕ → ℤ} {adj w A j : ℕ} {n INF nn x y : ℤ}
    (hx : μ (adj + j) = x) (hy : μ (w + j) = y) (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : adj + j < lim.space ∧ w + j < lim.space ∧ A + j < lim.space) :
    Ends lim P d apInitFill ⟨frame [n, INF, adj, w, A, j, nn], μ⟩ apInitFill.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, nn],
        Function.update μ (A + j) (if x = 1 then y else INF)⟩ := by
  unfold apInitFill
  -- if mem[AdjAt + Idx] = 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : x = 1 := by simpa [hx] using hc
    rw [if_pos hc']
    -- mem[Mat + Idx] := mem[WtsAt + Idx]
    light_store (A + j) y using hy
    rfl
  · have hc' : x ≠ 1 := by simpa [hx] using hc
    rw [if_neg hc']
    -- mem[Mat + Idx] := Big
    light_store (A + j) INF
    rfl

/-- **One round of the second pass of apInit**, for the address o of the diagonal cell.  The next
address o + n + 1 is computed also in the last round, so it has to fit. -/
private theorem apInitDiag_spec {μ : ℕ → ℤ} {n o : ℕ} {INF adj w A j : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (ho : o + n + 1 ≤ lim.space) :
    Ends lim P d apInitDiag ⟨frame [n, INF, adj, w, A, j, o], μ⟩ apInitDiag.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, (o + (n + 1) : ℕ)], Function.update μ o 0⟩ := by
  unfold apInitDiag
  -- mem[Diag] := 0 ; Diag := Diag + Verts + 1
  light_store o 0
  light_set (o + (n + 1) : ℕ)
  rfl

/-- **apInit** writes the weight matrix to A, changes nothing else, and takes at most
23 n² + 17 n + 18 steps.  Only n² cells are written; the space 2 n² is asked for because after the
last round of the second pass the local Diag holds A + n (n + 1), which has to fit. -/
theorem apInit_meets {p : ℕ} (hp : P[p]? = some apInitBody) {μ : ℕ → ℤ} {n adj w A : ℕ} {INF : ℤ}
    {ADJ W : List ℤ} (hn : 1 ≤ n) (lenADJ : ADJ.length = n * n) (lenW : W.length = n * n)
    (segADJ : Seg μ adj ADJ) (segW : Seg μ w W) (hw : (lim.space : ℤ) ≤ lim.word)
    (hadj : adj + n * n ≤ lim.space) (hwt : w + n * n ≤ lim.space)
    (hA : A + 2 * (n * n) ≤ lim.space) (sepADJ : adj + n * n ≤ A ∨ A + n * n ≤ adj)
    (sepW : w + n * n ≤ A ∨ A + n * n ≤ w) :
    Meets lim P p d [n, INF, adj, w, A] μ (23 * (n * n) + 17 * n + 18) fun _ μ' =>
      Seg μ' A (weightList n INF ADJ W) ∧ SameOutside μ μ' A (n * n) := by
  refine .of_body hp ?_
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have hword : (n : ℤ) * n ≤ lim.word := by exact_mod_cast (show ((n * n : ℕ) : ℤ) ≤ _ by omega)
  have hpos : 0 ≤ (n : ℤ) * n := by positivity
  unfold apInitBody
  -- Cells := Verts * Verts
  light_set (n * n : ℕ)
  -- for Idx < Cells: the first pass
  refine Ends.next _ (Ends.forFrame (fun j μ' => μ' = wrote μ A (apInitCell INF ADJ W) j)
    (n * n) wrote_zero.symm ?round ?done (hT := le_rfl)) (by simp [apInitFill]; omega)
  case round =>
    rintro j _ hj rfl
    -- the cells adj[j] and w[j] are as at the start
    have hadjCell : wrote μ A (apInitCell INF ADJ W) j (adj + j) = ADJ.getD j 0 :=
      (wrote_rest (by omega)).trans (segADJ.getD (lenADJ ▸ hj) 0)
    have hwtCell : wrote μ A (apInitCell INF ADJ W) j (w + j) = W.getD j 0 :=
      (wrote_rest (by omega)).trans (segW.getD (lenW ▸ hj) 0)
    refine (apInitFill_spec hadjCell hwtCell hw (by omega)).mono le_rfl ?_
    rintro _ rfl
    exact ⟨rfl, wrote_succ⟩
  case done =>
    rintro _ rfl
    -- Diag := Mat
    refine Ends.setToThen A ?_ (hT := by simp [apInitFill]; omega)
    -- for Idx < Verts: the second pass
    refine Ends.for (ApInitInv (wrote μ A (apInitCell INF ADJ W) (n * n)) n adj w A INF) n
      apInitDiag.blockCost ?start ?round ?done ?bound (by omega)
      (by simp [apInitFill, apInitDiag]; omega)
    case start =>
      rw [ApInitInv, zeroedDiag_zero, Nat.zero_mul, Nat.add_zero]
      exact congrArg (State.mk · _) (update_frame_setLocal _ _ _)
    case round =>
      rintro j _ hj - rfl
      have hrow := Nat.mul_add_le_mul hj (le_refl (n + 1))
      rw [Nat.mul_succ n n] at hrow
      refine (apInitDiag_spec hw (by omega)).mono le_rfl ?_
      rintro _ rfl
      exact ⟨rfl, by rw [ApInitInv, update_frame_setLocal, Nat.cast_succ, zeroedDiag_succ,
        Nat.succ_mul, Nat.add_assoc]; rfl⟩
    case done =>
      rintro _ - rfl
      exact ⟨seg_zeroedDiag_wrote, sameOutside_zeroedDiag (sameOutside_wrote le_rfl) le_rfl⟩
    case bound =>
      rintro j _ - - rfl
      exact ⟨trivial, rfl⟩

/-! ## apOut -/

namespace ApOut

/-- The number of cells of A. -/
abbrev Len : ℕ := 0
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 1
/-- The address of A. -/
abbrev Mat : ℕ := 2
/-- The address of the output. -/
abbrev Out : ℕ := 3
/-- The counter q. -/
abbrev Idx : ℕ := 4
/-- The address out + 2q. -/
abbrev Pos : ℕ := 5

end ApOut

open ApOut in
/-- The two cells of the output for the cell A[q]. -/
def apOutWrite : Stmt :=
  .ite (M (v Mat +' v Idx) =' v Big)
    (.store (v Pos) (k 0) ;; .store (v Pos +' k 1) (k 0))
    (.store (v Pos) (k 1) ;; .store (v Pos +' k 1) (M (v Mat +' v Idx)))

open ApOut in
/-- The round of apOut for the cell A[q]. -/
def apOutRound : Stmt := apOutWrite ;; .set Pos (v Pos +' k 2)

open ApOut in
/-- apOut(len, INF, A, out): for q < len, the cells out[2q], out[2q + 1] become 0, 0 if A[q] = INF,
and 1, A[q] otherwise. -/
def apOutBody : Stmt := .set Pos (v Out) ;; .for Idx (v Len) apOutRound

/-- Cell number c of the output: cells 2q and 2q + 1 are 0, 0 if L[q] = INF, and 1, L[q]
otherwise. -/
def apOutCell (INF : ℤ) (L : List ℤ) (c : ℕ) : ℤ :=
  if L.getD (c / 2) 0 = INF then 0 else if c % 2 = 0 then 1 else L.getD (c / 2) 0

/-- What round q writes. -/
private theorem wrote_apOutCell_succ {μ : ℕ → ℤ} {out : ℕ} {INF : ℤ} {L : List ℤ} (q : ℕ) :
    Function.update (Function.update (wrote μ out (apOutCell INF L) (2 * q)) (out + 2 * q)
      (if L.getD q 0 = INF then 0 else 1)) (out + 2 * q + 1)
      (if L.getD q 0 = INF then 0 else L.getD q 0) =
        wrote μ out (apOutCell INF L) (2 * (q + 1)) := by
  have heven : apOutCell INF L (2 * q) = if L.getD q 0 = INF then 0 else 1 := by
    simp only [apOutCell, Nat.mul_div_cancel_left q Nat.two_pos, Nat.mul_mod_right, if_true]
  have hodd : apOutCell INF L (2 * q + 1) = if L.getD q 0 = INF then 0 else L.getD q 0 := by
    simp only [apOutCell, show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega,
      one_ne_zero, if_false]
  rw [← heven, wrote_succ, Nat.add_assoc, ← hodd, wrote_succ]
  rfl

/-- The invariant of the loop of apOut before round j. -/
def ApOutInv (μ : ℕ → ℤ) (A out : ℕ) (INF : ℤ) (L : List ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩

/-- **The two stores of a round of apOut**, for the cell A[j] = x and the address o of the output.
-/
private theorem apOutWrite_spec {μ : ℕ → ℤ} {A out o j : ℕ} {n INF x : ℤ} (hread : μ (A + j) = x)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : A + j < lim.space ∧ o + 1 < lim.space ∧ A + j ≠ o) :
    Ends lim P d apOutWrite ⟨frame [n, INF, A, out, j, o], μ⟩ apOutWrite.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, A, out, j, o], Function.update (Function.update μ o
        (if x = INF then 0 else 1)) (o + 1) (if x = INF then 0 else x)⟩ := by
  unfold apOutWrite
  -- if mem[Mat + Idx] = Big
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : x = INF := by simpa [hread] using hc
    rw [if_pos hc', if_pos hc']
    -- mem[Pos] := 0 ; mem[Pos + 1] := 0
    light_store o 0
    light_store (o + 1) 0
    rfl
  · have hc' : x ≠ INF := by simpa [hread] using hc
    rw [if_neg hc', if_neg hc']
    -- mem[Pos] := 1 ; mem[Pos + 1] := mem[Mat + Idx]
    light_store o 1
    light_store (o + 1) x using Function.update_of_ne hplace.2.2, hread
    rfl

/-- **One round of apOut** writes the pair for the cell A[j] and moves Pos on by two. -/
private theorem apOutRound_spec {μ : ℕ → ℤ} {A out : ℕ} {INF : ℤ} {L : List ℤ} (hL : Seg μ A L)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : A + L.length ≤ lim.space)
    (hout : out + 2 * L.length ≤ lim.space) (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A)
    {j : ℕ} (hj : j < L.length) :
    Ends lim P d apOutRound
      ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩
      apOutRound.blockCost fun σ' =>
        σ' = ⟨frame [L.length, INF, A, out, j, (out + 2 * (j + 1) : ℕ)],
          wrote μ out (apOutCell INF L) (2 * (j + 1))⟩ := by
  have hread : wrote μ out (apOutCell INF L) (2 * j) (A + j) = L.getD j 0 :=
    (wrote_rest (by omega)).trans (hL.getD hj 0)
  rw [← wrote_apOutCell_succ]
  refine Ends.next _ ((apOutWrite_spec hread hw (by omega)).mono le_rfl ?_)
    (by simp [apOutRound])
  rintro _ rfl
  -- Pos := Pos + 2
  exact Ends.setTo (out + 2 * (j + 1) : ℕ) rfl (by light_side) (by simp [apOutRound])

/-- What apOut leaves from the address `out` on: for each number of the list `L` a pair of cells.
Its first cell holds 0 if the number is `INF`; otherwise the pair holds 1 and the number. -/
def PairsAt (μ' : ℕ → ℤ) (out : ℕ) (INF : ℤ) (L : List ℤ) : Prop :=
  ∀ i (hi : i < L.length), (L[i] = INF → μ' (out + 2 * i) = 0) ∧
    (L[i] ≠ INF → μ' (out + 2 * i) = 1 ∧ μ' (out + 2 * i + 1) = L[i])

/-- **apOut** writes the pairs to out, changes nothing else, and takes at most 30 len + 8 steps. -/
theorem apOut_meets {p : ℕ} (hp : P[p]? = some apOutBody) {μ : ℕ → ℤ} {A out : ℕ} {INF : ℤ}
    {L : List ℤ} (hL : Seg μ A L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : A + L.length ≤ lim.space) (hout : out + 2 * L.length ≤ lim.space)
    (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A) :
    Meets lim P p d [L.length, INF, A, out] μ (30 * L.length + 8) fun _ μ' =>
      PairsAt μ' out INF L ∧ SameOutside μ μ' out (2 * L.length) := by
  refine .of_body hp ?_
  unfold apOutBody
  -- Pos := Out
  light_set out
  refine Ends.for (ApOutInv μ A out INF L) L.length apOutRound.blockCost ?start ?round ?done ?bound
    (by omega) (by simp [apOutRound, apOutWrite]; omega)
  case start =>
    rw [ApOutInv, wrote_zero]
    exact congrArg (State.mk · μ) (update_frame_setLocal _ _ _)
  case round =>
    rintro j _ hj - rfl
    refine (apOutRound_spec hL hw hA hout hsep hj).mono le_rfl ?_
    rintro _ rfl
    exact ⟨rfl, by rw [ApOutInv, update_frame_setLocal, Nat.cast_succ]; rfl⟩
  case done =>
    rintro _ - rfl
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    change (_ → wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i) = 0) ∧
      (_ → wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i) = 1 ∧
        wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i + 1) = L[i])
    rw [wrote_done (by omega), Nat.add_assoc, wrote_done (by omega), apOutCell, apOutCell,
      show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega,
      List.getD_eq_getElem _ _ hi]
    exact ⟨fun h => if_pos h, fun h => ⟨by simp [h], by simp [h]⟩⟩
  case bound =>
    rintro j _ - - rfl
    exact ⟨trivial, rfl⟩

end Light.Sec3
