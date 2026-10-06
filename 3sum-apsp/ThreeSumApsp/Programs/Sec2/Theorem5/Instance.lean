/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.SortedFacts
public import ThreeSumApsp.Programs.Tasks

/-!
# Theorem 5: an instance of the task, in the terms of Section 2

An instance of the thin matrix product is given by lists in the memory. This file reads them as the
matrices X and Y and the set W of Section 2, and has the facts that link the two descriptions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- The first matrix of an instance. -/
def ThinX (x : ThinInst) (m : ℕ) : Matrix (Fin x.N) (Fin (D m)) ℤ :=
  fun i j => x.X.getD (i * D m + j) 0

/-- The second matrix of an instance. -/
def ThinY (x : ThinInst) (m : ℕ) : Matrix (Fin (D m)) (Fin x.N) ℤ :=
  fun i j => x.Y.getD (i * x.N + j) 0

/-- The set of the wanted positions of an instance. -/
def ThinW (x : ThinInst) : Finset (Fin x.N × Fin x.N) :=
  Finset.univ.filter fun q => ((q.1 : ℕ), (q.2 : ℕ)) ∈ x.WI.zip x.WJ

/-- The regime of Theorem 5, in terms of the sizes: D = 4^m with m ≥ 1, N ≥ D^18, and at
most N²/√D wanted positions. -/
structure Regime (N D w m : ℕ) : Prop where
  hm : 1 ≤ m
  hD : D = 4 ^ m
  hN : D ^ 18 ≤ N
  hw : w * 2 ^ m ≤ N ^ 2

/-- N ≥ D^18, with D written as the paper's D = 4^m. -/
theorem Regime.pow_le {N D w m : ℕ} (h : Regime N D w m) : ThreeSumApsp.D m ^ 18 ≤ N := by
  have hN := h.hN
  rwa [h.hD] at hN

/-- The sizes are in the regime of Theorem 5, for some m. -/
def InRegime (N D w : ℕ) : Prop := ∃ m : ℕ, Regime N D w m

/-- The regime of Theorem 5, for an instance. -/
abbrev Regime5 (x : ThinInst) (m : ℕ) : Prop := Regime x.N x.D x.w m

/-- The row of the wanted position number i. -/
def thinI (x : ThinInst) (i : ℕ) : ℕ := x.WI.getD i 0

/-- The column of the wanted position number i. -/
def thinJ (x : ThinInst) (i : ℕ) : ℕ := x.WJ.getD i 0

variable {x : ThinInst} {m : ℕ} {μ : ℕ → ℤ} {fr : ℕ}

/-- A list of n k numbers in the memory is an n × k matrix, row by row. -/
theorem matAt_getD {n k a : ℕ} {l : List ℤ} (h : Seg μ a l) (hlen : l.length = n * k) :
    MatAt μ a (fun (i : Fin n) (j : Fin k) => l.getD (i * k + j) 0) := fun i j => by
  rw [Nat.add_assoc]
  exact h.getD (hlen ▸ Nat.mul_add_lt_mul i.isLt j.isLt) 0

/-- The first matrix lies in the memory, row by row. -/
theorem matAt_thinX (hD : x.D = 4 ^ m) (hpre : x.Pre μ fr) : MatAt μ x.x (ThinX x m) :=
  matAt_getD hpre.segX (hpre.lenX.trans (by rw [hD]; rfl))

/-- The second matrix lies in the memory, row by row. -/
theorem matAt_thinY (hD : x.D = 4 ^ m) (hpre : x.Pre μ fr) : MatAt μ x.y (ThinY x m) :=
  matAt_getD hpre.segY (hpre.lenY.trans (by rw [hD]; rfl))

/-- The entries of the first matrix are bounded by U. -/
theorem abs_thinX_le (hpre : x.Pre μ fr) (i : Fin x.N) (j : Fin (D m)) : |ThinX x m i j| ≤ x.U := by
  exact hpre.leX.abs_getD_le (by positivity) _

/-- The entries of the second matrix are bounded by U. -/
theorem abs_thinY_le (hpre : x.Pre μ fr) (i : Fin (D m)) (j : Fin x.N) : |ThinY x m i j| ≤ x.U := by
  exact hpre.leY.abs_getD_le (by positivity) _

/-- The entry asked for by the task is the entry of the product of the two matrices. -/
theorem thinEntry_eq_mul (hD : x.D = 4 ^ m) (I J : Fin x.N) :
    thinEntry x.N x.D x.X x.Y I J = (ThinX x m * ThinY x m) I J := by
  have hDm : x.D = D m := hD
  unfold thinEntry
  rw [hDm, List.sum_map_range, Finset.sum_range, Matrix.mul_apply]
  rfl

section positions

variable {i : ℕ}

/-- A number of a wanted position is an index of the list of the rows. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWI (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WI.length :=
  hi.trans_eq hpre.lenWI.symm

/-- A number of a wanted position is an index of the list of the columns. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWJ (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WJ.length :=
  hi.trans_eq hpre.lenWJ.symm

/-- A number of a wanted position is an index of the list of the positions. -/
theorem _root_.Light.ThinInst.Pre.lt_lenZip (hpre : x.Pre μ fr) (hi : i < x.w) :
    i < (x.WI.zip x.WJ).length := by
  simp [hpre.lenWI, hpre.lenWJ, hi]

theorem thinI_eq (h : i < x.WI.length) : thinI x i = x.WI[i] := List.getD_eq_getElem _ _ h

theorem thinJ_eq (h : i < x.WJ.length) : thinJ x i = x.WJ[i] := List.getD_eq_getElem _ _ h

/-- The rows of the wanted positions are rows of the matrix. -/
theorem thinI_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinI x i < x.N := by
  rw [thinI_eq (hpre.lt_lenWI hi)]
  exact hpre.ltWI _ (List.getElem_mem _)

/-- The columns of the wanted positions are columns of the matrix. -/
theorem thinJ_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinJ x i < x.N := by
  rw [thinJ_eq (hpre.lt_lenWJ hi)]
  exact hpre.ltWJ _ (List.getElem_mem _)

/-- The rows of the wanted positions, in the memory. -/
theorem mem_thinI (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wi + i) = (thinI x i : ℕ) := by
  rw [thinI_eq (hpre.lt_lenWI hi), hpre.segWI i (by simpa using hpre.lt_lenWI hi),
    List.getElem_map]

/-- The columns of the wanted positions, in the memory. -/
theorem mem_thinJ (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wj + i) = (thinJ x i : ℕ) := by
  rw [thinJ_eq (hpre.lt_lenWJ hi), hpre.segWJ i (by simpa using hpre.lt_lenWJ hi),
    List.getElem_map]

end positions

/-- The wanted positions are different. -/
theorem thin_inj (hpre : x.Pre μ fr) :
    ∀ i < x.w, ∀ j < x.w, thinI x i = thinI x j → thinJ x i = thinJ x j → i = j := by
  intro i hi j hj hrow hcol
  rw [thinI_eq (hpre.lt_lenWI hi), thinI_eq (hpre.lt_lenWI hj)] at hrow
  rw [thinJ_eq (hpre.lt_lenWJ hi), thinJ_eq (hpre.lt_lenWJ hj)] at hcol
  refine (hpre.nodup.getElem_inj_iff (hi := hpre.lt_lenZip hi) (hj := hpre.lt_lenZip hj)).1 ?_
  rw [List.getElem_zip, List.getElem_zip, hrow, hcol]

/-- The set of the wanted positions, from the two functions. -/
theorem thinW_eq_wantedSet (hpre : x.Pre μ fr) :
    ThinW x = wantedSet x.N x.w (thinI x) (thinJ x) := by
  ext q
  simp only [ThinW, wantedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
    have hi' : i < x.WI.length ∧ i < x.WJ.length := by simpa using hi
    rw [List.getElem_zip] at he
    obtain ⟨e1, e2⟩ := Prod.mk.inj he
    exact ⟨i, by rw [← hpre.lenWI]; exact hi'.1, by rw [thinI_eq hi'.1, e1],
      by rw [thinJ_eq hi'.2, e2]⟩
  · rintro ⟨i, hi, e1, e2⟩
    rw [thinI_eq (hpre.lt_lenWI hi)] at e1
    rw [thinJ_eq (hpre.lt_lenWJ hi)] at e2
    have : ((q.1 : ℕ), (q.2 : ℕ)) = (x.WI.zip x.WJ)[i]'(hpre.lt_lenZip hi) := by
      rw [List.getElem_zip, e1, e2]
    rw [this]
    exact List.getElem_mem _

/-- There is one answer for each wanted position. -/
theorem length_thinOut (hpre : x.Pre μ fr) : (thinOut x.N x.D x.X x.Y x.WI x.WJ).length = x.w := by
  simp [thinOut, hpre.lenWI, hpre.lenWJ]

/-- The answer number i. -/
theorem getD_thinOut (hpre : x.Pre μ fr) {i : ℕ} (hi : i < x.w) :
    (thinOut x.N x.D x.X x.Y x.WI x.WJ).getD i 0
      = thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) := by
  rw [thinI_eq (hpre.lt_lenWI hi), thinJ_eq (hpre.lt_lenWJ hi)]
  unfold thinOut
  rw [List.getD_eq_getElem _ _ (by simpa using hpre.lt_lenZip hi), List.getElem_map,
    List.getElem_zip]

end Light.Sec2
