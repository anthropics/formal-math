/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.DataStructure

/-!
# Corollary 40: what the programs for v-hinted Mv and Mv-hinted Mv share

Proof of Corollary 40: "we preprocess X := M and Y := V [...]  In Phase 3, the n entries of column i
of MV are n queries".  The procedure col asks the n queries for a column and writes the signs of the
counts (`col_meets`); the data structure is an arbitrary kit.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam Light.Sec4

/-! ## The n queries for a column -/

namespace Col

/-- The locals of col(N, D, aX, aY, fr, j, out).  The arguments: the size N, the inner dimension D,
the addresses of X, of Y and of the data structure, the column j, the address of the output.  Then
the row, which counts from 0 to N - 1, and the count that the query returns. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Inner : ℕ := 1
@[inherit_doc Size] abbrev AddrX : ℕ := 2
@[inherit_doc Size] abbrev AddrY : ℕ := 3
@[inherit_doc Size] abbrev Free : ℕ := 4
@[inherit_doc Size] abbrev Column : ℕ := 5
@[inherit_doc Size] abbrev Out : ℕ := 6
@[inherit_doc Size] abbrev Row : ℕ := 7
@[inherit_doc Size] abbrev Count : ℕ := 8

end Col

open Col in
/-- col(N, D, aX, aY, fr, j, out): for every row r, out[r] := 1 if (XY)[r, j] > 0, else 0. -/
def colBody : Stmt :=
  .for Row (v Size) (
    .call Proc.query31 [v Row, v Column, v Size, v Inner, v AddrX, v AddrY, v Free] Count ;;
    .ite (k 0 <' v Count) (.store (v Out +' v Row) (k 1)) (.store (v Out +' v Row) (k 0)))

/-- The time of col, if a query takes tq steps. -/
def tCol (tq N : ℕ) : ℕ := N * (tq + 30) + 6

open Col in
/-- **col** writes, for every row r, whether the entry (XY)[r, j] is positive. -/
theorem col_meets {P : Program} (K : DsKit P) {pCol : ℕ} (hc : P[pCol]? = some colBody)
    {lim : Limits} {d : ℕ} {N D₀ aX aY fr out : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
    {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ} (j : Fin N)
    (hin : K.Input lim X Y aX aY fr U) (hout : out + N ≤ fr) (apX : Apart aX (N * D₀) out N)
    (apY : Apart aY (D₀ * N) out N) (hR : K.Ready X Y aX aY fr μ) (hd : d + 4 ≤ lim.depth) :
    Meets lim P pCol d [(N : ℤ), D₀, aX, aY, fr, (j : ℕ), out] μ (tCol (K.tQ D₀) N) fun _ μ' =>
      ∀ r : Fin N, μ' (out + r) = if 0 < (X * Y) r j then 1 else 0 := by
  obtain ⟨hw, h100, hsp, -⟩ := K.basics hin.lim
  have hbelowX := hin.belowX
  have hbelowY := hin.belowY
  refine .of_body hc ?_
  unfold colBody tCol
  -- for r < N: the structure is ready, and the answers for the rows below r are written
  refine Ends.forScratch [Count] (fun i μ' => K.Ready X Y aX aY fr μ' ∧
      ∀ r : Fin N, (r : ℕ) < i → μ' (out + r) = if 0 < (X * Y) r j then 1 else 0)
    N (K.tQ D₀ + 22) ⟨hR, fun r hr => absurd hr (by omega)⟩ ?round fun _ _ h r => h.2 r r.isLt
  rintro i _ μ' hi ⟨hR', hdone⟩
  -- count := query(r, j, N, D, aX, aY, fr)
  light_call (K.query hin hR' ⟨i, hi⟩ j _ (by omega)) with _ μ₂ ⟨rfl, hR₂, hsame⟩
  -- after out[r] := b, where b is 1 if the count is positive, and else 0
  have hstored (b : ℤ) (hb : b = if 0 < (X * Y) ⟨i, hi⟩ j then 1 else 0) :
      K.Ready X Y aX aY fr (Function.update μ₂ (out + i) b) ∧ ∀ r : Fin N, (r : ℕ) < i + 1 →
        Function.update μ₂ (out + i) b (out + r) = if 0 < (X * Y) r j then 1 else 0 := by
    refine ⟨hR₂.keep, fun r hr => ?_⟩
    rcases Nat.lt_or_ge r i with hlt | hge
    · exact Eq.trans (by light_keep) (hdone r hlt)
    · obtain rfl : r = ⟨i, hi⟩ := Fin.ext (show (r : ℕ) = i by omega)
      rw [Function.update_self, hb]
  -- if 0 < count then out[r] := 1 else out[r] := 0
  light_if hpos hneg : 0 < (X * Y) ⟨i, hi⟩ j
  · light_store (out + i) 1
    exact hstored 1 (if_pos hpos).symm
  · light_store (out + i) 0
    exact hstored 0 (if_neg hneg).symm

/-- "a Boolean entry is 1 exactly when the corresponding integer entry is positive": what col writes
is the Boolean as a number. -/
theorem ite_pos_eq_bit {b : Bool} {z : ℤ} (h : b = true ↔ 0 < z) :
    (if 0 < z then 1 else 0) = bit b := by
  simp only [bit, h]

end Light.Sec5
