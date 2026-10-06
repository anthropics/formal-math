/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

/-!
# Section 4.4, the data structure: the two main procedures for the layout of the statements

The input is N, D, X, Y (`ThinPair.input []`), as in the statements of the corollaries; the free
pointer is the first cell after it. The texts `preMain31Body` and `queryMain31Body` serve all
rational parameters c and θ. Each reads N and D, computes the address of Y and the free pointer, and
calls the relocatable routine: `preMain31_meets` for the preprocessing, `queryMain31_meets` for a
query. Between them the memory satisfies `InputReady31`. The relocatable routines enter through
their specifications `PreSpec31` and `QuerySpec31`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The texts -/

namespace Main31

/-- The locals of the two main procedures: the answer, which in a query is at first the row I, and
the column J; then N, D, the product N D, the address of Y, the free pointer, and in the
preprocessing the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Col : ℕ := 1
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Area : ℕ := 4
@[inherit_doc Ans] abbrev MatY : ℕ := 5
@[inherit_doc Ans] abbrev Free : ℕ := 6
@[inherit_doc Ans] abbrev Res : ℕ := 7

end Main31

open Main31 in
/-- The main procedure of the preprocessing: read the sizes, compute the two addresses, call pre31,
answer 1. -/
def preMain31Body : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Area (v Size *' v Dim) ;;
  .set MatY (k 2 +' v Area) ;; .set Free (v MatY +' v Area) ;;
  .call Proc.pre31 [v Size, v Dim, k 2, v MatY, v Free] Res ;;
  .set Ans (k 1)

open Main31 in
/-- The main procedure of a query (I, J): the same five assignments, then call query31. -/
def queryMain31Body : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Area (v Size *' v Dim) ;;
  .set MatY (k 2 +' v Area) ;; .set Free (v MatY +' v Area) ;;
  .call Proc.query31 [v Ans, v Col, v Size, v Dim, k 2, v MatY, v Free] Ans

/-- The free pointer behind the input. -/
def inputEnd (N D₀ : ℕ) : ℕ := 2 + N * D₀ + N * D₀

/-! ## What they do -/

/-- **The memory holds the input and what a query needs.** -/
structure InputReady31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (μ : ℕ → ℤ) : Prop where
  cellN : μ 0 = N
  cellD : μ 1 = D₀
  ready : Ready31 G X Y 2 (2 + N * D₀) (inputEnd N D₀) μ

/-- **The main procedure of the preprocessing** leaves a memory that is ready for queries. -/
theorem preMain31_meets {c : ℕ} (hP : P[Proc.preMain31]? = some preMain31Body)
    (hpre : PreSpec31 lim P c G) (hD : 1 ≤ D₀) (hN : 1 ≤ N) (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hlim : Lim31 lim G N D₀ (inputEnd N D₀) U) (hd : G.L (logFour D₀) + 9 ≤ lim.depth) (μ : ℕ → ℤ)
    (h0 : μ 0 = N) (h1 : μ 1 = D₀) (hmX : MatAt μ 2 X) (hmY : MatAt μ (2 + N * D₀) Y) :
    Meets lim P Proc.preMain31 1 [0, 0] μ (tPre31 c G N D₀ + 30) fun _ μ' => InputReady31 G X Y
        μ' := by
  have hw := hlim.std.space_le
  have hconst := hlim.std.const_le
  have hspace := hlim.space
  have hfr3 := add_three_le_structEnd G N D₀ (inputEnd N D₀)
  refine Meets.of_body hP ?_
  -- a name for the product N D
  obtain ⟨area, harea⟩ : ∃ area, area = N * D₀ := ⟨_, rfl⟩
  have hmul : (N : ℤ) * (D₀ : ℤ) = area := by rw [harea]; push_cast; rfl
  have hfr : inputEnd N D₀ = 2 + area + area := by rw [harea]; rfl
  -- Size := mem[0] ; Dim := mem[1] ; Area := Size * Dim
  light_set N using h0
  light_set D₀ using h1
  light_set area using hmul
  -- MatY := 2 + Area ; Free := MatY + Area
  light_set (2 + area : ℕ)
  light_set (inputEnd N D₀ : ℕ) using hfr
  -- Res := pre31(Size, Dim, 2, MatY, Free)
  light_call (hpre N D₀ 2 (2 + area) (inputEnd N D₀) X Y U μ
    { one_le_D := hD, one_le_N := hN, lim := hlim, absX := hX, absY := hY, belowX := by omega
      belowY := by rw [Nat.mul_comm D₀ N]; omega } hmX (harea ▸ hmY) _
      (by omega)) with r μ' ⟨hready, hsame⟩
  -- Ans := 1
  light_set 1
  subst harea
  exact ⟨(hsame 0 (Or.inl (by omega))).trans h0, (hsame 1 (Or.inl (by omega))).trans h1, hready⟩

/-- **The main procedure of a query** returns the entry and keeps the memory ready. -/
theorem queryMain31_meets (hP : P[Proc.queryMain31]? = some queryMain31Body)
    (hq : QuerySpec31 lim P G) (hD : 1 ≤ D₀) (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hlim : Lim31 lim G N D₀ (inputEnd N D₀) U) (hd : 5 ≤ lim.depth) (μ : ℕ → ℤ)
    (hM : InputReady31 G X Y μ) (I J : Fin N) :
    Meets lim P Proc.queryMain31 1 [((I : ℕ) : ℤ), ((J : ℕ) : ℤ)] μ (tQuery31 G D₀ + 30)
      fun r μ' => r = (X * Y) I J ∧ InputReady31 G X Y μ' := by
  have hw := hlim.std.space_le
  have hconst := hlim.std.const_le
  have hspace := hlim.space
  have hfr3 := add_three_le_structEnd G N D₀ (inputEnd N D₀)
  refine Meets.of_body hP ?_
  obtain ⟨area, harea⟩ : ∃ area, area = N * D₀ := ⟨_, rfl⟩
  have hmul : (N : ℤ) * (D₀ : ℤ) = area := by rw [harea]; push_cast; rfl
  have hfr : inputEnd N D₀ = 2 + area + area := by rw [harea]; rfl
  -- Size := mem[0] ; Dim := mem[1] ; Area := Size * Dim
  light_set N using hM.cellN
  light_set D₀ using hM.cellD
  light_set area using hmul
  -- MatY := 2 + Area ; Free := MatY + Area
  light_set (2 + area : ℕ)
  light_set (inputEnd N D₀ : ℕ) using hfr
  -- Ans := query31(I, J, Size, Dim, 2, MatY, Free)
  light_call (hq N D₀ 2 (2 + area) (inputEnd N D₀) X Y U μ I J
    { one_le_D := hD, one_le_N := I.pos, lim := hlim, absX := hX, absY := hY, belowX := by omega
      belowY := by rw [Nat.mul_comm D₀ N]; omega }
    (harea ▸ hM.ready) _ (by omega)) with r μ' ⟨hr, hready, hsame⟩
  subst harea
  exact ⟨by simpa using hr, (hsame 0 (Or.inl (by omega))).trans hM.cellN,
    (hsame 1 (Or.inl (by omega))).trans hM.cellD, hready⟩

end Light.Sec4
