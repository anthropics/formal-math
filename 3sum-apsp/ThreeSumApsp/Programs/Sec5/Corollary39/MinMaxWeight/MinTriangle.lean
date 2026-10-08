/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Programs.Sec5.Corollary39.MinMaxWeight.SearchRoutines
public import ThreeSumApsp.Programs.Sec5.Corollary39.Tasks
public import ThreeSumApsp.Sec5.Corollary39

/-!
# Min-Weight Triangle from Max-Weight Triangle, as a host

Proof of Corollary 39: "a minimum weight triangle is a maximum weight triangle for the negated
weights". minTri(n, U, ab, bc, ac, res, fr) writes the three negated matrices to the free pointer
and calls a solver of Max-Weight Triangle (`minTri_spec`, `isHost_minTri`).  The quoted sentence is
`Corollary39.isMinWeightTriangle_iff_negate`; the three matrices that the program writes are the
instance with the negated weights (`triOf_affL_neg`).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.KClique Light.Sec3

namespace MinTri

/-- The locals of minTri(n, U, ab, bc, ac, res, fr).  The arguments; the first one also takes the
result, and the free pointer is the address of the first negated matrix.  Then n², the addresses of
the other two negated matrices, the free pointer for the solver, and a result that is not used. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AddrAB : ℕ := 2
@[inherit_doc Size] abbrev AddrBC : ℕ := 3
@[inherit_doc Size] abbrev AddrAC : ℕ := 4
@[inherit_doc Size] abbrev Res : ℕ := 5
@[inherit_doc Size] abbrev Free : ℕ := 6
@[inherit_doc Size] abbrev Cells : ℕ := 7
@[inherit_doc Size] abbrev NegBC : ℕ := 9
@[inherit_doc Size] abbrev NegAC : ℕ := 10
@[inherit_doc Size] abbrev Top : ℕ := 11
@[inherit_doc Size] abbrev Unused : ℕ := 12

end MinTri

open MinTri in
/-- minTri(n, U, ab, bc, ac, res, fr). -/
def minTriBody (pMax pAff : ℕ) : Stmt :=
  .set Cells (v Size *' v Size) ;;
  .set NegBC (v Free +' v Cells) ;;
  .set NegAC (v NegBC +' v Cells) ;;
  .set Top (v NegAC +' v Cells) ;;
  .call pAff [v Cells, v AddrAB, k 0 -' k 1, k 0, v Free] Unused ;;
  .call pAff [v Cells, v AddrBC, k 0 -' k 1, k 0, v NegBC] Unused ;;
  .call pAff [v Cells, v AddrAC, k 0 -' k 1, k 0, v NegAC] Unused ;;
  .call pMax [v Size, v Bound, v Free, v NegBC, v NegAC, v Res, v Top] Size

/-- The time of minTri, if the solver of Max-Weight Triangle takes T n U steps. -/
def minTriTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 60 * (n * n) + 70 + T n U

/-- The need of minTri, if the solver of Max-Weight Triangle needs r n U. -/
def minTriNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := U + 8 + (r n U).word
  cells := 3 * (n * n) + 1 + (r n U).cells
  depth := (r n U).depth + 1

/-- The three negated matrices are the instance with the negated weights. -/
theorem triOf_affL_neg {n : ℕ} {AB BC AC : List ℤ} (lAB : AB.length = n * n)
    (lBC : BC.length = n * n) (lAC : AC.length = n * n) :
    triOf n (affL (-1) 0 AB) (affL (-1) 0 BC) (affL (-1) 0 AC) = negate (triOf n AB BC AC) := by
  unfold triOf negate
  congr 1 <;> funext i j
  · rw [getD_affL _ _ lAB, add_zero, neg_one_mul]
  · rw [getD_affL _ _ lBC, add_zero, neg_one_mul]
  · rw [getD_affL _ _ lAC, add_zero, neg_one_mul]

/-- **minTri** finds a minimum weight triangle: it negates the three matrices and asks for a maximum
weight triangle. -/
theorem minTri_spec {lim : Limits} {d : ℕ} {P₁ R' : Program} {pMax pAff : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hsol : Solves maxTriTask P₁ pMax T r)
    (hA : (P₁ ++ R')[pAff]? = some affineBody) {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (minTriNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P₁ ++ R') d (minTriBody pMax pAff)
      ⟨frame [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.res, fr], μ⟩ (minTriTime T x.n x.U)
      fun σ' => minTriTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  -- What the limits allow, and where the input lies.
  have hw := hok.space
  have hword : ((x.U + 8 + (r x.n x.U).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have hcells : fr + (3 * (x.n * x.n) + 1 + (r x.n x.U).cells) ≤ lim.space := hok.cells
  have hdepth : d + ((r x.n x.U).depth + 1) ≤ lim.depth := hok.depth
  have hab := hpre.belowAB
  have hbc := hpre.belowBC
  have hac := hpre.belowAC
  have hneg {l : List ℤ} (hl : AbsLe l x.U) : AbsLe (affL (-1) 0 l) x.U :=
    absLe_affL hl (.inr rfl) le_rfl (by omega) (by omega)
  unfold minTriBody minTriTime
  -- n², and the three places fr + n², fr + 2n², fr + 3n²
  light_set (x.n * x.n : ℕ)
  light_set (fr + x.n * x.n : ℕ)
  light_set (fr + 2 * (x.n * x.n) : ℕ)
  light_set (fr + 3 * (x.n * x.n) : ℕ)
  -- the three negated matrices; each call leaves the earlier matrices and the input alone
  light_call (affine_meets_of_absLe hA (-1) 0 fr hpre.segAB hpre.lenAB hpre.leAB
    (.inr rfl) hw hab) with _ μ₁ ⟨sAB, oAB⟩
  light_call (affine_meets_of_absLe hA (-1) 0 (fr + x.n * x.n)
    (hpre.segBC.keep (by light_keep [hpre.lenBC])) hpre.lenBC hpre.leBC (.inr rfl)
    hw) with _ μ₂ ⟨sBC, oBC⟩
  light_call (affine_meets_of_absLe hA (-1) 0 (fr + 2 * (x.n * x.n))
    (hpre.segAC.keep (by light_keep [hpre.lenAC])) hpre.lenAC hpre.leAC (.inr rfl) hw)
    with _ μ₃ ⟨sAC, oAC⟩
  -- a maximum weight triangle of the negated matrices
  refine Ends.callTo (T' := T x.n x.U) (hsol.meets R' (⟨⟨x.n, x.U, fr, fr + x.n * x.n,
      fr + 2 * (x.n * x.n), affL (-1) 0 x.AB, affL (-1) 0 x.BC, affL (-1) 0 x.AC⟩, x.res⟩ :
      FindInst) (fr + 3 * (x.n * x.n))
    (findPre_of_arrays hpre.n_pos hpre.U_pos
      { len := by simp [hpre.lenAB], bound := hneg hpre.leAB
        seg := sAB.keep (by light_keep [hpre.lenAB]) }
      { len := by simp [hpre.lenBC], bound := hneg hpre.leBC
        seg := sBC.keep (by light_keep [hpre.lenBC]) }
      { len := by simp [hpre.lenAC], seg := sAC, bound := hneg hpre.leAC } hpre.belowRes)
    ⟨by change ((r x.n x.U).word : ℤ) ≤ _; omega, by change _ + (r x.n x.U).cells ≤ _; omega, hw,
      by change _ + (r x.n x.U).depth ≤ _; omega⟩) ?_ (by simp [maxTriTask])
  -- It is a minimum weight triangle of the given matrices, and only cells from fr on and the answer
  -- have changed.
  rintro _ μ₄ ⟨⟨a, b, c, h1, h2, h3, hmax⟩, hk⟩
  replace hk : KeptBut μ₃ μ₄ (fr + 3 * (x.n * x.n)) x.res 3 := hk
  rw [triOf_affL_neg hpre.lenAB hpre.lenBC hpre.lenAC] at hmax
  refine ⟨⟨a, b, c, h1, h2, h3, (Corollary39.isMinWeightTriangle_iff_negate _ a b c).2 hmax⟩,
    fun y ⟨hy, hout⟩ => ?_⟩
  change μ₄ y = μ y
  rw [hk y ⟨by omega, hout⟩, oAC y (by omega), oBC y (by omega), oAB y (by omega)]

/-- The need of minTri is polynomially bounded if the need of the solver is. -/
theorem polyNeed_minTriNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (minTriNeed r) := by
  unfold minTriNeed
  poly_need [hr.word, hr.cells, hr.depth]

/-- **Min-Weight Triangle from Max-Weight Triangle.** -/
theorem isHost_minTri : IsHost maxTriTask minTriTask minTriTime minTriNeed := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, minTriBody p P.length], P.length + 1,
    minTriBody p P.length, by simp, fun R lim d x μ fr hpre hok => ?_⟩,
    fun r hr => polyNeed_minTriNeed hr⟩
  rw [List.append_assoc]
  exact minTri_spec hsol (by simp) hpre hok

end Light.Sec5
