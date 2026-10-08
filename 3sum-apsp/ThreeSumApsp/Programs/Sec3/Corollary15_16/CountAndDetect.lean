/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Programs.LightModel

/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/

/-- One more parameter with the value 1 costs a factor `2^e`. -/
theorem polyBound_snoc_one (s e : ℕ) (ps : List ℕ) :
    polyBound s e (ps ++ [1]) = polyBound (s + e) e ps := by
  simp only [polyBound, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one,
    mul_pow, pow_add]
  norm_num
  ring

/-- Twice the bound leaves room for one more. -/
theorem polyBound_le_succ (s e : ℕ) (ps : List ℕ) :
    polyBound s e ps + 1 ≤ polyBound (1 + s) e ps := by
  have h1 := one_le_polyBound s e ps
  rw [← polyBound_mul]
  omega

/-! ## Counting with the thin matrix product -/

/-- A solver of the thin matrix product solves #Lop-AE-SparseTri. -/
theorem solvesN_count_of_thin {P : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN thinTask P p Tn need) :
    SolvesN lopCountTask P p (fun ps => Tn (ps ++ [1])) fun ps => need (ps ++ [1]) := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, hp, fun R lim d x μ fr hpre hok => ?_⟩
  obtain ⟨h1, -, h3⟩ := hpre
  have hpars : thinTask.pars x = lopCountTask.pars x ++ [1] := by
    simp only [thinTask, lopCountTask, List.cons_append, List.nil_append]
    rw [h3]
  have hrun := hb R lim d x μ fr h1 (hpars ▸ hok)
  rwa [hpars] at hrun

/-- A polynomially bounded need stays so when a parameter is fixed to 1. -/
theorem polyNeedN_snoc_one {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN fun ps => need (ps ++ [1]) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨s + e, e, fun ps => ?_⟩
  rw [← polyBound_snoc_one]
  exact h _

end LopHosts

open LopHosts

/-- **Counting common neighbours is a thin matrix product** (Section 3.1). -/
theorem claim_lopCountFromThinProduct : Claim.LopCountFromThinProduct lightModel := by
  refine ⟨0, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P, p, _, _, polyNeedN_snoc_one hneed, solvesN_count_of_thin hsol,
    fun n D w w' hn hD hw => ?_⟩
  have := htime n D w w' 1 1 hn hD le_rfl hw (by norm_num)
  simpa using this

/-! ## Detecting with counting -/

namespace LopArgs

/-- The local variables that hold the arguments of a solver of the thin matrix product or of a
lopsided triangle problem: N, D, w, U, x, y, wi, wj, out, fr. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev DD : ℕ := 1
@[inherit_doc N] abbrev W : ℕ := 2
@[inherit_doc N] abbrev U : ℕ := 3
@[inherit_doc N] abbrev X : ℕ := 4
@[inherit_doc N] abbrev Y : ℕ := 5
@[inherit_doc N] abbrev WI : ℕ := 6
@[inherit_doc N] abbrev WJ : ℕ := 7
@[inherit_doc N] abbrev OUT : ℕ := 8
@[inherit_doc N] abbrev FR : ℕ := 9

end LopArgs

open LopArgs in
/-- detect(N, D, w, U, x, y, wi, wj, out, fr): calls the counting solver on the same arguments, then
replaces every nonzero answer by 1.  Local 10 takes the result of the call and is then the
counter. -/
def lopDetectBody (pCount : ℕ) : Stmt :=
  .call pCount [v N, v DD, v W, v U, v X, v Y, v WI, v WJ, v OUT, v FR] 10 ;;
  .for 10 (v W) (.ite (M (v OUT +' v 10) =' k 0) .skip (.store (v OUT +' v 10) (k 1)))

/-- The number of steps of detect, if the counting solver takes Tn; the third parameter is w. -/
def lopDetectTime (Tn : List ℕ → ℕ) (ps : List ℕ) : ℕ := Tn ps + 20 * ps.getD 2 0 + 18

/-- What detect needs: one more level of calls. -/
def lopDetectNeed (need : List ℕ → Need) (ps : List ℕ) : Need :=
  ⟨(need ps).word, (need ps).cells, (need ps).depth + 1⟩

namespace LopHosts

/-- There is one answer for each wanted position. -/
theorem length_thinOut (N D : ℕ) (X Y : List ℤ) {WI WJ : List ℕ} {w : ℕ} (h1 : WI.length = w)
    (h2 : WJ.length = w) : (thinOut N D X Y WI WJ).length = w := by
  simp [thinOut, h1, h2]

/-- **detect** solves Lop-AE-SparseTri. -/
theorem detect_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN lopCountTask P₀ p Tn need) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : lopDetectTask.Pre x μ fr)
    (hok : (lopDetectNeed need (lopDetectTask.pars x)).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopDetectBody p) ⟨frame (lopDetectTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopDetectTime Tn (lopDetectTask.pars x))
      fun σ' => lopDetectTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hw := hok.space
  have hcells := hok.cells
  have hdep : d + ((need [x.N, x.D, x.w]).depth + 1) ≤ lim.depth := hok.depth
  have bO := hpre.1.belowOut
  have hlen := length_thinOut x.N x.D x.X x.Y hpre.1.lenWI hpre.1.lenWJ
  have hm : Meets lim (P₀ ++ R) p (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (Tn [x.N, x.D, x.w]) fun _ μ₁ =>
        Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ₁ fr x.out x.w :=
    hsol.meets R x hpre (hok.mono le_rfl le_rfl (by
      change d + 1 + (need [x.N, x.D, x.w]).depth ≤ d + ((need [x.N, x.D, x.w]).depth + 1)
      omega))
  change Ends lim (P₀ ++ R) d (lopDetectBody p)
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (Tn [x.N, x.D, x.w] + 20 * x.w + 18) _
  -- the counts
  refine Ends.callToThen hm fun r μ₁ ⟨hseg, hk⟩ => ?_
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ i, f i = if μ₁ (x.out + i) = 0 then 0 else 1 := ⟨_, fun _ => rfl⟩
  -- for i < w: the first i counts have been replaced
  refine Ends.forFrame (fun j μ' => μ' = wrote μ₁ x.out f j) x.w wrote_zero.symm ?round ?done
    (hT := by simp; omega)
  case round =>
    rintro j _ hj rfl
    have hread : wrote μ₁ x.out f j (x.out + j) = μ₁ (x.out + j) := wrote_rest (by omega)
    rw [← wrote_succ]
    -- if out[i] ≠ 0 then out[i] := 1
    refine Ends.iteLast (fun hc => Ends.skip ⟨rfl, ?_⟩) fun hc =>
      Ends.storeTo (x.out + j) 1 ⟨rfl, ?_⟩
    · have hc : μ₁ (x.out + j) = 0 := by simpa [hread] using hc
      have e : f j = wrote μ₁ x.out f j (x.out + j) := by rw [hf, if_pos hc, hread, hc]
      rw [e, Function.update_eq_self]
    · have hc : μ₁ (x.out + j) ≠ 0 := by simpa [hread] using hc
      rw [hf, if_neg hc]
  case done =>
    rintro _ rfl
    refine ⟨fun i hi => ?_, fun a ha => (wrote_rest ha.2).trans (hk a ha)⟩
    have hi' : i < x.w := by simpa [hlen] using hi
    rw [List.getElem_map, ← hseg i (by omega), ← hf]
    exact wrote_done hi'

/-- The need of detect is polynomially bounded if that of the counting solver is. -/
theorem polyNeedN_detect {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopDetectNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + s, e, fun ps => ?_⟩
  have h1 := polyBound_le_succ s e ps
  obtain ⟨a, b, c⟩ := h ps
  simp only [lopDetectNeed]
  omega

end LopHosts

open LopHosts

/-- **Detection from counting** (proof of Corollary 15). -/
theorem claim_lopDetectFromCount : Claim.LopDetectFromCount lightModel := by
  refine ⟨20, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopDetectBody p], P.length, lopDetectTime Tn, lopDetectNeed need,
    polyNeedN_detect hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopDetectBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact detect_spec hsol hpre hok
  · have h1 := htime n D w w' hn hD hw
    have h2 : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopDetectTime, List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    linarith

end Light.Sec3
