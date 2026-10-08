/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Passes
public import ThreeSumApsp.Programs.Tasks

/-!
# APSP from the (min,+)-product

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix ⌈log₂ n⌉
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most nU, where U bounds the edge weights.  The host below does this over an
arbitrary solver of the (min,+)-product.

ap(n, U, adj, w, out, fr) keeps the current matrix in the `n²` cells from `fr`, with `3nU` for `+∞`;
the product is written to the next `n²` cells, and the solver gets the free pointer `fr + 2n²`.
After each product the entries above `nU` are set back to `3nU` while the matrix is copied back.
The rounds are counted by doubling a number that starts at 1, as long as it is below `n`: these are
`⌈log₂ n⌉` rounds.

The proof follows the text: one round squares the matrix (`ApspHost.round_spec`), the last call
writes the answer (`ApspHost.out_spec`, `ApspHost.answer_correct`), and `ap_spec` puts the parts
together.  The result is `isHost_ap : IsHost mpTask apTask apTime apNeed`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace ApspHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the weights. -/
abbrev Bound : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The address of the answer. -/
abbrev Out : ℕ := 4
/-- The free pointer, where the current matrix is kept. -/
abbrev Free : ℕ := 5
/-- n². -/
abbrev Cells : ℕ := 6
/-- nU. -/
abbrev Thresh : ℕ := 7
/-- 3nU, which stands for +∞. -/
abbrev Big : ℕ := 8
/-- fr + n², where the product is written. -/
abbrev ProdAt : ℕ := 10
/-- fr + 2n², the free pointer of the solver. -/
abbrev SolverFree : ℕ := 11
/-- The power of two that counts the rounds. -/
abbrev Power : ℕ := 12
/-- Takes the results of the calls. -/
abbrev Res : ℕ := 13

end ApspHost

open ApspHost in
/-- One round: the product of the matrix with itself, clipped and copied back. -/
def apRound (pMP pClip : ℕ) : Stmt :=
  .call pMP [v Verts, v Big, v Free, v Free, v ProdAt, v SolverFree] Res ;;
  .call pClip [v Cells, v Thresh, v Big, v ProdAt, v Free] Res ;;
  .set Power (v Power +' v Power)

open ApspHost in
/-- ap(n, U, adj, w, out, fr), over the procedures number pMP (a solver of the (min,+)-product),
pInit, pClip and pOut (the three passes). -/
def apBody (pMP pInit pClip pOut : ℕ) : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Thresh (v Verts *' v Bound) ;;
  .set Big (k 3 *' v Thresh) ;;
  .set ProdAt (v Free +' v Cells) ;;
  .set SolverFree (v ProdAt +' v Cells) ;;
  .call pInit [v Verts, v Big, v AdjAt, v WtsAt, v Free] Res ;;
  .set Power (k 1) ;;
  .while (v Power <' v Verts) (apRound pMP pClip) ;;
  .call pOut [v Cells, v Big, v Free, v Out] Res

/-- The time of the host, given the time of the solver: `⌈log₂ n⌉` products at the bound `3nU`, and
`O(n²)` steps for each product and at both ends. -/
def apTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  Nat.clog 2 n * (T n (3 * (n * U)) + 23 * (n * n) + 29) + 53 * (n * n) + 17 * n + 65

/-- The need of the host, given the need of the solver. -/
def apNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := max (r n (3 * (n * U))).word (3 * (n * U))
  cells := 2 * (n * n) + (r n (3 * (n * U))).cells
  depth := (r n (3 * (n * U))).depth + 1

namespace ApspHost

/-- The locals of the host during the loop; pw is the power of two that counts the rounds, res the
result of the last call.  Local 9 is not used and stays 0. -/
abbrev locals (x : GraphInst) (fr : ℕ) (pw res : ℤ) : List ℤ :=
  [x.n, x.U, x.adj, x.w, x.out, fr, (x.n * x.n : ℕ), (x.n * x.U : ℕ), 3 * (x.n * x.U : ℕ), 0,
    (fr + x.n * x.n : ℕ), (fr + 2 * (x.n * x.n) : ℕ), pw, res]

/-- The invariant of the loop before round t: the matrix after t squarings stands at the free
pointer, and nothing below it has changed. -/
def Inv (x : GraphInst) (μ : ℕ → ℤ) (fr t : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals x fr (2 ^ t : ℕ) res), μ'⟩ ∧
    Seg μ' fr (squareList x.n x.U x.ADJ x.W t) ∧ Kept μ μ' fr

/-- The program has the solver and the three passes, the instance is as the task prescribes, and the
limits allow for the need of the host. -/
structure Ctx (P₀ R₀ : Program) (pMP pInit pClip pOut : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves mpTask P₀ pMP T r
  init : (P₀ ++ R₀)[pInit]? = some apInitBody
  clip : (P₀ ++ R₀)[pClip]? = some clipBody
  out : (P₀ ++ R₀)[pOut]? = some apOutBody
  pre : x.Pre μ fr
  ok : (apNeed r x.n x.U).Ok lim fr d

variable {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The arithmetic facts of the hypotheses as one conjunction: what the limits allow and what the
instance satisfies. -/
private theorem Ctx.places (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 3 * ((x.n : ℤ) * x.U) ≤ lim.word ∧
      ((r x.n (3 * (x.n * x.U))).word : ℤ) ≤ lim.word ∧
      fr + (2 * (x.n * x.n) + (r x.n (3 * (x.n * x.U))).cells) ≤ lim.space ∧
      d + ((r x.n (3 * (x.n * x.U))).depth + 1) ≤ lim.depth) ∧
      x.n ≤ x.n * x.n ∧ 1 ≤ x.n * x.U ∧ x.adj + x.n * x.n ≤ fr ∧ x.w + x.n * x.n ≤ fr ∧
      x.out + 2 * (x.n * x.n) ≤ fr :=
  ⟨⟨C.ok.space, by exact_mod_cast le_trans (Nat.cast_le.2 (le_max_right _ _)) C.ok.word,
    le_trans (by exact_mod_cast le_max_left _ _) C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.le_mul_of_pos_left _ C.pre.n_pos, Nat.mul_pos C.pre.n_pos C.pre.U_pos, C.pre.belowADJ,
    C.pre.belowW, C.pre.belowOut⟩

/-- The pairs that apOut writes for the matrix after ⌈log₂ n⌉ squarings are the answer. -/
private theorem answer_correct (hpre : x.Pre μ fr) {μ' : ℕ → ℤ}
    (hans : PairsAt μ' x.out (3 * (x.n * x.U : ℕ))
      (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n))) :
    ∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
      ∀ i j : Fin x.n, (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
        ∀ z : ℤ, dist i j = (z : WithTop ℤ) → μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z := by
  obtain ⟨dist, hdist, hentries⟩ :=
    squareList_distances hpre.n_pos hpre.U_pos hpre.leW hpre.noNegativeCycle
  refine ⟨dist, hdist, fun i j => ?_⟩
  have hq : i.val * x.n + j.val < (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length := by
    rw [length_squareList]
    exact Nat.mul_add_lt_mul i.isLt j.isLt
  obtain ⟨htop, hfin⟩ := hentries i j
  rw [entry, List.getD_eq_getElem _ _ hq] at htop hfin
  obtain ⟨hzero, hone⟩ := hans _ hq
  refine ⟨fun h => hzero (htop h), fun z hz => ?_⟩
  obtain ⟨hval, hne⟩ := hfin z hz
  exact hval ▸ hone (hval ▸ hne)

/-- **One round of the host** squares the matrix at the free pointer: a (min,+)-product, the
clipping of the large entries, and the doubling of Power. -/
private theorem round_spec (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) {t : ℕ}
    (ht : 2 ^ t < x.n) {σ : State} (hσ : Inv x μ fr t σ) :
    Ends lim (P₀ ++ R₀) d (apRound pMP pClip) σ (T x.n (3 * (x.n * x.U)) + 23 * (x.n * x.n) + 25)
      (Inv x μ fr (t + 1)) := by
  obtain ⟨res, μ', rfl, hseg, hkept⟩ := hσ
  have hplaces := C.places
  have hw := C.ok.space
  set L := squareList x.n x.U x.ADJ x.W t
  have hlen : L.length = x.n * x.n := length_squareList _ _ _ _ _
  have hlenP : (minPlusList x.n L L).length = x.n * x.n := length_minPlusList _ _ _
  have hle : AbsLe L ((3 * (x.n * x.U) : ℕ) : ℤ) :=
    abs_squareList_le C.pre.n_pos C.pre.U_pos C.pre.leW C.pre.noNegativeCycle t
  unfold apRound
  -- Res := pMP(Verts, Big, Free, Free, ProdAt, SolverFree)
  refine Ends.callToThen (C.solver.meets R₀
    (⟨x.n, 3 * (x.n * x.U), fr, fr, fr + x.n * x.n, L, L⟩ : MatInst) (fr + 2 * (x.n * x.n))
    ⟨C.pre.n_pos, by simp only; omega, hlen, hlen, hseg, hseg, hle, hle, by simp only; omega,
      by simp only; omega, by simp only; omega, Or.inl le_rfl, Or.inl le_rfl⟩
    { word := by simp only [mpTask]; omega
      cells := by simp only [mpTask]; omega
      space := hw
      depth := by simp only [mpTask]; omega }) ?_ (by simp [mpTask]) (by omega)
        (by simp [mpTask]; omega)
  rintro r₁ μ₁ ⟨hprod, hkept₁⟩
  simp only at hprod hkept₁
  -- Res := pClip(Cells, Thresh, Big, ProdAt, Free)
  refine Ends.callToThen (clip_meets C.clip (thr := (x.n * x.U : ℕ)) (INF := 3 * (x.n * x.U : ℕ))
    (dst := fr) hprod hw (by omega) (by omega) (Or.inr (by omega))) ?_ (by simp [hlenP])
    (by omega) (by simp [mpTask, hlenP]; omega)
  rintro r₂ μ₂ ⟨hseg₂, hsame₂⟩
  rw [hlenP] at hsame₂
  -- Power := Power + Power
  refine Ends.setTo (2 ^ (t + 1) : ℕ) ⟨r₂, μ₂, rfl, hseg₂, fun a ha => ?_⟩ ?_
    (by simp [mpTask, hlenP]; omega)
  · light_keep
  · have hpow : (2 : ℤ) ^ t < x.n := by exact_mod_cast ht
    have hpos : (0 : ℤ) ≤ 2 ^ t := by positivity
    simp [abs_le, pow_succ]
    omega

/-- **The end of the host**: the answer is written. -/
private theorem out_spec (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) {σ : State}
    (hσ : Inv x μ fr (Nat.clog 2 x.n) σ) :
    Ends lim (P₀ ++ R₀) d (.call pOut [v Cells, v Big, v Free, v Out] Res) σ (30 * (x.n * x.n) + 14)
      fun σ' => apTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨res, μ', rfl, hseg, hkept⟩ := hσ
  have hplaces := C.places
  have hw := C.ok.space
  have hlen : (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length = x.n * x.n :=
    length_squareList _ _ _ _ _
  -- Res := pOut(Cells, Big, Free, Out)
  refine Ends.callTo (apOut_meets C.out (INF := 3 * (x.n * x.U : ℕ)) (out := x.out) hseg hw
    (by omega) (by omega) (Or.inr (by omega))) ?_ (by simp [hlen]) (hT := by rw [hlen]; light_time)
  rintro r₂ μ₂ ⟨hans, hsame₂⟩
  rw [hlen] at hsame₂
  exact ⟨answer_correct C.pre hans, fun a ⟨ha, hout⟩ => (hsame₂ a hout).trans (hkept a ha)⟩

end ApspHost

open ApspHost in
/-- **The host is correct**, in every program that begins with the solver's program and has the
three passes. -/
theorem ap_spec {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}
    (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) :
    Ends lim (P₀ ++ R₀) d (apBody pMP pInit pClip pOut) ⟨frame (apTask.args x ++ [(fr : ℤ)]), μ⟩
      (apTime T x.n x.U) fun σ' => apTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hplaces := C.places
  have hw := C.ok.space
  have hpre := C.pre
  have hsquare : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  have hthresh : (0 : ℤ) ≤ (x.n : ℤ) * x.U := by positivity
  unfold apBody apTime
  change Ends _ _ _ _ ⟨frame [(x.n : ℤ), x.U, x.adj, x.w, x.out, fr], μ⟩ _ _
  -- Cells := Verts * Verts ; Thresh := Verts * Bound ; Big := 3 * Thresh
  light_set (x.n * x.n : ℕ)
  light_set (x.n * x.U : ℕ)
  light_set (3 * (x.n * x.U : ℕ))
  -- ProdAt := Free + Cells ; SolverFree := ProdAt + Cells
  light_set (fr + x.n * x.n : ℕ)
  light_set (fr + 2 * (x.n * x.n) : ℕ)
  -- Res := pInit(Verts, Big, AdjAt, WtsAt, Free)
  light_call (apInit_meets C.init (INF := 3 * (x.n * x.U : ℕ)) (A := fr) hpre.n_pos
    hpre.lenADJ hpre.lenW hpre.segADJ hpre.segW hw (by omega) (by omega) (by omega)
    (Or.inl hpre.belowADJ) (Or.inl hpre.belowW)) with r₁ μ₁ ⟨hseg₁, hsame₁⟩
  -- Power := 1
  light_set (2 ^ 0 : ℕ)
  -- while Power < Verts: the rounds
  refine Ends.next _ (Ends.whileConst (Inv x μ fr) (Nat.clog 2 x.n)
    (T x.n (3 * (x.n * x.U)) + 23 * (x.n * x.n) + 25)
    ⟨r₁, μ₁, rfl, hseg₁, fun a ha => hsame₁ a (Or.inl ha)⟩ ?round ?done le_rfl)
  case round =>
    rintro t σ ht hσ
    have hpow : 2 ^ t < x.n := Nat.pow_lt_of_lt_clog ht
    refine ⟨?_, ?_, round_spec C hpow hσ⟩ <;> obtain ⟨res, μ', rfl, -, -⟩ := hσ
    · exact ⟨trivial, trivial⟩
    · simpa using (by exact_mod_cast hpow : ((2 : ℤ) ^ t < x.n))
  case done =>
    intro σ hσ
    have hpow : x.n ≤ 2 ^ Nat.clog 2 x.n := Nat.le_pow_clog (by norm_num) x.n
    refine ⟨?_, ?_, (out_spec C hσ).mono (by light_time) fun _ h => h⟩ <;>
      obtain ⟨res, μ', rfl, -, -⟩ := hσ
    · exact ⟨trivial, trivial⟩
    · simpa using (by exact_mod_cast hpow : ((x.n : ℤ) ≤ 2 ^ Nat.clog 2 x.n))

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_apNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (apNeed r) := by
  unfold apNeed
  poly_need [hr.word, hr.cells, hr.depth]

/-- **APSP from the (min,+)-product**, as a host. -/
theorem isHost_ap : IsHost mpTask apTask apTime apNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => polyNeed_apNeed hr⟩
  refine ⟨[apInitBody, clipBody, apOutBody, apBody p P.length (P.length + 1) (P.length + 2)],
    P.length + 3, apBody p P.length (P.length + 1) (P.length + 2), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact ap_spec ⟨hs, by simp, by simp, by simp, hpre, hok⟩

end Light.Sec3
