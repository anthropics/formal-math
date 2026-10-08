/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Host
public import ThreeSumApsp.Programs.Sec5.Corollary39.MinMaxWeight.SearchRoutines
public import ThreeSumApsp.Programs.Sec5.Corollary39.Tasks

/-!
# Max-Weight Triangle from Exact Triangle, as a host

Proof of Corollary 39: "By [VW13, Theorem 3.3], finding a maximum weight triangle costs O(log² n)
times as much" as deciding whether there is a triangle of weight zero.

maxTri(n, U, ab, bc, ac, res, fr) first finds the weight W of a maximum weight triangle, by a search
from -3U upwards with the powers of two up to 6U (`mtWeight_spec`); the question whether there is a
triangle of weight at least w is an instance of Negative Triangle (`mtProbeW_spec`), which is solved
with the help of the solver of Exact Triangle.  Then it finds the largest a such that some triangle
of weight W has its first vertex ≥ a, then the largest b for this a, then the largest c for these a
and b, by three searches with the powers of two up to n (`mtStage_spec`, `mtVertices_spec`); here a
decision is an instance of Exact Triangle in which the other vertices are switched off by the weight
6U + 1 (`mtProbeZ_spec`).  All instances have the n vertices per part of the given one.  The four
searches are one loop (`search_spec`).  `isHost_maxTri` puts the procedures together.
-/

@[expose] public section

open ThreeSumApsp ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp.KClique Light.Sec3

/-! ## The text -/

namespace MaxTri

/-- The locals of maxTri(n, U, ab, bc, ac, res, fr).  The arguments; the free pointer is also the
address of the table of the powers of two up to 6U.  Then n²; the number of powers of two up to 6U;
three arrays of n² cells; the free pointer for the solvers; the weight 6U + 1 that switches off; the
bounds 10U and 7U + 1 of the instances; the vertices a and b; the weight W; the address of the table
of the powers of two up to n, and their number; a local that is never written and holds 0.  The
locals of the search lie between them. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AddrAB : ℕ := 2
@[inherit_doc Size] abbrev AddrBC : ℕ := 3
@[inherit_doc Size] abbrev AddrAC : ℕ := 4
@[inherit_doc Size] abbrev Res : ℕ := 5
@[inherit_doc Size] abbrev Free : ℕ := 6
@[inherit_doc Size] abbrev Cells : ℕ := 7
@[inherit_doc Size] abbrev LevelsU : ℕ := 9
@[inherit_doc Size] abbrev ArrAB : ℕ := 11
@[inherit_doc Size] abbrev ArrBC : ℕ := 12
@[inherit_doc Size] abbrev ArrAC : ℕ := 13
@[inherit_doc Size] abbrev Top : ℕ := 16
@[inherit_doc Size] abbrev Large : ℕ := 21
@[inherit_doc Size] abbrev BoundNT : ℕ := 22
@[inherit_doc Size] abbrev BoundET : ℕ := 23
@[inherit_doc Size] abbrev VertA : ℕ := 24
@[inherit_doc Size] abbrev VertB : ℕ := 25
@[inherit_doc Size] abbrev Weight : ℕ := 26
@[inherit_doc Size] abbrev TableN : ℕ := 27
@[inherit_doc Size] abbrev LevelsN : ℕ := 28
@[inherit_doc Size] abbrev Zero : ℕ := 29

end MaxTri

namespace Search

/-- The locals of the search: the address of the table of the powers of two, the number reached so
far, the number of powers that are still to be tried, the candidate, and the answer of the decision
for the candidate. -/
abbrev Table : ℕ := 8
@[inherit_doc Table] abbrev Reached : ℕ := 17
@[inherit_doc Table] abbrev Left : ℕ := 18
@[inherit_doc Table] abbrev Cand : ℕ := 19
@[inherit_doc Table] abbrev Answer : ℕ := 20

end Search

open Search in
/-- The search: while powers are left, the candidate is the number reached plus the largest power
that is left; probe puts the answer of the decision for the candidate into its local; if it is yes,
the candidate is reached. -/
def searchLoop (probe : Stmt) : Stmt :=
  .while (k 0 <' v Left) (
    .set Left (v Left -' k 1) ;;
    .set Cand (v Reached +' M (v Table +' v Left)) ;;
    probe ;;
    .ite (v Answer =' k 1) (.set Reached (v Cand)) .skip)

open MaxTri Search

/-- Sizes, bounds, the two tables of powers of two, and the addresses. -/
def mtInit (pPw : ℕ) : Stmt :=
  .set Cells (v Size *' v Size) ;;
  .set Large (k 6 *' v Bound +' k 1) ;;
  .set BoundNT (k 10 *' v Bound) ;;
  .set BoundET (k 7 *' v Bound +' k 1) ;;
  .call pPw [k 6 *' v Bound, v Free] LevelsU ;;
  .set TableN (v Free +' v LevelsU) ;;
  .call pPw [v Size, v TableN] LevelsN ;;
  .set ArrAB (v TableN +' v LevelsN) ;;
  .set ArrBC (v ArrAB +' v Cells) ;;
  .set ArrAC (v ArrBC +' v Cells) ;;
  .set Top (v ArrAC +' v Cells)

/-- The decision "some triangle has weight at least the candidate". -/
def mtProbeW (pNT pAff : ℕ) : Stmt :=
  .call pAff [v Cells, v AddrAC, k 0 -' k 1, v Cand -' k 1, v ArrAC] Answer ;;
  .call pNT [v Size, v BoundNT, v ArrAB, v ArrBC, v ArrAC, v Top] Answer

/-- The weight of a maximum weight triangle. -/
def mtWeight (pNT pAff : ℕ) : Stmt :=
  .call pAff [v Cells, v AddrAB, k 0 -' k 1, k 0, v ArrAB] Answer ;;
  .call pAff [v Cells, v AddrBC, k 0 -' k 1, k 0, v ArrBC] Answer ;;
  .set Table (v Free) ;;
  .set Left (v LevelsU) ;;
  .set Reached (k 0 -' k 3 *' v Bound) ;;
  searchLoop (mtProbeW pNT pAff) ;;
  .set Weight (v Reached)

/-- The decision "some triangle of weight W has a ≥ local ia, b ≥ local ib, c ≥ local ic". -/
def mtProbeZ (pET pMask ia ib ic : ℕ) : Stmt :=
  .call pMask [v Size, v AddrAB, v ia, v ib, v Large, v ArrAB] Answer ;;
  .call pMask [v Size, v AddrBC, v Zero, v ic, v Large, v ArrBC] Answer ;;
  .call pET [v Size, v BoundET, v ArrAB, v ArrBC, v ArrAC, v Top] Answer

/-- One of the three searches for a vertex. -/
def mtStage (pET pMask ia ib ic : ℕ) : Stmt :=
  .set Left (v LevelsN) ;;
  .set Reached (k 0) ;;
  searchLoop (mtProbeZ pET pMask ia ib ic)

/-- The three vertices. -/
def mtVertices (pET pAff pMask : ℕ) : Stmt :=
  .call pAff [v Cells, v AddrAC, k 1, k 0 -' v Weight, v ArrAC] Answer ;;
  .set Table (v TableN) ;;
  mtStage pET pMask Cand Zero Zero ;;
  .set VertA (v Reached) ;;
  mtStage pET pMask VertA Cand Zero ;;
  .set VertB (v Reached) ;;
  mtStage pET pMask VertA VertB Cand ;;
  .store (v Res) (v VertA) ;;
  .store (v Res +' k 1) (v VertB) ;;
  .store (v Res +' k 2) (v Reached)

/-- maxTri(n, U, ab, bc, ac, res, fr). -/
def maxTriBody (pET pNT pAff pMask pPw : ℕ) : Stmt :=
  mtInit pPw ;; mtWeight pNT pAff ;; mtVertices pET pAff pMask

/-- The time of maxTri, if the solver of Exact Triangle takes T n U steps. -/
def maxTriTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  60 * (n * n) + 178 + lv (6 * U) * (20 * (n * n) + 65 + ntTime T n (10 * U)) +
    lv n * (252 * (n * n) + 238 + 3 * T n (7 * U + 1))

/-- The need of maxTri, if the two solvers need re and rn. -/
def mtNeedAt (re rn : Need) (n U : ℕ) : Need where
  word := 60 * U + 2 * n + 40 + re.word + rn.word
  cells := lv (6 * U) + lv n + 3 * (n * n) + 1 + re.cells + rn.cells
  depth := re.depth + rn.depth + 1

/-- The need of maxTri, if the solver of Exact Triangle needs r n U. -/
def maxTriNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  mtNeedAt (r n (7 * U + 1)) (ntNeed r n (10 * U)) n U

/-! ## The local variables and the memory -/

/-- The address of the first of the three arrays. -/
def mtBase (x : FindInst) (fr : ℕ) : ℕ := fr + lv (6 * x.U) + lv x.n

/-- The local variables of maxTri after the beginning.  The eight parameters are those that change:
the address of the table of the search, the number reached, the number of powers that are left, the
candidate, the answer, the vertices a and b, and the weight W. -/
abbrev mtFrame (x : FindInst) (fr : ℕ) (tab lo left cand ans va vb W : ℤ) : List ℤ :=
  [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, (x.n * x.n : ℕ), tab, lv (6 * x.U), 0, mtBase x fr,
    (mtBase x fr + x.n * x.n : ℕ), (mtBase x fr + 2 * (x.n * x.n) : ℕ), 0, 0,
    (mtBase x fr + 3 * (x.n * x.n) : ℕ), lo, left, cand, ans, (6 * x.U + 1 : ℕ), (10 * x.U : ℕ),
    (7 * x.U + 1 : ℕ), va, vb, W, (fr + lv (6 * x.U) : ℕ), lv x.n]

/-- The two tables of powers of two are in the memory, and nothing below the free pointer has
changed. -/
structure MtMem (x : FindInst) (μ : ℕ → ℤ) (fr : ℕ) (μ' : ℕ → ℤ) : Prop where
  powU : Seg μ' fr (powList 2 (lv (6 * x.U)))
  powN : Seg μ' (fr + lv (6 * x.U)) (powList 2 (lv x.n))
  kept : Kept μ μ' fr

/-- A change from the first of the three arrays on keeps the tables. -/
theorem MtMem.keep {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ} {μ₁ μ₂ : ℕ → ℤ} (h : MtMem x μ fr μ₁)
    (hk : ∀ c < mtBase x fr, μ₂ c = μ₁ c) : MtMem x μ fr μ₂ := by
  unfold mtBase at hk
  exact ⟨h.powU.congr fun i hi => hk _ (by simp at hi; omega),
    h.powN.congr fun i hi => hk _ (by simp at hi; omega),
    fun c hc => (hk c (by have : c < fr := hc; omega)).trans (h.kept c hc)⟩

/-- What the proofs about maxTri use of the limits. -/
structure MtLim (lim : Limits) (d : ℕ) (x : FindInst) (fr : ℕ) (re rn : Need) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  word : ((60 * x.U + 2 * x.n + 40 : ℕ) : ℤ) ≤ lim.word
  cells : mtBase x fr + 3 * (x.n * x.n) < lim.space
  depth : d < lim.depth
  okE : re.Ok lim (mtBase x fr + 3 * (x.n * x.n)) (d + 1)
  okN : rn.Ok lim (mtBase x fr + 3 * (x.n * x.n)) (d + 1)

/-- `MtLim` follows from the need of maxTri. -/
theorem MtLim.of_ok {lim : Limits} {d : ℕ} {x : FindInst} {fr : ℕ} {re rn : Need}
    (h : (mtNeedAt re rn x.n x.U).Ok lim fr d) : MtLim lim d x fr re rn := by
  have hw : ((60 * x.U + 2 * x.n + 40 + re.word + rn.word : ℕ) : ℤ) ≤ lim.word := h.word
  have hc : fr + (lv (6 * x.U) + lv x.n + 3 * (x.n * x.n) + 1 + re.cells + rn.cells)
      ≤ lim.space := h.cells
  have hd : d + (re.depth + rn.depth + 1) ≤ lim.depth := h.depth
  exact ⟨h.space, by omega, by unfold mtBase; omega, by omega,
    ⟨by omega, by unfold mtBase; omega, h.space, by omega⟩,
    ⟨by omega, by unfold mtBase; omega, h.space, by omega⟩⟩

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The beginning -/

/-- **The beginning**: the locals are set, and the two tables are written. -/
theorem mtInit_spec {pPw : ℕ} (hPw : P[pPw]? = some pwBody) {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ}
    {re rn : Need} (hpre : x.Pre μ fr) (hl : MtLim lim d x fr re rn) :
    Ends lim P d (mtInit pPw) ⟨frame [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.res, fr], μ⟩
      (74 + 19 * lv (6 * x.U) + 19 * lv x.n) fun σ' => ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame (mtFrame x fr 0 0 0 0 0 0 0 0), μ'⟩ ∧ MtMem x μ fr μ' := by
  have hw := hl.space
  have hword := hl.word
  have hcells := hl.cells
  have hdepth := hl.depth
  have hU := hpre.U_pos
  have hbase : mtBase x fr = fr + lv (6 * x.U) + lv x.n := rfl
  unfold mtInit
  refine Ends.setToThen (x.n * x.n : ℕ) ?_
  refine Ends.setToThen (6 * x.U + 1 : ℕ) ?_
  refine Ends.setToThen (10 * x.U : ℕ) ?_
  refine Ends.setToThen (7 * x.U + 1 : ℕ) ?_
  -- the powers of two up to 6U, from fr on
  light_call (pw_meets hPw (x := 6 * x.U) (dst := fr) (by omega) hw (by omega)
    (by omega)) with _ μ₁ ⟨rfl, hpowU, hsame₁⟩
  light_set (fr + lv (6 * x.U) : ℕ)
  -- the powers of two up to n, behind them
  light_call (pw_meets hPw (x := x.n) (dst := fr + lv (6 * x.U)) hpre.n_pos hw
    (by omega) (by omega)) with _ μ₂ ⟨rfl, hpowN, hsame₂⟩
  -- the three arrays and the free pointer for the solvers
  light_set (mtBase x fr : ℕ)
  light_set (mtBase x fr + x.n * x.n : ℕ)
  light_set (mtBase x fr + 2 * (x.n * x.n) : ℕ)
  light_set (mtBase x fr + 3 * (x.n * x.n) : ℕ)
  refine ⟨μ₂, rfl,
    hpowU.keep, hpowN, fun c hc => ?_⟩
  have hc' : c < fr := hc
  rw [hsame₂ c (.inl (by omega)), hsame₁ c (.inl hc')]

/-! ## The search -/

/-- **The search** starts at a number lo₀ for which the decision is yes, while it is no for
lo₀ + 2^L, and ends at a number for which it is yes, while it is no for the next number.  Inv is
what the decisions need of the memory and keep. -/
theorem search_spec {probe : Stmt} {Pred : ℤ → Prop} {Inv : (ℕ → ℤ) → Prop} {x : FindInst}
    {fr tab L Tp : ℕ} {lo₀ va vb W : ℤ} (hw : (lim.space : ℤ) ≤ lim.word)
    (htab : tab + L < lim.space) (hword : |lo₀| + 2 ^ L ≤ lim.word)
    (hcell : ∀ μ, Inv μ → Seg μ tab (powList 2 L))
    (hprobe : ∀ (μ : ℕ → ℤ) (lo left cand ans : ℤ), Inv μ → lo₀ < cand → cand ≤ lo₀ + 2 ^ L →
      Ends lim P d probe ⟨frame (mtFrame x fr tab lo left cand ans va vb W), μ⟩ Tp fun σ' =>
        ∃ μ' : ℕ → ℤ, σ' = ⟨frame (mtFrame x fr tab lo left cand (flag (Pred cand)) va vb W), μ'⟩ ∧
          Inv μ')
    (h0 : Pred lo₀) (hL : ¬ Pred (lo₀ + 2 ^ L)) {μ : ℕ → ℤ} (hI : Inv μ) (cand ans : ℤ) :
    Ends lim P d (searchLoop probe) ⟨frame (mtFrame x fr tab lo₀ L cand ans va vb W), μ⟩
      (L * (Tp + 21) + 4) fun σ' => ∃ (lo cand ans : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (mtFrame x fr tab lo 0 cand ans va vb W), μ'⟩ ∧ Inv μ' ∧ Pred lo ∧
          ¬ Pred (lo + 1) ∧ lo₀ ≤ lo := by
  have habs := abs_le.1 (le_refl |lo₀|)
  unfold searchLoop
  -- after i rounds the change from yes to no lies between lo and lo + 2^(L - i)
  refine Ends.whileConst (fun i σ' => ∃ (lo cand ans : ℤ) (μ' : ℕ → ℤ),
      σ' = ⟨frame (mtFrame x fr tab lo (L - i : ℕ) cand ans va vb W), μ'⟩ ∧ Inv μ' ∧ Pred lo ∧
        ¬ Pred (lo + 2 ^ (L - i)) ∧ lo₀ ≤ lo ∧ lo + 2 ^ (L - i) ≤ lo₀ + 2 ^ L)
    L (Tp + 17) ?start ?round ?done (by light_time)
  case start => exact ⟨lo₀, cand, ans, μ, rfl, hI, h0, hL, le_rfl, le_rfl⟩
  case done =>
    rintro _ ⟨lo, cand, ans, μ', rfl, hI', hyes, hno, hlo, hhi⟩
    simp only [Nat.sub_self, pow_zero] at hno hhi
    exact ⟨by simp; omega, by simp, lo, cand, ans, μ', by simp, hI', hyes, hno, hlo⟩
  case round =>
    rintro i _ hi ⟨lo, cand, ans, μ', rfl, hI', hyes, hno, hlo, hhi⟩
    obtain ⟨t, ht⟩ : ∃ t, L - i = t + 1 := ⟨L - i - 1, by omega⟩
    rw [show L - (i + 1) = t by omega]
    rw [ht, pow_succ] at hno hhi
    rw [ht]
    have hpos : (0 : ℤ) < 2 ^ t := by positivity
    have hread : μ' (tab + t) = 2 ^ t := by
      rw [hcell μ' hI' t (by simp; omega), getElem_powList]
      simp
    refine ⟨by simp; omega, by simp, ?_⟩
    -- the candidate is lo + 2^t
    light_set t
    light_set (lo + 2 ^ t) using hread
    refine Ends.next Tp ((hprobe μ' lo t (lo + 2 ^ t) ans hI' (by omega) (by omega)).mono le_rfl ?_)
    rintro _ ⟨μ₂, rfl, hI₂⟩
    -- if the answer is yes, the candidate is reached
    refine Ends.iteLast (fun hc => ?_) fun hc => ?_
    · have hcand : Pred (lo + 2 ^ t) := flag_eq_one_iff.1 (by simpa using hc)
      exact Ends.setTo (lo + 2 ^ t) ⟨lo + 2 ^ t, _, _, μ₂, rfl, hI₂, hcand,
        by rwa [add_assoc, ← mul_two], by omega, by omega⟩
    · have hcand : ¬ Pred (lo + 2 ^ t) := fun h => hc (by simp [flag_of h])
      exact Ends.skip ⟨lo, _, _, μ₂, rfl, hI₂, hyes, hcand, hlo, by omega⟩

/-! ## The surroundings -/

/-- The program holds a solver of Exact Triangle, a solver of Negative Triangle, and the three
procedures affine, mask, pw. -/
structure MtCtx (P₁ R' : Program) (pET pNT pAff pMask pPw : ℕ) (T T' : ℕ → ℕ → ℕ)
    (r r' : ℕ → ℕ → Need) : Prop where
  et : Solves etTask P₁ pET T r
  nt : Solves ntTask P₁ pNT T' r'
  aff : (P₁ ++ R')[pAff]? = some affineBody
  mask : (P₁ ++ R')[pMask]? = some maskBody
  pw : (P₁ ++ R')[pPw]? = some pwBody

variable {P₁ R' : Program} {pET pNT pAff pMask pPw : ℕ} {T T' : ℕ → ℕ → ℕ} {r r' : ℕ → ℕ → Need}

/-! ## The weight of a maximum weight triangle -/

/-- What the decisions of the first search need of the memory and keep: the tables and the two
negated matrices. -/
structure MtMemW (x : FindInst) (μ : ℕ → ℤ) (fr : ℕ) (μ' : ℕ → ℤ) : Prop
    extends MtMem x μ fr μ' where
  negAB : Seg μ' (mtBase x fr) (affL (-1) 0 x.AB)
  negBC : Seg μ' (mtBase x fr + x.n * x.n) (affL (-1) 0 x.BC)

/-- y < 2^(lv y) ≤ 2y, in ℤ. -/
theorem two_pow_lv_cast {y : ℕ} (hy : 1 ≤ y) : (y : ℤ) < 2 ^ lv y ∧ (2 : ℤ) ^ lv y ≤ 2 * y :=
  ⟨by exact_mod_cast lt_two_pow_lv y, by exact_mod_cast two_pow_lv_le hy⟩

/-- **The decision of the first search**: is there a triangle of weight at least the candidate? -/
theorem mtProbeW_spec (C : MtCtx P₁ R' pET pNT pAff pMask pPw T T' r r') {x : FindInst}
    {μ μ₀ : ℕ → ℤ} {fr : ℕ} {re : Need} (hpre : x.Pre μ fr)
    (hl : MtLim lim d x fr re (r' x.n (10 * x.U))) (hI : MtMemW x μ fr μ₀)
    (tab lo left cand ans va vb W : ℤ) (hlo : -(3 * (x.U : ℤ)) < cand)
    (hhi : cand ≤ -(3 * (x.U : ℤ)) + 2 ^ lv (6 * x.U)) :
    Ends lim (P₁ ++ R') d (mtProbeW pNT pAff)
      ⟨frame (mtFrame x fr tab lo left cand ans va vb W), μ₀⟩
      (20 * (x.n * x.n) + 25 + T' x.n (10 * x.U)) fun σ' => ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame (mtFrame x fr tab lo left cand (flag (AtLeast x.n x.AB x.BC x.AC cand)) va vb
          W), μ'⟩ ∧ MtMemW x μ fr μ' := by
  have hw := hl.space
  have hword := hl.word
  have hcells := hl.cells
  have hdepth := hl.depth
  have hU := hpre.U_pos
  have hpow := (two_pow_lv_cast (y := 6 * x.U) (by omega)).2
  have hbase : fr ≤ mtBase x fr := by unfold mtBase; omega
  have hac := hpre.belowAC
  push_cast at hpow
  unfold mtProbeW
  -- the third matrix: the negated weights, with the candidate minus 1 added
  light_call (affine_meets_of_absLe C.aff (-1) (cand - 1)
    (mtBase x fr + 2 * (x.n * x.n)) (hpre.segAC.keep (by light_keep [hI.kept, hpre.lenAC]))
    hpre.lenAC hpre.leAC (.inr rfl) hw) with _ μ₁ ⟨hAC, hsame⟩
  have hAB := hI.negAB.of_sameOutside hsame (by simp [hpre.lenAB]; omega)
  have hBC := hI.negBC.of_sameOutside hsame (by simp [hpre.lenBC]; omega)
  -- has it a negative triangle?
  refine Ends.callTo (T' := T' x.n (10 * x.U)) (C.nt.meets R' (⟨x.n, 10 * x.U, mtBase x fr,
      mtBase x fr + x.n * x.n, mtBase x fr + 2 * (x.n * x.n), affL (-1) 0 x.AB, affL (-1) 0 x.BC,
      affL (-1) (cand - 1) x.AC⟩ : TriInst) (mtBase x fr + 3 * (x.n * x.n))
    (triPre_of_arrays hpre.n_pos (by omega)
      { len := by simp [hpre.lenAB], seg := hAB
        bound := absLe_affL hpre.leAB (.inr rfl) (by push_cast; omega) (by push_cast; omega)
          (by push_cast; omega) }
      { len := by simp [hpre.lenBC], seg := hBC
        bound := absLe_affL hpre.leBC (.inr rfl) (by push_cast; omega) (by push_cast; omega)
          (by push_cast; omega) }
      { len := by simp [hpre.lenAC], seg := hAC
        bound := absLe_affL hpre.leAC (.inr rfl) (by push_cast; omega) (by push_cast; omega)
          (by push_cast; omega) }) hl.okN) ?_ (by simp [ntTask])
  rintro _ μ₂ ⟨rfl, hkept⟩
  replace hkept : Kept μ₁ μ₂ (mtBase x fr + 3 * (x.n * x.n)) := hkept
  refine ⟨μ₂, ?_, hI.toMtMem.keep fun c hc => ?_, hAB.keep (by light_keep [hpre.lenAB]),
    hBC.keep (by light_keep [hpre.lenBC])⟩
  · rw [← flag_congr (neg_iff_atLeast hpre.lenAB hpre.lenBC hpre.lenAC cand)]
    rfl
  · rw [hkept c (show c < _ by omega), hsame c (.inl (by omega))]

/-- **The first search** finds the weight of a maximum weight triangle. -/
theorem mtWeight_spec (C : MtCtx P₁ R' pET pNT pAff pMask pPw T T' r r') {x : FindInst}
    {μ μ₀ : ℕ → ℤ} {fr : ℕ} {re : Need} (hpre : x.Pre μ fr)
    (hl : MtLim lim d x fr re (r' x.n (10 * x.U))) (hm : MtMem x μ fr μ₀) :
    Ends lim (P₁ ++ R') d (mtWeight pNT pAff) ⟨frame (mtFrame x fr 0 0 0 0 0 0 0 0), μ₀⟩
      (40 * (x.n * x.n) + 46 + lv (6 * x.U) * (20 * (x.n * x.n) + 46 + T' x.n (10 * x.U)))
      fun σ' => ∃ (tab lo cand ans W : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (mtFrame x fr tab lo 0 cand ans 0 0 W), μ'⟩ ∧ MtMem x μ fr μ' ∧
        AtLeast x.n x.AB x.BC x.AC W ∧ ¬ AtLeast x.n x.AB x.BC x.AC (W + 1) ∧
        |W| ≤ 3 * (x.U : ℤ) := by
  have hw := hl.space
  have hword := hl.word
  have hcells := hl.cells
  have hdepth := hl.depth
  have hU := hpre.U_pos
  obtain ⟨hpow₁, hpow₂⟩ := two_pow_lv_cast (y := 6 * x.U) (by omega)
  have hbase : mtBase x fr = fr + lv (6 * x.U) + lv x.n := rfl
  have hab := hpre.belowAB
  have hbc := hpre.belowBC
  have hS := abs_S_le (n := x.n) hpre.leAB hpre.leBC hpre.leAC
  push_cast at hpow₁ hpow₂
  unfold mtWeight
  -- the first two matrices, negated
  light_call (affine_meets_of_absLe C.aff (-1) 0 (mtBase x fr)
    (hpre.segAB.keep (by light_keep [hm.kept, hpre.lenAB])) hpre.lenAB hpre.leAB (.inr rfl) hw)
    with _ μ₁ ⟨hAB, hsame₁⟩
  light_call (affine_meets_of_absLe C.aff (-1) 0 (mtBase x fr + x.n * x.n)
    (hpre.segBC.keep (by light_keep [hm.kept, hpre.lenBC])) hpre.lenBC hpre.leBC (.inr rfl) hw)
    with _ μ₂ ⟨hBC, hsame₂⟩
  have hI : MtMemW x μ fr μ₂ :=
    ⟨hm.keep fun c hc => by rw [hsame₂ c (.inl (by omega)), hsame₁ c (.inl hc)],
      hAB.keep (by light_keep [hpre.lenAB]), hBC⟩
  -- the search from -3U upwards, with the powers of two up to 6U
  light_set fr
  light_set (lv (6 * x.U))
  light_set (-(3 * (x.U : ℤ)))
  light_piece (search_spec (Pred := AtLeast x.n x.AB x.BC x.AC) (Inv := MtMemW x μ fr)
    (tab := fr) (L := lv (6 * x.U)) (Tp := 20 * (x.n * x.n) + 25 + T' x.n (10 * x.U)) hw (by omega)
    (by rw [abs_neg, abs_of_nonneg (by omega)]; omega) (fun _ h => h.powU)
    (fun μ' lo left cand ans hμ' => mtProbeW_spec C hpre hl hμ' _ lo left cand ans _ _ _)
    ⟨⟨0, hpre.n_pos⟩, ⟨0, hpre.n_pos⟩, ⟨0, hpre.n_pos⟩, (hS _ _ _).1⟩
    (fun ⟨a, b, c, h⟩ => by have := (hS a b c).2; omega) hI _ _)
    with _ ⟨lo, cand, ans, μ₃, rfl, hI₃, hyes, hno, hlo⟩
  -- the weight
  obtain ⟨a, b, c, habc⟩ := hyes
  have := (hS a b c).2
  light_set lo
  exact ⟨_, _, _, _, _, μ₃, rfl, hI₃.toMtMem, ⟨a, b, c, habc⟩, hno,
    abs_le.2 ⟨by omega, by omega⟩⟩

/-! ## The three vertices -/

/-- What the decisions of the other three searches need of the memory and keep: the tables, and the
third matrix with W subtracted. -/
structure MtMemZ (x : FindInst) (μ : ℕ → ℤ) (fr : ℕ) (W : ℤ) (μ' : ℕ → ℤ) : Prop
    extends MtMem x μ fr μ' where
  shiftAC : Seg μ' (mtBase x fr + 2 * (x.n * x.n)) (affL 1 (-W) x.AC)

/-- The entries fit in a word, also with 6U + 1 added. -/
theorem mask_fits {l : List ℤ} {U : ℕ} (hle : AbsLe l U)
    (hword : ((7 * U + 1 : ℕ) : ℤ) ≤ lim.word) :
    ∀ y ∈ l, |y| ≤ lim.word ∧ |y + (6 * (U : ℤ) + 1)| ≤ lim.word := by
  intro y hy
  have := abs_le.1 (hle y hy)
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-- Some triangle of the instance with a ≥ a₀, b ≥ b₀, c ≥ c₀ has weight exactly W. -/
abbrev _root_.Light.Sec3.FindInst.Exact (x : FindInst) (W a₀ b₀ c₀ : ℤ) : Prop :=
  ExactFrom x.n x.AB x.BC x.AC W a₀ b₀ c₀

/-- The locals ia, ib, ic of the list l hold a, b, c. -/
structure HoldsThree (l : List ℤ) (ia ib ic : ℕ) (a b c : ℤ) : Prop where
  first : frame l ia = a
  second : frame l ib = b
  third : frame l ic = c

/-- **The decision of the other searches**: is there a triangle of weight W with vertices from a, b
and c on?  These three numbers are held by the locals ia, ib, ic, whatever the answer local holds.
-/
theorem mtProbeZ_spec (C : MtCtx P₁ R' pET pNT pAff pMask pPw T T' r r') {x : FindInst}
    {μ μ₀ : ℕ → ℤ} {fr : ℕ} {rn : Need} (hpre : x.Pre μ fr)
    (hl : MtLim lim d x fr (r x.n (7 * x.U + 1)) rn) {W : ℤ} (hW : |W| ≤ 3 * (x.U : ℤ))
    (hI : MtMemZ x μ fr W μ₀) {ia ib ic : ℕ} {a b c : ℤ} (tab lo left cand ans va vb : ℤ)
    (hargs : ∀ z, HoldsThree (mtFrame x fr tab lo left cand z va vb W) ia ib ic a b c) :
    Ends lim (P₁ ++ R') d (mtProbeZ pET pMask ia ib ic)
      ⟨frame (mtFrame x fr tab lo left cand ans va vb W), μ₀⟩
      (84 * (x.n * x.n) + 52 + T x.n (7 * x.U + 1)) fun σ' => ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame (mtFrame x fr tab lo left cand (flag (x.Exact W a b c)) va vb W), μ'⟩ ∧
          MtMemZ x μ fr W μ' := by
  have hw := hl.space
  have hword := hl.word
  have hcells := hl.cells
  have hdepth := hl.depth
  have hbase : fr ≤ mtBase x fr := by unfold mtBase; omega
  have hab := hpre.belowAB
  have hbc := hpre.belowBC
  have hWb := abs_le.1 hW
  unfold mtProbeZ
  -- the first matrix, with the rows below a and the columns below b switched off
  refine Ends.callToThen (mask_meets C.mask (src := x.ab) (dst := mtBase x fr) (r₀ := a) (c₀ := b)
    (Big := 6 * x.U + 1) hpre.n_pos (hpre.segAB.keep (by light_keep [hI.kept, hpre.lenAB]))
    hpre.lenAB hw (by omega) (by omega) (.inl (by omega)) (mask_fits hpre.leAB (by omega))) ?_
    ⟨by simp, by
      simp only [List.map_cons, List.map_nil, Expr.val, (hargs ans).first, (hargs ans).second]
      simp⟩
  rintro z₁ μ₁ ⟨hAB, hsame₁⟩
  -- the second matrix, with the columns below c switched off
  have hic₁ : frame (setLocal (mtFrame x fr tab lo left cand ans va vb W) Answer z₁) ic = c :=
    (hargs z₁).third
  refine Ends.callToThen (mask_meets C.mask (src := x.bc) (dst := mtBase x fr + x.n * x.n)
    (r₀ := 0) (c₀ := c) (Big := 6 * x.U + 1) hpre.n_pos
    (hpre.segBC.keep (by light_keep [hI.kept, hpre.lenBC])) hpre.lenBC hw (by omega) (by omega)
    (.inl (by omega)) (mask_fits hpre.leBC (by omega))) ?_
    ⟨by simp, by simp only [List.map_cons, List.map_nil, Expr.val, hic₁]; simp⟩
  rintro z₂ μ₂ ⟨hBC, hsame₂⟩
  have hAC := (hI.shiftAC.of_sameOutside hsame₁ (by omega)).of_sameOutside hsame₂ (by omega)
  -- is there a triangle of weight zero?
  refine Ends.callTo (T' := T x.n (7 * x.U + 1)) (C.et.meets R' (⟨x.n, 7 * x.U + 1, mtBase x fr,
      mtBase x fr + x.n * x.n, mtBase x fr + 2 * (x.n * x.n), maskL x.n a b (6 * x.U + 1) x.AB,
      maskL x.n 0 c (6 * x.U + 1) x.BC, affL 1 (-W) x.AC⟩ : TriInst)
      (mtBase x fr + 3 * (x.n * x.n))
    (triPre_of_arrays hpre.n_pos (by omega)
      { len := by simp, seg := hAB.keep
        bound := maskL_le hpre.lenAB hpre.leAB _ _ }
      { len := by simp, seg := hBC, bound := maskL_le hpre.lenBC hpre.leBC _ _ }
      { len := by simp [hpre.lenAC], seg := hAC
        bound := absLe_affL hpre.leAC (.inl rfl) (by push_cast; omega) (by push_cast; omega)
          (by push_cast; omega) }) hl.okE) ?_ (by simp [etTask])
  rintro _ μ₃ ⟨rfl, hkept⟩
  replace hkept : Kept μ₂ μ₃ (mtBase x fr + 3 * (x.n * x.n)) := hkept
  refine ⟨μ₃, ?_, hI.toMtMem.keep fun y hy => ?_, hAC.keep (by light_keep [hpre.lenAC])⟩
  · rw [← flag_congr (zero_iff_exactFrom hpre.lenAC hpre.leAB hpre.leBC hpre.leAC hW a b c)]
    rfl
  · rw [hkept y (show y < _ by omega), hsame₂ y (.inl (by omega)), hsame₁ y (.inl hy)]

/-- **One of the three searches for a vertex**: the three numbers of the decision are functions a,
b, c of the candidate. -/
theorem mtStage_spec (C : MtCtx P₁ R' pET pNT pAff pMask pPw T T' r r') {x : FindInst}
    {μ μ₀ : ℕ → ℤ} {fr : ℕ} {rn : Need} (hpre : x.Pre μ fr)
    (hl : MtLim lim d x fr (r x.n (7 * x.U + 1)) rn) {W : ℤ} (hW : |W| ≤ 3 * (x.U : ℤ))
    (hI : MtMemZ x μ fr W μ₀) {ia ib ic : ℕ} {a b c : ℤ → ℤ} {va vb : ℤ}
    (hargs : ∀ lo left cand ans, HoldsThree
      (mtFrame x fr (fr + lv (6 * x.U) : ℕ) lo left cand ans va vb W) ia ib ic (a cand) (b cand)
      (c cand))
    (h0 : x.Exact W (a 0) (b 0) (c 0)) (hn : ∀ z, (x.n : ℤ) ≤ z → ¬ x.Exact W (a z) (b z) (c z))
    (lo left cand ans : ℤ) :
    Ends lim (P₁ ++ R') d (mtStage pET pMask ia ib ic)
      ⟨frame (mtFrame x fr (fr + lv (6 * x.U) : ℕ) lo left cand ans va vb W), μ₀⟩
      (8 + lv x.n * (84 * (x.n * x.n) + 73 + T x.n (7 * x.U + 1)))
      fun σ' => ∃ (lo cand ans : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (mtFrame x fr (fr + lv (6 * x.U) : ℕ) lo 0 cand ans va vb W), μ'⟩ ∧
        MtMemZ x μ fr W μ' ∧ x.Exact W (a lo) (b lo) (c lo) ∧
        ¬ x.Exact W (a (lo + 1)) (b (lo + 1)) (c (lo + 1)) := by
  have hw := hl.space
  have hword := hl.word
  have hcells := hl.cells
  obtain ⟨hpow₁, hpow₂⟩ := two_pow_lv_cast hpre.n_pos
  have hbase : mtBase x fr = fr + lv (6 * x.U) + lv x.n := rfl
  unfold mtStage
  refine Ends.setToThen (lv x.n) (Ends.setToThen 0 ?_)
  -- the search from 0 upwards, with the powers of two up to n
  light_piece (search_spec (Pred := fun z => x.Exact W (a z) (b z) (c z))
    (Inv := MtMemZ x μ fr W) (tab := fr + lv (6 * x.U)) (L := lv x.n)
    (Tp := 84 * (x.n * x.n) + 52 + T x.n (7 * x.U + 1)) (lo₀ := 0) hw (by omega)
    (by simp; omega) (fun _ h => h.powN)
    (fun μ' lo left cand ans hμ' _ _ => mtProbeZ_spec C hpre hl hW hμ' _ lo left cand ans va vb
      (hargs lo left cand))
    h0 (hn _ (by omega)) hI _ _) with _ ⟨lo', cand', ans', μ', rfl, hI', hyes, hno, -⟩
  exact ⟨lo', cand', ans', μ', rfl, hI', hyes, hno⟩

/-- **The three vertices** of a triangle of maximum weight are written to the place for the answer.
-/
theorem mtVertices_spec (C : MtCtx P₁ R' pET pNT pAff pMask pPw T T' r r') {x : FindInst}
    {μ μ₀ : ℕ → ℤ} {fr : ℕ} {rn : Need} (hpre : x.Pre μ fr)
    (hl : MtLim lim d x fr (r x.n (7 * x.U + 1)) rn) (hm : MtMem x μ fr μ₀) {W : ℤ}
    (hyes : AtLeast x.n x.AB x.BC x.AC W) (hno : ¬ AtLeast x.n x.AB x.BC x.AC (W + 1))
    (hW : |W| ≤ 3 * (x.U : ℤ)) (tab lo cand ans : ℤ) :
    Ends lim (P₁ ++ R') d (mtVertices pET pAff pMask)
      ⟨frame (mtFrame x fr tab lo 0 cand ans 0 0 W), μ₀⟩
      (20 * (x.n * x.n) + 58 + 3 * (lv x.n * (84 * (x.n * x.n) + 73 + T x.n (7 * x.U + 1))))
      fun σ' => maxTriTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hw := hl.space
  have hword := hl.word
  have hcells := hl.cells
  have hdepth := hl.depth
  have hbase : fr ≤ mtBase x fr := by unfold mtBase; omega
  have hac := hpre.belowAC
  have hres := hpre.belowRes
  have hWb := abs_le.1 hW
  unfold mtVertices
  -- the third matrix, with W subtracted
  light_call (affine_meets_of_absLe C.aff 1 (-W) (mtBase x fr + 2 * (x.n * x.n))
    (hpre.segAC.keep (by light_keep [hm.kept, hpre.lenAC])) hpre.lenAC hpre.leAC (.inl rfl) hw)
    with _ μ₁ ⟨hAC, hsame⟩
  have hI₁ : MtMemZ x μ fr W μ₁ := ⟨hm.keep fun y hy => hsame y (.inl (by omega)), hAC⟩
  light_set (fr + lv (6 * x.U) : ℕ)
  -- the first vertex
  light_piece (mtStage_spec C hpre hl hW hI₁ (a := id) (b := fun _ => 0) (c := fun _ => 0)
    (fun _ _ _ _ => ⟨rfl, rfl, rfl⟩) (exactFrom_zero hyes hno)
    (fun _ hz => not_exactFrom (.inl hz)) _ _ _ _) with _ ⟨a₀, _, _, μ₂, rfl, hI₂, ha, ha'⟩
  light_set a₀
  -- the second vertex
  light_piece (mtStage_spec C hpre hl hW hI₂ (a := fun _ => a₀) (b := id)
    (c := fun _ => 0) (fun _ _ _ _ => ⟨rfl, rfl, rfl⟩) ha
    (fun _ hz => not_exactFrom (.inr (.inl hz))) _ _ _ _) with _ ⟨b₀, _, _, μ₃, rfl, hI₃, hb, hb'⟩
  light_set b₀
  -- the third vertex
  light_piece (mtStage_spec C hpre hl hW hI₃ (a := fun _ => a₀) (b := fun _ => b₀)
    (c := id) (fun _ _ _ _ => ⟨rfl, rfl, rfl⟩) hb
    (fun _ hz => not_exactFrom (.inr (.inr hz))) _ _ _ _) with _ ⟨c₀, _, _, μ₄, rfl, hI₄, hc, hc'⟩
  obtain ⟨a, b, c, rfl, rfl, rfl, hmax⟩ := isMax_of_searches hno ha' hb' hc hc'
  -- the answer
  light_store x.res a
  light_store (x.res + 1) b
  light_store (x.res + 2) c
  refine ⟨⟨a, b, c, by simp, by simp, by simp, hmax⟩, fun y hy => ?_⟩
  obtain ⟨hfr, hout⟩ : y < fr ∧ Outside x.res 3 y := hy
  change Function.update (Function.update (Function.update μ₄ _ _) _ _) _ _ y = μ y
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]
  exact hI₄.kept y hfr

/-! ## The procedure -/

/-- **maxTri** finds a triangle of maximum weight. -/
theorem maxTri_spec (C : MtCtx P₁ R' pET pNT pAff pMask pPw T T' r r') {x : FindInst} {μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (mtNeedAt (r x.n (7 * x.U + 1)) (r' x.n (10 * x.U)) x.n x.U).Ok lim fr d) :
    Ends lim (P₁ ++ R') d (maxTriBody pET pNT pAff pMask pPw)
      ⟨frame [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.res, fr], μ⟩
      (60 * (x.n * x.n) + 178 + lv (6 * x.U) * (20 * (x.n * x.n) + 65 + T' x.n (10 * x.U)) +
        lv x.n * (252 * (x.n * x.n) + 238 + 3 * T x.n (7 * x.U + 1)))
      fun σ' => maxTriTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hl := MtLim.of_ok hok
  unfold maxTriBody
  refine Ends.seq _ _ ((mtInit_spec C.pw hpre hl).mono le_rfl ?_) (le_of_eq (by ring) :
    (74 + 19 * lv (6 * x.U) + 19 * lv x.n) + ((40 * (x.n * x.n) + 46 +
      lv (6 * x.U) * (20 * (x.n * x.n) + 46 + T' x.n (10 * x.U))) + (20 * (x.n * x.n) + 58 +
      3 * (lv x.n * (84 * (x.n * x.n) + 73 + T x.n (7 * x.U + 1))))) ≤ _)
  rintro _ ⟨μ₁, rfl, hm₁⟩
  refine Ends.seq _ _ ((mtWeight_spec C hpre hl hm₁).mono le_rfl ?_) le_rfl
  rintro _ ⟨tab, lo, cand, ans, W, μ₂, rfl, hm₂, hyes, hno, hW⟩
  exact mtVertices_spec C hpre hl hm₂ hyes hno hW tab lo cand ans

/-- The need of maxTri is polynomially bounded if the need of the solver is. -/
theorem polyNeed_maxTriNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (maxTriNeed r) := by
  have hneg := polyNeed_ntNeed hr
  unfold maxTriNeed mtNeedAt lv
  poly_need [hr.word, hr.cells, hr.depth, hneg.word, hneg.cells, hneg.depth]

/-- **Max-Weight Triangle from Exact Triangle**: from every solver of Exact Triangle, the procedures
of the host for Negative Triangle and affine, mask, pw, maxTri make a solver of Max-Weight Triangle.
Every call of the given solver is on an instance with the same number of vertices. -/
theorem isHost_maxTri : IsHost etTask maxTriTask maxTriTime maxTriNeed := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_maxTriNeed hr⟩
  obtain ⟨R₁, p₁, hnt⟩ := isHost_nt.1 P p T r hsol
  -- the four new procedures stand behind those of the host for Negative Triangle
  obtain ⟨o, ho⟩ : ∃ o, o = (P ++ R₁).length := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Program,
      B = [affineBody, maskBody, pwBody, maxTriBody p p₁ o (o + 1) (o + 2)] := ⟨_, rfl⟩
  have look (R : Program) {i : ℕ} {body : Stmt} (h : B[i]? = some body) :
      ((P ++ R₁) ++ (B ++ R))[o + i]? = some body := ho ▸ getElem?_append_append R h
  refine ⟨R₁ ++ B, o + 3, maxTriBody p p₁ o (o + 1) (o + 2), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have := look [] (i := 3) (by rw [hB]; rfl)
    rwa [List.append_nil, List.append_assoc] at this
  · rw [show P ++ (R₁ ++ B) ++ R = (P ++ R₁) ++ (B ++ R) by simp only [List.append_assoc]]
    exact maxTri_spec ⟨hsol.append R₁, hnt, look R (i := 0) (by rw [hB]; rfl),
      look R (i := 1) (by rw [hB]; rfl), look R (i := 2) (by rw [hB]; rfl)⟩ hpre hok

end Light.Sec5
