/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Logs
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.CopyBlock
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem21b.AllPairs

/-!
# All pairs with a witness, with an algorithm that finds a negative triangle

The middle step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).  Given three n ×
n matrices X, Y, V, the host marks all pairs (i, j) for which some k has X[i,k] + Y[k,j] < V[i,j].
It cuts the three ranges into p = ⌈n/s⌉ blocks of s = ⌈n^{1/3}⌉ indices and visits the p³ triples of
blocks.  In each round it forms the s × s × s instance of the current triple, with the weights
X[i,k], Y[k,j], and -V[i,j], or 2U + 1 if (i, j) is already marked, and asks the solver for a
negative triangle.  A triangle that comes back marks a new pair; if there is none, the host goes on
to the next triple. So there are at most p³ + n² rounds.  The last block of a range is moved back so
that it ends at n (blocks may overlap), so there are no padding vertices.

The result is isHost_pairs : IsHost findTask pairsTask pairsTime pairsNeed.  The proof goes from the
inside to the outside: the third matrix of an instance (mask_meets); one question (ask_meets, with
the instance askInst and the meaning AskPost of the answer); the parts of a round (off_spec,
mark_spec, advance_spec); what a round achieves (Progress.mark and Progress.next: less is left to
do); a round (round_spec, with the invariant PairsInv); the host (pairs_spec; when nothing is left
to do the marks are the answer, Progress.complete).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedures -/

namespace Mask

/-- The local variables of mask: the arguments len, F (Large), ac (Mat), tmp (Flags), and the
counter q (Index). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Large : ℕ := 1
@[inherit_doc Len] abbrev Mat : ℕ := 2
@[inherit_doc Len] abbrev Flags : ℕ := 3
@[inherit_doc Len] abbrev Index : ℕ := 4

end Mask

open Mask in
/-- mask(len, F, ac, tmp): for q < len, ac[q] := F if tmp[q] = 1, and ac[q] := -ac[q] otherwise. -/
def maskBody : Stmt :=
  .for Index (v Len) (
    .ite (M (v Flags +' v Index) =' k 1)
      (.store (v Mat +' v Index) (v Large))
      (.store (v Mat +' v Index) (k 0 -' M (v Mat +' v Index))))

namespace Ask

/-- The local variables of ask: the arguments n, s (Side), F (Large), x, y, v, out, the offsets oI,
oK, oJ, and fr (Free); then s² (Area), and results that are not used. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev Side : ℕ := 1
@[inherit_doc N] abbrev Large : ℕ := 2
@[inherit_doc N] abbrev X : ℕ := 3
@[inherit_doc N] abbrev Y : ℕ := 4
@[inherit_doc N] abbrev V : ℕ := 5
@[inherit_doc N] abbrev Out : ℕ := 6
@[inherit_doc N] abbrev OffI : ℕ := 7
@[inherit_doc N] abbrev OffK : ℕ := 8
@[inherit_doc N] abbrev OffJ : ℕ := 9
@[inherit_doc N] abbrev Free : ℕ := 10
@[inherit_doc N] abbrev Area : ℕ := 11
@[inherit_doc N] abbrev Unused : ℕ := 12

end Ask

open Ask in
/-- ask(n, s, F, x, y, v, out, oI, oK, oJ, fr): forms the instance of the triple of blocks at the
offsets oI, oK, oJ in the cells from fr (three matrices of s² cells; the block of marks is copied
behind them for a moment), and asks the solver for a negative triangle, with the place for the
answer at fr + 3s² and the free pointer fr + 3s² + 3.  The answer goes to local 0 and so is the
result. -/
def askBody (pFind pSub pMask : ℕ) : Stmt :=
  .set Area (v Side *' v Side) ;;
  .call pSub [v N, v Side, v X, v OffI, v OffK, v Free] Unused ;;
  .call pSub [v N, v Side, v Y, v OffK, v OffJ, v Free +' v Area] Unused ;;
  .call pSub [v N, v Side, v V, v OffI, v OffJ, v Free +' v Area +' v Area] Unused ;;
  .call pSub [v N, v Side, v Out, v OffI, v OffJ, v Free +' v Area +' v Area +' v Area] Unused ;;
  .call pMask [v Area, v Large, v Free +' v Area +' v Area, v Free +' v Area +' v Area +' v Area]
    Unused ;;
  .call pFind [v Side, v Large, v Free, v Free +' v Area, v Free +' v Area +' v Area,
    v Free +' v Area +' v Area +' v Area,
    v Free +' v Area +' v Area +' v Area +' k 3] 0

namespace Pairs

/-- The local variables of allPairs: the arguments n, U, x, y, v, out, fr (Free); the side s of a
block and the number p of blocks; the numbers I, K, J of the three blocks and their offsets oI, oK,
oJ; F = 2U + 1 (Large); the address fr + 3s² of the solver's answer; the last result (Reply). -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev X : ℕ := 2
@[inherit_doc N] abbrev Y : ℕ := 3
@[inherit_doc N] abbrev V : ℕ := 4
@[inherit_doc N] abbrev Out : ℕ := 5
@[inherit_doc N] abbrev Free : ℕ := 6
@[inherit_doc N] abbrev Side : ℕ := 7
@[inherit_doc N] abbrev Blocks : ℕ := 8
@[inherit_doc N] abbrev BlockI : ℕ := 9
@[inherit_doc N] abbrev BlockK : ℕ := 10
@[inherit_doc N] abbrev BlockJ : ℕ := 11
@[inherit_doc N] abbrev OffI : ℕ := 12
@[inherit_doc N] abbrev OffK : ℕ := 13
@[inherit_doc N] abbrev OffJ : ℕ := 14
@[inherit_doc N] abbrev Large : ℕ := 15
@[inherit_doc N] abbrev Answer : ℕ := 16
@[inherit_doc N] abbrev Reply : ℕ := 17

end Pairs

open Pairs in
/-- The offset of the block whose number is in the local src, into the local dst: I s, or n - s if
n < I s + s. -/
def offStmt (dst src : ℕ) : Stmt :=
  .set dst (v src *' v Side) ;;
  .ite (v N <' v dst +' v Side) (.set dst (v N -' v Side)) .skip

open Pairs in
/-- The next triple of blocks. -/
def advanceStmt : Stmt :=
  .set BlockJ (v BlockJ +' k 1) ;;
  .ite (v BlockJ =' v Blocks)
    (.set BlockJ (k 0) ;; .set BlockK (v BlockK +' k 1) ;;
     .ite (v BlockK =' v Blocks) (.set BlockK (k 0) ;; .set BlockI (v BlockI +' k 1)) .skip)
    .skip

open Pairs in
/-- The pair that the solver has found is marked: out[(oI + a) n + (oJ + c)] := 1, where a and c
stand in the first and the third cell of the solver's answer. -/
def markStmt : Stmt :=
  .store (v Out +' (v OffI +' M (v Answer)) *' v N +' (v OffJ +' M (v Answer +' k 2))) (k 1)

open Pairs in
/-- One round of allPairs: the offsets of the three blocks, the question, and then either a new mark
or the next triple of blocks. -/
def pairsRound (pAsk : ℕ) : Stmt :=
  offStmt OffI BlockI ;; offStmt OffK BlockK ;; offStmt OffJ BlockJ ;;
  .call pAsk [v N, v Side, v Large, v X, v Y, v V, v Out, v OffI, v OffK, v OffJ, v Free] Reply ;;
  .ite (v Reply =' k 1) markStmt advanceStmt

open Pairs in
/-- p := ⌈n/s⌉, by counting up. -/
def countStmt : Stmt :=
  .set Blocks (k 0) ;;
  .while (v Blocks *' v Side <' v N) (.set Blocks (v Blocks +' k 1))

open Pairs in
/-- allPairs(n, U, x, y, v, out, fr): s, p, F and the address of the solver's answer; no pair is
marked; then the rounds, from the first triple of blocks on. -/
def pairsBody (pCbrt pFill pAsk : ℕ) : Stmt :=
  .call pCbrt [v N] Side ;;
  countStmt ;;
  .set Large (v U +' v U +' k 1) ;;
  .set Answer (v Free +' k 3 *' (v Side *' v Side)) ;;
  .call pFill [v Out, v N *' v N, k 0] Reply ;;
  .set BlockI (k 0) ;; .set BlockK (k 0) ;; .set BlockJ (k 0) ;;
  .while (v BlockI <' v Blocks) (pairsRound pAsk)

/-! ## Time and need -/

/-- The number of steps of mask. -/
def maskTime (len : ℕ) : ℕ := 25 * len + 6

/-- The number of steps of ask, if the solver takes T. -/
def askTime (T : ℕ → ℕ → ℕ) (s U : ℕ) : ℕ :=
  4 * subCopyTime s + maskTime (s * s) + T s (2 * U + 1) + 100

/-- The number of steps of one round of allPairs: three offsets, the question, and a mark or the
next triple of blocks. -/
def Pairs.roundTime (T : ℕ → ℕ → ℕ) (s U : ℕ) : ℕ := askTime T s U + 83

/-- **The number of steps of allPairs**, if the solver that finds negative triangles takes T: at
most p³ + n² rounds, with s = ⌈n^{1/3}⌉ (see cbrtLeast_eq_cbrtCeil) and p = ⌈n/s⌉, each with one
question at size s and bound 2U + 1. -/
def pairsTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  40 * n ^ 2 + 80 +
    (blockCount n (cbrtLeast n) ^ 3 + n ^ 2) *
        (220 * cbrtLeast n ^ 2 + 250 + T (cbrtLeast n) (2 * U + 1))

/-- **What allPairs needs**, if the solver needs r: the numbers up to 8n + 2U + 4, room for four
blocks and the solver's answer, three more levels of calls, and what the solver needs at the size
⌈n^{1/3}⌉ and the bound 2U + 1. -/
def pairsNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 8 * n + 2 * U + 4 + (r (cbrtLeast n) (2 * U + 1)).word
  cells := 4 * (cbrtLeast n * cbrtLeast n) + 3 + (r (cbrtLeast n) (2 * U + 1)).cells
  depth := 3 + (r (cbrtLeast n) (2 * U + 1)).depth

/-- The procedures that the host appends to the program of a solver whose program has o procedures
and whose procedure number is p: copy, fill, subCopy, cbrtCeil, mask, ask, allPairs, with the
numbers o, …, o + 6. -/
def pairsProcs (o p : ℕ) : Program :=
  [copyBody, fillBody, subCopyBody o, cbrtCeilBody, maskBody, askBody p (o + 2) (o + 4),
    pairsBody (o + 3) (o + 1) (o + 5)]

namespace Pairs

variable {P₀ R : Program} {p₀ pCbrt pFill pAsk pSub pCopy pMask : ℕ} {T : ℕ → ℕ → ℕ}
  {r : ℕ → ℕ → Need}

/-- The surroundings of allPairs: a solver that finds negative triangles, and the procedures that
the host adds. -/
structure Ctx (P₀ R : Program) (p pCbrt pFill pAsk pSub pCopy pMask : ℕ) (T : ℕ → ℕ → ℕ)
    (r : ℕ → ℕ → Need) : Prop where
  sol : Solves findTask P₀ p T r
  sub : (P₀ ++ R)[pSub]? = some (subCopyBody pCopy)
  copy : (P₀ ++ R)[pCopy]? = some copyBody
  mask : (P₀ ++ R)[pMask]? = some maskBody
  cbrt : (P₀ ++ R)[pCbrt]? = some cbrtCeilBody
  fill : (P₀ ++ R)[pFill]? = some fillBody
  ask : (P₀ ++ R)[pAsk]? = some (askBody p pSub pMask)

/-! ## The third matrix of an instance -/

/-- **mask** turns the block A of V held at ac into the third matrix of the instance, with the block
O of marks held at tmp, and changes nothing else. -/
theorem mask_meets {P : Program} {pMask : ℕ} (hp : P[pMask]? = some maskBody) {μ : ℕ → ℤ}
    {ac tmp U : ℕ} (len : ℕ) (F : ℤ) {A O : List ℤ} (hA : Seg μ ac A) (hO : Seg μ tmp O)
    (hlen : A.length = len ∧ O.length = len) (hle : AbsLe A U)
    (hplace : ac + len ≤ tmp ∧ tmp + len ≤ lim.space)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ (U : ℤ) ≤ lim.word) :
    Meets lim P pMask d [(len : ℤ), F, ac, tmp] μ (maskTime len) fun _ μ' =>
      Seg μ' ac (maskNeg F O A) ∧ SameOutside μ μ' ac len := by
  obtain ⟨lA, lO⟩ := hlen
  obtain ⟨hw, hU⟩ := hlim
  unfold maskTime
  set f : ℕ → ℤ := fun i => (maskNeg F O A).getD i 0 with hf
  -- for q < len: before round q, the first q entries of the new matrix have been written
  refine .of_body hp (Ends.forFrame (fun q μ' => μ' = wrote μ ac f q) len wrote_zero.symm
    ?round ?done (hT := by simp; omega))
  case round =>
    rintro q _ hq rfl
    -- The two cells that the round reads are as at the start.
    have hmark : wrote μ ac f q (tmp + q) = O[q] := hO.keep.get (by omega)
    have hval : wrote μ ac f q (ac + q) = A[q] := (wrote_rest (by omega)).trans (hA q (by omega))
    have hfits := abs_le.1 ((hle.getElem (i := q) (by omega)).trans hU)
    have hfq : f q = if O[q] = 1 then F else -A[q] := by
      rw [hf]
      simp only [getD_maskNeg (F := F) (show q < O.length by omega) (show q < A.length by omega),
        List.getD_eq_getElem _ _ (show q < O.length by omega),
        List.getD_eq_getElem _ _ (show q < A.length by omega)]
    -- if tmp[q] = 1
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp [Limits.Addr, abs_le]; omega)
    · -- ac[q] := F
      refine Ends.storeTo (ac + q) F ⟨rfl, ?_⟩
      rw [← wrote_succ, hfq, if_pos (by simpa [hmark] using hc)]
    · -- ac[q] := 0 - ac[q]
      refine Ends.storeTo (ac + q) (-A[q]) ⟨rfl, ?_⟩ (by simp [Limits.Addr, abs_le, hval]; omega)
      rw [← wrote_succ, hfq, if_neg (by simpa [hmark] using hc)]
  case done =>
    rintro _ rfl
    dsimp only
    exact ⟨fun i hi => (wrote_done (by simpa [lA, lO] using hi)).trans
      (List.getD_eq_getElem _ _ hi), sameOutside_wrote le_rfl⟩

/-! ## One question -/

/-- The instance of the triple of blocks at the offsets oI, oK, oJ, with its three matrices at fr,
fr + s², fr + 2s² and the place for the answer behind them: the weights X[i,k], Y[k,j], and -V[i,j],
or 2U + 1 if the pair (i, j) is marked in O. -/
def askInst (q : PairsInst) (O : List ℤ) (fr s oI oK oJ : ℕ) : FindInst where
  n := s
  U := 2 * q.U + 1
  ab := fr
  bc := fr + s * s
  ac := fr + s * s + s * s
  AB := subMat q.n s oI oK q.X
  BC := subMat q.n s oK oJ q.Y
  AC := maskNeg (2 * (q.U : ℤ) + 1) (subMat q.n s oI oJ O) (subMat q.n s oI oJ q.V)
  res := fr + s * s + s * s + s * s

/-- It is an instance, once its three matrices stand at their places. -/
theorem askInst_pre {q : PairsInst} {O : List ℤ} {μ μ' : ℕ → ℤ} {fr s oI oK oJ : ℕ}
    (hpre : q.Pre μ fr) (hs : 1 ≤ s) (sAB : Seg μ' fr (askInst q O fr s oI oK oJ).AB)
    (sBC : Seg μ' (fr + s * s) (askInst q O fr s oI oK oJ).BC)
    (sAC : Seg μ' (fr + s * s + s * s) (askInst q O fr s oI oK oJ).AC) :
    (askInst q O fr s oI oK oJ).Pre μ' (fr + 3 * (s * s) + 3) :=
  have hU : (0 : ℤ) ≤ ((2 * q.U + 1 : ℕ) : ℤ) := by positivity
  have hF : |2 * (q.U : ℤ) + 1| ≤ ((2 * q.U + 1 : ℕ) : ℤ) := abs_le.2 ⟨by omega, by omega⟩
  have hle : ∀ L : List ℤ, AbsLe L q.U → ∀ z ∈ L, |z| ≤ ((2 * q.U + 1 : ℕ) : ℤ) := fun L hL z hz =>
    (hL z hz).trans (by push_cast; omega)
  { n_pos := hs
    U_pos := by change 1 ≤ 2 * q.U + 1; omega
    lenAB := by simp [askInst]
    lenBC := by simp [askInst]
    lenAC := by simp [askInst]
    segAB := sAB
    segBC := sBC
    segAC := sAC
    leAB := abs_le_of_mem_subMat hU (hle _ hpre.leX)
    leBC := abs_le_of_mem_subMat hU (hle _ hpre.leY)
    leAC := abs_le_of_mem_maskNeg hF (abs_le_of_mem_subMat hU (hle _ hpre.leV))
    belowAB := by simp only [askInst]; omega
    belowBC := by simp only [askInst]; omega
    belowAC := by simp only [askInst]; omega
    belowRes := by simp only [askInst]; omega
    apartAB := by simp only [askInst]; omega
    apartBC := by simp only [askInst]; omega
    apartAC := by simp only [askInst]; omega }

/-- What ask returns: 0, and in the triple of blocks every pair with a witness is marked; or 1, and
the cells res and res + 2 hold a and c such that (oI + a, oJ + c) is an unmarked pair with a
witness. -/
def AskPost (q : PairsInst) (O : List ℤ) (s oI oK oJ res : ℕ) (z : ℤ) (μ' : ℕ → ℤ) : Prop :=
  (z = 0 ∧ BlockDone q.n s q.X q.Y q.V O oI oK oJ) ∨
  (z = 1 ∧ ∃ a < s, ∃ b < s, ∃ c < s, μ' res = a ∧ μ' (res + 2) = c ∧
    entry q.n O (oI + a) (oJ + c) ≠ 1 ∧ Witness q.n q.X q.Y q.V (oI + a) (oK + b) (oJ + c))

/-- What the answer of the solver means for the triple of blocks. -/
theorem askPost_of_post {q : PairsInst} {O : List ℤ} {μ μ₅ μ₆ : ℕ → ℤ} {fr fr' s oI oK oJ : ℕ}
    {z : ℤ} (hpre : q.Pre μ fr) (h : findTask.Post (askInst q O fr s oI oK oJ) μ₅ fr' z μ₆) :
    AskPost q O s oI oK oJ (fr + 3 * (s * s)) z μ₆ := by
  obtain ⟨hz, hyes, -⟩ := h
  have hres : fr + 3 * (s * s) = fr + s * s + s * s + s * s := by omega
  by_cases hneg : (blockTri q.n s (2 * (q.U : ℤ) + 1) q.X q.Y q.V O oI oK oJ).HasNegativeTriangle
  · have hone : z = 1 := hz.trans (flag_of hneg)
    obtain ⟨a, b, c, ma, -, mc, hS⟩ := hyes hone
    obtain ⟨hun, hlt⟩ := unmarked_of_neg (O := O) (V := q.V) hpre.leX hpre.leY hS
    exact .inr ⟨hone, a, a.2, b, b.2, c, c.2, hres ▸ ma, hres ▸ mc, hun, hlt⟩
  · exact .inl ⟨hz.trans (flag_of_not hneg), blockDone_of_not hneg⟩

/-- **ask** asks the solver about the triple of blocks at the offsets oI, oK, oJ, and changes no
cell below the free pointer. -/
theorem ask_meets (C : Ctx P₀ R p₀ pCbrt pFill pAsk pSub pCopy pMask T r) {q : PairsInst}
    {μ : ℕ → ℤ} {fr : ℕ} {O : List ℤ} (s oI oK oJ : ℕ) (hpre : q.Pre μ fr) (hO : Seg μ q.out O)
    (lO : O.length = q.n * q.n) (hs : 1 ≤ s) (hin : oI + s ≤ q.n ∧ oK + s ≤ q.n ∧ oJ + s ≤ q.n)
    (hok : (r s (2 * q.U + 1)).Ok lim (fr + 3 * (s * s) + 3) (d + 1))
    (hlim : fr + 4 * (s * s) ≤ lim.space ∧ 2 * (q.U : ℤ) + 1 ≤ lim.word ∧ d + 1 < lim.depth) :
    Meets lim (P₀ ++ R) pAsk d
      [(q.n : ℤ), s, 2 * (q.U : ℤ) + 1, q.x, q.y, q.v, q.out, oI, oK, oJ, fr] μ (askTime T s q.U)
      fun z μ' => Kept μ μ' fr ∧ AskPost q O s oI oK oJ (fr + 3 * (s * s)) z μ' := by
  have hw := hok.space
  have hcells := hok.cells
  light_facts hpre
  refine .of_body C.ask ?_
  unfold askBody askTime
  -- area := s * s
  refine Ends.setToThen (s * s : ℕ) ?_
  -- subCopy(n, s, x, oI, oK, fr)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oI oK fr hpre.segX hpre.lenX (by omega)
    (by omega)) ?_
  rintro _ μ₁ ⟨sX, same₁⟩
  -- subCopy(n, s, y, oK, oJ, fr + area)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oK oJ (fr + s * s) hpre.segY.keep hpre.lenY
    (by omega) (by omega)) ?_
  rintro _ μ₂ ⟨sY, same₂⟩
  -- subCopy(n, s, v, oI, oJ, fr + area + area)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oI oJ (fr + s * s + s * s) hpre.segV.keep
    hpre.lenV (by omega) (by omega)) ?_
  rintro _ μ₃ ⟨sV, same₃⟩
  -- subCopy(n, s, out, oI, oJ, fr + area + area + area)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oI oJ (fr + s * s + s * s + s * s) hO.keep lO
    (by omega) (by omega)) ?_
  rintro _ μ₄ ⟨sO, same₄⟩
  -- mask(area, F, fr + area + area, fr + area + area + area)
  refine Ends.callToThen (mask_meets C.mask (s * s) (2 * (q.U : ℤ) + 1) sV.keep sO
    ⟨by simp, by simp⟩ (abs_le_of_mem_subMat (by positivity) hpre.leV) (by omega) (by omega)) ?_
  rintro _ μ₅ ⟨sM, same₅⟩
  -- The solver is asked about the three matrices.
  refine Ends.callTo (T' := T s (2 * q.U + 1)) (C.sol.meets R (askInst q O fr s oI oK oJ)
    (fr + 3 * (s * s) + 3) (askInst_pre hpre hs sX.keep sY.keep sM) hok) ?_
    (by simp [findTask, askInst, abs_le]; omega)
  rintro z μ₆ hpost
  have same₆ : KeptBut μ₅ μ₆ _ (fr + s * s + s * s + s * s) 3 := hpost.2.2
  exact ⟨by light_keep, askPost_of_post hpre hpost⟩

/-! ## The parts of a round -/

variable {q : PairsInst} {s p I K J : ℕ} {O : List ℤ}

/-- The local variables of allPairs during the rounds, as a list. -/
abbrev locals (q : PairsInst) (fr s p I K J : ℕ) (oI oK oJ z : ℤ) : List ℤ :=
  [q.n, q.U, q.x, q.y, q.v, q.out, fr, s, p, I, K, J, oI, oK, oJ, 2 * (q.U : ℤ) + 1,
    (fr + 3 * (s * s) : ℕ), z]

/-- (I', K', J') is the triple of blocks after (I, K, J); after the last triple comes (p, 0, 0). -/
structure Next (p I K J I' K' J' : ℕ) : Prop where
  leI : I' ≤ p
  ltK : K' < p
  ltJ : J' < p
  top : I' = p → K' = 0 ∧ J' = 0
  idx : tripleIdx p I' K' J' = tripleIdx p I K J + 1

/-- advanceStmt goes on to the next triple of blocks. -/
theorem advance_spec {P : Program} {q : PairsInst} {μ : ℕ → ℤ} {fr s p I K J : ℕ} {oI oK oJ z : ℤ}
    (hlt : I < p ∧ K < p ∧ J < p) (hword : (p : ℤ) + 1 ≤ lim.word) :
    Ends lim P d advanceStmt ⟨frame (locals q fr s p I K J oI oK oJ z), μ⟩ 24 fun σ' =>
      ∃ I' K' J', σ' = ⟨frame (locals q fr s p I' K' J' oI oK oJ z), μ⟩ ∧
        Next p I K J I' K' J' := by
  unfold advanceStmt
  -- J := J + 1; if J = p
  refine Ends.setToThen (J + 1 : ℕ) ?_
  refine Ends.iteLast (fun hJ => ?_) (fun hJ => ?_)
  · obtain rfl : J + 1 = p := by simp at hJ; omega
    -- J := 0; K := K + 1; if K = p
    refine Ends.setToThen (0 : ℕ) ?_
    refine Ends.setToThen (K + 1 : ℕ) ?_
    refine Ends.iteLast (fun hK => ?_) (fun hK => ?_)
    · obtain rfl : K = J := by simpa using hK
      -- K := 0; I := I + 1
      refine Ends.setToThen (0 : ℕ) ?_
      refine Ends.setTo (I + 1 : ℕ) ?_
      exact ⟨I + 1, 0, 0, rfl,
        { leI := by omega, ltK := by omega, ltJ := by omega, top := fun _ => ⟨rfl, rfl⟩
          idx := tripleIdx_succ_I K I }⟩
    · have hK' : K ≠ J := by simpa using hK
      exact Ends.skip ⟨I, K + 1, 0, rfl,
        { leI := by omega, ltK := by omega, ltJ := by omega, top := fun h => by omega
          idx := tripleIdx_succ_K J I K }⟩
  · have hJ' : J + 1 ≠ p := by simp at hJ; omega
    exact Ends.skip ⟨I, K, J + 1, rfl,
      { leI := by omega, ltK := by omega, ltJ := by omega, top := fun h => by omega
        idx := tripleIdx_succ_J p I K J }⟩

/-- offStmt puts the offset of block number I into the local dst and changes nothing else.  The text
is used for three pairs of locals, so this is stated like a rule, for any list l of locals and any
Q: h says that Q holds of the state afterwards, and in a proof it is the goal that remains. -/
theorem off_spec {P : Program} {l : List ℤ} {μ : ℕ → ℤ} {dst src : ℕ} {Q : State → Prop} (n s I : ℕ)
    (h : Q ⟨frame (setLocal l dst (blockOff n s I : ℕ)), μ⟩) (hI : I * s < n ∧ s ≤ n)
    (hword : 2 * (n : ℤ) ≤ lim.word) (hN : frame l N = n := by rfl)
    (hS : frame l Side = s := by rfl) (hsrc : frame l src = I := by rfl)
    (hdst : N ≠ dst ∧ Side ≠ dst := by decide) :
    Ends lim P d (offStmt dst src) ⟨frame l, μ⟩ 14 Q := by
  rw [← update_frame_setLocal, blockOff] at h
  generalize frame l = loc at *
  have hN' : ∀ z, Function.update loc dst z N = n := fun z => by
    rw [Function.update_of_ne hdst.1, hN]
  have hS' : ∀ z, Function.update loc dst z Side = s := fun z => by
    rw [Function.update_of_ne hdst.2, hS]
  unfold offStmt
  -- dst := I * s
  refine Ends.setThen ?_ (by simp [hsrc, hS]; omega)
  -- if n < dst + s
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp [hsrc, hS, hS', abs_le]; omega)
  · -- dst := n - s
    rw [if_neg (by simp [hsrc, hS, hS', hN'] at hc; omega)] at h
    exact Ends.setLast (by simpa [hS', hN', Nat.cast_sub hI.2] using h)
      (by simp [hS', hN', abs_le]; omega)
  · rw [if_pos (by simp [hsrc, hS, hS', hN'] at hc; omega)] at h
    exact Ends.skip (by simpa [hsrc, hS] using h)

/-- markStmt marks the pair (oI + a, oJ + c), where a and c stand in the solver's answer. -/
theorem mark_spec {P : Program} {μ : ℕ → ℤ} {fr oI oK oJ a c : ℕ} {z : ℤ}
    (ha : μ (fr + 3 * (s * s)) = a) (hc : μ (fr + 3 * (s * s) + 2) = c)
    (hlt : oI + a < q.n ∧ oJ + c < q.n) (hout : q.out + q.n * q.n ≤ fr)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fr + 3 * (s * s) + 3 ≤ lim.space) :
    Ends lim P d markStmt ⟨frame (locals q fr s p I K J oI oK oJ z), μ⟩ 24 fun σ' =>
      σ' = ⟨frame (locals q fr s p I K J oI oK oJ z),
        Function.update μ (q.out + ((oI + a) * q.n + (oJ + c))) 1⟩ := by
  have hn : q.n ≤ q.n * q.n := Nat.le_mul_self _
  have hidx : (oI + a) * q.n + (oJ + c) < q.n * q.n := Nat.mul_add_lt_mul hlt.1 hlt.2
  have hidxZ : 0 ≤ ((oI : ℤ) + a) * q.n ∧
      ((oI : ℤ) + a) * q.n + ((oJ : ℤ) + c) < (q.n : ℤ) * q.n := by
    exact_mod_cast And.intro (Nat.zero_le _) hidx
  have hres : ((fr : ℤ) + 3 * ((s : ℤ) * s)).toNat = fr + 3 * (s * s) := by omega
  have hres2 : ((fr : ℤ) + 3 * ((s : ℤ) * s) + 2).toNat = fr + 3 * (s * s) + 2 := by omega
  unfold markStmt
  exact Ends.storeTo (q.out + ((oI + a) * q.n + (oJ + c))) 1 rfl
    (by simp [Limits.Addr, abs_le, -abs_mul, hres, hres2, ha, hc]; omega)

/-! ## The invariant -/

/-- How far the rounds have come: the marks O are right, and in the triples of blocks before
(I, K, J) every pair with a witness is marked. -/
structure Progress (q : PairsInst) (s p I K J : ℕ) (O : List ℤ) : Prop where
  leI : I ≤ p
  ltK : K < p
  ltJ : J < p
  top : I = p → K = 0 ∧ J = 0
  marks : Marks q.n q.X q.Y q.V O
  done : ∀ I' < p, ∀ K' < p, ∀ J' < p, tripleIdx p I' K' J' < tripleIdx p I K J →
    BlockDone q.n s q.X q.Y q.V O (blockOff q.n s I') (blockOff q.n s K') (blockOff q.n s J')

/-- What is left to do: the number of triples of blocks from (I, K, J) on, plus the number of
unmarked pairs. -/
def todo (p I K J : ℕ) (O : List ℤ) : ℕ := (p * p * p - tripleIdx p I K J) + O.count 0

/-- A new mark on a pair with a witness: less is left to do. -/
theorem Progress.mark (h : Progress q s p I K J O) {i j k : ℕ}
    (hlt : i < q.n ∧ j < q.n ∧ k < q.n) (hun : entry q.n O i j ≠ 1)
    (hit : Witness q.n q.X q.Y q.V i k j) :
    Progress q s p I K J (O.set (i * q.n + j) 1) ∧
      todo p I K J (O.set (i * q.n + j) 1) < todo p I K J O := by
  obtain ⟨hi, hj, hk⟩ := hlt
  have hidx : i * q.n + j < O.length := h.marks.len ▸ Nat.mul_add_lt_mul hi hj
  have hcount := count_set_one hidx
    ((h.marks.sound i hi j hj).resolve_right fun hmarked => hun hmarked.1)
  exact ⟨{ h with
    marks := h.marks.set hi hj ⟨k, hk, hit⟩
    done := fun I' hI' K' hK' J' hJ' hbefore => (h.done I' hI' K' hK' J' hJ' hbefore).set hidx },
    by unfold todo; omega⟩

/-- The current triple of blocks is done, and the next one comes: less is left to do. -/
theorem Progress.next (h : Progress q s p I K J O) (hI : I < p)
    (hblock : BlockDone q.n s q.X q.Y q.V O (blockOff q.n s I) (blockOff q.n s K)
      (blockOff q.n s J)) {I' K' J' : ℕ} (hn : Next p I K J I' K' J') :
    Progress q s p I' K' J' O ∧ todo p I' K' J' O < todo p I K J O := by
  have hlt := tripleIdx_lt hI h.ltK h.ltJ
  refine ⟨{ hn with marks := h.marks, done := fun I'' hI'' K'' hK'' J'' hJ'' hbefore => ?_ },
    by unfold todo; rw [hn.idx]; omega⟩
  -- A triple before the next one is a triple before the current one, or the current one.
  rcases Nat.lt_succ_iff_lt_or_eq.1 (hn.idx ▸ hbefore) with hlt' | heq
  · exact h.done I'' hI'' K'' hK'' J'' hJ'' hlt'
  · obtain ⟨rfl, rfl, rfl⟩ := tripleIdx_inj hK'' hJ'' h.ltK h.ltJ heq
    exact hblock

/-- The state between two rounds: the marks stand at out, and below the free pointer no other cell
has changed. -/
def PairsInv (q : PairsInst) (μ : ℕ → ℤ) (fr s p : ℕ) (σ : State) : Prop :=
  ∃ (I K J : ℕ) (O : List ℤ) (oI oK oJ z : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals q fr s p I K J oI oK oJ z), μ'⟩ ∧ KeptBut μ μ' fr q.out (q.n * q.n) ∧
    Seg μ' q.out O ∧ Progress q s p I K J O

/-- What is left to do, read off the state. -/
def pairsVar (q : PairsInst) (p : ℕ) (σ : State) : ℕ :=
  todo p (σ.loc BlockI).toNat (σ.loc BlockK).toNat (σ.loc BlockJ).toNat
    (readSeg σ.mem q.out (q.n * q.n))

private theorem pairsVar_eq {fr : ℕ} {oI oK oJ z : ℤ} {μ' : ℕ → ℤ} (hO : Seg μ' q.out O)
    (h : Progress q s p I K J O) :
    pairsVar q p ⟨frame (locals q fr s p I K J oI oK oJ z), μ'⟩ = todo p I K J O := by
  rw [hO.eq_readSeg, h.marks.len]
  simp [pairsVar]

/-- What the limits have to allow for: the need of the solver behind three matrices and its answer,
two levels further down; room for four blocks; the numbers up to 8n + 2U + 4; three levels of
calls. -/
structure Lim (lim : Limits) (d : ℕ) (r : ℕ → ℕ → Need) (q : PairsInst) (fr s : ℕ) : Prop where
  ok : (r s (2 * q.U + 1)).Ok lim (fr + 3 * (s * s) + 3) (d + 2)
  cells : fr + 4 * (s * s) + 3 ≤ lim.space
  word : 8 * (q.n : ℤ) + 2 * (q.U : ℤ) + 4 ≤ lim.word
  depth : d + 3 ≤ lim.depth

/-! ## A round -/

/-- One round keeps the invariant, and afterwards less is left to do. -/
theorem round_spec (C : Ctx P₀ R p₀ pCbrt pFill pAsk pSub pCopy pMask T r) {q : PairsInst}
    {μ : ℕ → ℤ} {fr s : ℕ} (hpre : q.Pre μ fr) (hlim : Lim lim d r q fr s) (hs : 1 ≤ s ∧ s ≤ q.n)
    {σ : State} (hI : PairsInv q μ fr s (blockCount q.n s) σ)
    (hc : (v BlockI <' v Blocks).Holds σ) :
    Ends lim (P₀ ++ R) d (pairsRound pAsk) σ (roundTime T s q.U) fun σ' =>
      PairsInv q μ fr s (blockCount q.n s) σ' ∧
        pairsVar q (blockCount q.n s) σ' < pairsVar q (blockCount q.n s) σ := by
  obtain ⟨I, K, J, O, z₁, z₂, z₃, z, μ', rfl, hk, hO, hP⟩ := hI
  have hIlt : I < blockCount q.n s := by simpa using hc
  have hpn : blockCount q.n s ≤ q.n := blockCount_le hs.1
  have hw := hlim.ok.space
  have hword := hlim.word
  have hcells := hlim.cells
  have hdepth := hlim.depth
  have hout := hpre.belowOut
  have hlen := hP.marks.len
  have bI := blockOff_add_le hs.2 I
  have bK := blockOff_add_le hs.2 K
  have bJ := blockOff_add_le hs.2 J
  rw [pairsVar_eq hO hP]
  unfold pairsRound roundTime
  -- oI, oK, oJ := the offsets of the three blocks
  refine Ends.next _ (off_spec q.n s I ?_ ⟨(lt_blockCount_iff hs.1 I).1 hIlt, hs.2⟩ (by omega))
  refine Ends.next _ (off_spec q.n s K ?_ ⟨(lt_blockCount_iff hs.1 K).1 hP.ltK, hs.2⟩ (by omega))
  refine Ends.next _ (off_spec q.n s J ?_ ⟨(lt_blockCount_iff hs.1 J).1 hP.ltJ, hs.2⟩ (by omega))
  -- reply := ask(n, s, F, x, y, v, out, oI, oK, oJ, fr)
  refine Ends.callToThen (ask_meets C s (blockOff q.n s I) (blockOff q.n s K) (blockOff q.n s J)
    hpre.keep hO hlen hs.1 ⟨bI, bK, bJ⟩ hlim.ok (by omega)) ?_
  rintro reply μ'' ⟨hkAsk, hpost⟩
  have hO'' : Seg μ'' q.out O := hO.keep
  -- if reply = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- The solver has found an unmarked pair with a witness: it is marked.
    obtain ⟨-, a, ha, b, hb, c, hc, ma, mc, hun, hwit⟩ :=
      hpost.resolve_left fun h => by simp [h.1] at hyes
    obtain ⟨hP', hless⟩ := hP.mark (k := blockOff q.n s K + b) (by omega) hun hwit
    have hidx := Nat.mul_add_lt_mul (show blockOff q.n s I + a < q.n by omega)
      (show blockOff q.n s J + c < q.n by omega)
    have hO' := hO''.update_in (hlen ▸ hidx) 1
    refine (mark_spec ma mc (by omega) hout ⟨hw, by omega⟩).mono (by light_time) ?_
    rintro _ rfl
    exact ⟨⟨I, K, J, _, _, _, _, _, _, rfl, by light_keep, hO', hP'⟩,
      by rw [pairsVar_eq hO' hP']; exact hless⟩
  · -- The triple of blocks is done: the next one comes.
    have hblock := (hpost.resolve_right fun h => hno (by simp [h.1])).2
    refine (advance_spec ⟨hIlt, hP.ltK, hP.ltJ⟩ (by omega)).mono (by light_time) ?_
    rintro _ ⟨I', K', J', rfl, hnext⟩
    obtain ⟨hP', hless⟩ := hP.next hIlt hblock hnext
    exact ⟨⟨I', K', J', O, _, _, _, _, μ'', rfl, by light_keep, hO'', hP'⟩,
      by rw [pairsVar_eq hO'' hP']; exact hless⟩

/-! ## The host -/

/-- countStmt puts p = ⌈n/s⌉ into its local and changes nothing else.  It is stated like off_spec,
for any list l of locals and any Q. -/
theorem count_spec {P : Program} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop} (n s : ℕ)
    (h : Q ⟨frame (setLocal l Blocks (blockCount n s : ℕ)), μ⟩) (hs : 1 ≤ s ∧ s ≤ n)
    (hword : 2 * (n : ℤ) + 1 ≤ lim.word) (hN : frame l N = n := by rfl)
    (hS : frame l Side = s := by rfl) :
    Ends lim P d countStmt ⟨frame l, μ⟩ (10 * blockCount n s + 8) Q := by
  have hpn : blockCount n s ≤ n := blockCount_le hs.1
  rw [← update_frame_setLocal] at h
  generalize frame l = loc at *
  unfold countStmt
  -- p := 0
  refine Ends.setThen ?_
  -- while p * s < n: p := p + 1
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Blocks j, μ⟩) (blockCount n s)
    (by simp) ?round ?done
  case round =>
    rintro j _ hj rfl
    have hjs : j * s < n := (lt_blockCount_iff hs.1 j).1 hj
    exact ⟨by light_norm [N, Side, Blocks, hS, abs_le]; omega,
      by light_norm [N, Side, Blocks, hN, hS]; omega,
      by light_norm [Stmt.BlockSafe, abs_le]; omega, by simp⟩
  case done =>
    rintro _ rfl
    have hlow := le_blockCount_mul (n := n) hs.1
    have hhigh := blockCount_mul_lt (n := n) hs.1
    exact ⟨by light_norm [N, Side, Blocks, hS, abs_le]; omega,
      by light_norm [N, Side, Blocks, hN, hS]; omega, h⟩

/-- The list of marks is the list of flags of the task, when it holds the right flag for every
pair. -/
theorem eq_pairFlags {n : ℕ} {X Y V O : List ℤ} (lO : O.length = n * n)
    (h : ∀ i < n, ∀ j < n, entry n O i j = flag (PairHit n X Y V i j)) :
    O = pairFlags n X Y V := by
  refine List.ext_getElem (by simp [pairFlags, lO]) fun t ht _ => ?_
  obtain ⟨i, hi, j, hj, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (lO ▸ ht)
  rw [← List.getD_eq_getElem _ 0 ht, ← entry, h i hi j hj]
  simp only [pairFlags, List.getElem_map, List.getElem_range, PairHit, Witness,
    Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]

/-- **When no triple of blocks is left, the marks are the answer.** -/
theorem Progress.complete (h : Progress q s (blockCount q.n s) (blockCount q.n s) K J O)
    (hs : 1 ≤ s ∧ s ≤ q.n) : O = pairFlags q.n q.X q.Y q.V := by
  obtain ⟨rfl, rfl⟩ := h.top rfl
  exact eq_pairFlags h.marks.len fun i hi j hj => h.marks.complete hs.1 hs.2
    (fun I' hI' K' hK' J' hJ' =>
      h.done I' hI' K' hK' J' hJ' (tripleIdx_top _ ▸ tripleIdx_lt hI' hK' hJ'))
    hi hj

/-- At the beginning all p³ triples of blocks and all pairs are left. -/
private theorem todo_start (p m : ℕ) : todo p 0 0 0 (List.replicate m 0) = p * p * p + m := by
  simp [todo, tripleIdx]

/-- At the beginning no pair is marked, and no triple of blocks has been visited. -/
theorem progress_start (q : PairsInst) (s : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    Progress q s p 0 0 0 (List.replicate (q.n * q.n) 0) :=
  { leI := by omega
    ltK := hp
    ltJ := hp
    top := fun _ => ⟨rfl, rfl⟩
    marks := marks_replicate ..
    done := fun I' _ K' _ J' _ hbefore => absurd hbefore (by simp [tripleIdx]) }

/-- What allPairs needs covers what the rounds need. -/
private theorem lim_of_ok {fr : ℕ} (hok : (pairsNeed r q.n q.U).Ok lim fr d) :
    Lim lim d r q fr (cbrtLeast q.n) := by
  have hword := hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [pairsNeed] at hword hcells hdepth
  exact
    { ok := by refine hok.mono ?_ ?_ ?_ <;> simp only [pairsNeed] <;> omega
      cells := by omega
      word := by omega
      depth := by omega }

/-- A round, with the test of the loop (4 steps). -/
private theorem roundTime_le (T : ℕ → ℕ → ℕ) (s U : ℕ) :
    roundTime T s U + 4 ≤ 220 * s ^ 2 + 250 + T s (2 * U + 1) := by
  have hs : s ≤ s ^ 2 := Nat.le_self_pow (by norm_num) s
  have hcopy : s * (16 * s + 31) = 16 * s ^ 2 + 31 * s := by ring
  unfold roundTime askTime subCopyTime maskTime
  rw [hcopy, ← pow_two]
  omega

/-- The steps of allPairs add up to at most pairsTime: cbrtCeil takes 12 s steps, countStmt 10 p,
fill 13 n², the other statements before the rounds 56 in all, and there are at most p³ + n² rounds,
each with the test of the loop. -/
private theorem time_le (T : ℕ → ℕ → ℕ) {n s p : ℕ} (U : ℕ) (hsn : s ≤ n) (hpn : p ≤ n) :
    12 * s + 10 * p + 13 * (n * n) + 56 + ((p * p * p + n * n) * (roundTime T s U + 4) + 4) ≤
      40 * n ^ 2 + 80 + (p ^ 3 + n ^ 2) * (220 * s ^ 2 + 250 + T s (2 * U + 1)) := by
  have hn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have hrounds := Nat.mul_le_mul_left (p ^ 3 + n ^ 2) (roundTime_le T s U)
  rw [show p * p * p = p ^ 3 by ring, ← pow_two]
  omega

/-- **allPairs** solves the task. -/
theorem pairs_spec (C : Ctx P₀ R p₀ pCbrt pFill pAsk pSub pCopy pMask T r) {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : q.Pre μ fr) (hok : (pairsNeed r q.n q.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (pairsBody pCbrt pFill pAsk) ⟨frame (pairsTask.args q ++ [(fr : ℤ)]), μ⟩
      (pairsTime T q.n q.U) fun σ' => pairsTask.Post q μ fr (σ'.loc 0) σ'.mem := by
  have hlim := lim_of_ok hok
  have hs : 1 ≤ cbrtLeast q.n ∧ cbrtLeast q.n ≤ q.n :=
      ⟨one_le_cbrtLeast hpre.n_pos, cbrtLeast_le_self q.n⟩
  refine Ends.mono ?_ (time_le T q.U hs.2 (blockCount_le hs.1)) fun _ h => h
  have hw := hlim.ok.space
  have hword := hlim.word
  have hcells := hlim.cells
  have hdepth := hlim.depth
  have hout := hpre.belowOut
  have hP := progress_start q (cbrtLeast q.n) (blockCount_pos hs.1 hpre.n_pos)
  change Ends _ _ _ _ ⟨frame [(q.n : ℤ), q.U, q.x, q.y, q.v, q.out, fr], μ⟩ _ _
  unfold pairsBody
  -- s := cbrtCeil(n)
  refine Ends.callToThen (cbrtCeil_meets (n := q.n) C.cbrt μ (by push_cast; omega)) ?_
  rintro _ μ₀ ⟨rfl, hμ⟩
  obtain rfl : μ = μ₀ := hμ.symm
  unfold cbrtCeilTime
  generalize cbrtLeast q.n = s at *
  -- p := ⌈n/s⌉
  refine Ends.next _ (count_spec q.n s ?_ hs (by omega))
  -- large := 2U + 1; answer := fr + 3 s²
  refine Ends.setToThen (2 * (q.U : ℤ) + 1) ?_
  refine Ends.setToThen (fr + 3 * (s * s) : ℕ) ?_
  -- fill(out, n², 0): no pair is marked
  refine Ends.callToThen (fill_meets C.fill (dst := q.out) (n := q.n * q.n) (x := 0) hw (by omega))
    ?_
  rintro z μ₁ ⟨hO, hrest⟩
  -- I := 0; K := 0; J := 0
  refine Ends.setToThen (0 : ℕ) ?_
  refine Ends.setToThen (0 : ℕ) ?_
  refine Ends.setToThen (0 : ℕ) ?_
  -- The rounds.
  refine Ends.whileVariant (PairsInv q μ fr s (blockCount q.n s)) (pairsVar q (blockCount q.n s))
    (roundTime T s q.U)
    ⟨0, 0, 0, _, 0, 0, 0, z, μ₁, rfl, by light_keep, hO, hP⟩
    (fun _ _ => ⟨trivial, trivial⟩) (fun σ hI hc => round_spec C hpre hlim hs hI hc) ?done ?time
  case done =>
    rintro _ ⟨I, K, J, O, _, _, _, _, μ', rfl, hk, hO', hP'⟩ hc
    obtain rfl : I = blockCount q.n s := by have := hP'.leI; simp at hc; omega
    exact ⟨hP'.complete hs ▸ hO', hk⟩
  case time =>
    change pairsVar q _ ⟨frame (locals q fr s (blockCount q.n s) 0 0 0 0 0 0 z), μ₁⟩ * _ + _ ≤ _
    rw [pairsVar_eq hO hP, todo_start]
    light_time

/-! ## The need -/

/-- The need of allPairs is polynomially bounded if the need of the solver is. -/
theorem polyNeed_pairs (hr : PolyNeed r) : PolyNeed (pairsNeed r) := by
  unfold pairsNeed
  poly_need [hr.word, hr.cells, hr.depth, Scale.SoftO.of_forall_le cbrtLeast_le_self]

end Pairs

open Pairs

/-- **The middle step of [VW18, Theorem 4.2]: all pairs with a witness, from finding a negative
triangle.** -/
theorem isHost_pairs : IsHost findTask pairsTask pairsTime pairsNeed := by
  refine ⟨fun P p T r hsol => ⟨pairsProcs P.length p, P.length + 6, ?_⟩,
    fun r hr => polyNeed_pairs hr⟩
  refine ⟨pairsBody (P.length + 3) (P.length + 1) (P.length + 5), by simp [pairsProcs],
    fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact pairs_spec (pSub := P.length + 2) (pCopy := P.length) (pMask := P.length + 4)
    { sol := hsol
      sub := by simp [pairsProcs]
      copy := by simp [pairsProcs]
      mask := by simp [pairsProcs]
      cbrt := by simp [pairsProcs]
      fill := by simp [pairsProcs]
      ask := by simp [pairsProcs] } hpre hok

end Light.Sec3
