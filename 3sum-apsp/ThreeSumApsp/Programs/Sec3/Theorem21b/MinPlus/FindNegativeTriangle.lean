/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.CopyBlock
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem21b.FindNegativeTriangle

/-!
# Finding a negative triangle with an algorithm that decides whether there is one

[VW18, Lemma 4.1], a step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
The host asks the solver of Negative Triangle about the whole instance.  If the answer is yes, it
keeps three offsets and a side length h such that the h × h × h sub-instance at these offsets has a
negative triangle.  While h > 1 it puts h' = ⌈h/2⌉, asks about the eight sub-instances of side h'
made of the lower half [o, o + h') or the upper half [o + h - h', o + h) of each of the three
ranges, and goes on with one for which the answer is yes.  All eight questions are asked, and the
last yes counts.

The result is isHost_find : IsHost ntTask findTask findTime findNeed.  The proof goes from the
inside to the outside: one question (probe_meets: three calls of subCopy, one of the solver); the
questions of a round (try_spec and tries_spec, with the invariant TryInv); a round (round_spec; that
one of the eight answers is yes is NegAt.split); the rounds (loop_spec, with the invariant LoopInv);
the search and the host (search_spec, find_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedures -/

namespace Probe

/-- The local variables of probe: the arguments n, U, ab, bc, ac, the offsets a0, b0, c0, the side
h and fr (Free); then h² (Area), and the results of subCopy, which are not used. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev AB : ℕ := 2
@[inherit_doc N] abbrev BC : ℕ := 3
@[inherit_doc N] abbrev AC : ℕ := 4
@[inherit_doc N] abbrev OffA : ℕ := 5
@[inherit_doc N] abbrev OffB : ℕ := 6
@[inherit_doc N] abbrev OffC : ℕ := 7
@[inherit_doc N] abbrev Side : ℕ := 8
@[inherit_doc N] abbrev Free : ℕ := 9
@[inherit_doc N] abbrev Area : ℕ := 10
@[inherit_doc N] abbrev Unused : ℕ := 11

end Probe

open Probe in
/-- probe(n, U, ab, bc, ac, a0, b0, c0, h, fr): copies the three h × h blocks of the sub-instance at
the offsets a0, b0, c0 to fr, fr + h², fr + 2h², and asks the solver of Negative Triangle about
them, with the free pointer fr + 3h².  The answer goes to local 0 and so is the result. -/
def probeBody (pNT pSub : ℕ) : Stmt :=
  .set Area (v Side *' v Side) ;;
  .call pSub [v N, v Side, v AB, v OffA, v OffB, v Free] Unused ;;
  .call pSub [v N, v Side, v BC, v OffB, v OffC, v Free +' v Area] Unused ;;
  .call pSub [v N, v Side, v AC, v OffA, v OffC, v Free +' v Area +' v Area] Unused ;;
  .call pNT [v Side, v U, v Free, v Free +' v Area, v Free +' v Area +' v Area,
    v Free +' v Area +' v Area +' v Area] 0

namespace Find

/-- The local variables of find: the arguments n, U, ab, bc, ac, res (Answer), fr (Free); the
offsets a0, b0, c0 and the side length h of the current sub-instance; the next side length h' (Half)
and δ = h - h' (Shift); the offsets na, nb, nc of the last sub-instance with the answer yes; the
last answer of probe or of the solver (Reply). -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev AB : ℕ := 2
@[inherit_doc N] abbrev BC : ℕ := 3
@[inherit_doc N] abbrev AC : ℕ := 4
@[inherit_doc N] abbrev Answer : ℕ := 5
@[inherit_doc N] abbrev Free : ℕ := 6
@[inherit_doc N] abbrev OffA : ℕ := 7
@[inherit_doc N] abbrev OffB : ℕ := 8
@[inherit_doc N] abbrev OffC : ℕ := 9
@[inherit_doc N] abbrev Side : ℕ := 10
@[inherit_doc N] abbrev Half : ℕ := 11
@[inherit_doc N] abbrev Shift : ℕ := 12
@[inherit_doc N] abbrev NewA : ℕ := 13
@[inherit_doc N] abbrev NewB : ℕ := 14
@[inherit_doc N] abbrev NewC : ℕ := 15
@[inherit_doc N] abbrev Reply : ℕ := 16

end Find

open Find in
/-- One question of a round of find: about the sub-instance of side h' whose offsets are those of
the round, moved by δ where the triple t has a 1.  If the answer is yes, the offsets are noted in
na, nb, nc. -/
def tryStmt (pProbe : ℕ) (t : ℕ × ℕ × ℕ) : Stmt :=
  .call pProbe [v N, v U, v AB, v BC, v AC, v OffA +' k t.1 *' v Shift,
    v OffB +' k t.2.1 *' v Shift, v OffC +' k t.2.2 *' v Shift, v Half, v Free] Reply ;;
  .ite (v Reply =' k 1)
    (.set NewA (v OffA +' k t.1 *' v Shift) ;; .set NewB (v OffB +' k t.2.1 *' v Shift) ;;
      .set NewC (v OffC +' k t.2.2 *' v Shift))
    .skip

/-- The questions for a list of triples, one after the other. -/
def triesStmt (pProbe : ℕ) : List (ℕ × ℕ × ℕ) → Stmt
  | [] => .skip
  | t :: ts => tryStmt pProbe t ;; triesStmt pProbe ts

open Find in
/-- h' := ⌈h/2⌉, by counting up. -/
def halfStmt : Stmt :=
  .set Half (k 0) ;;
  .while (v Half +' v Half <' v Side) (.set Half (v Half +' k 1))

open Find in
/-- One round of find: h' = ⌈h/2⌉, δ = h - h', the eight questions, the new offsets and the new
side length. -/
def roundStmt (pProbe : ℕ) : Stmt :=
  halfStmt ;;
  .set Shift (v Side -' v Half) ;;
  .set NewA (v OffA) ;; .set NewB (v OffB) ;; .set NewC (v OffC) ;;
  triesStmt pProbe octants ;;
  .set OffA (v NewA) ;; .set OffB (v NewB) ;; .set OffC (v NewC) ;; .set Side (v Half)

open Find in
/-- The search of find, once it is known that there is a negative triangle: rounds until the side
length is 1; then the offsets are the triangle, and the result is 1. -/
def searchStmt (pProbe : ℕ) : Stmt :=
  .set OffA (k 0) ;; .set OffB (k 0) ;; .set OffC (k 0) ;; .set Side (v N) ;;
  .while (k 1 <' v Side) (roundStmt pProbe) ;;
  .store (v Answer) (v OffA) ;;
  .store (v Answer +' k 1) (v OffB) ;;
  .store (v Answer +' k 2) (v OffC) ;;
  .set 0 (k 1)

open Find in
/-- find(n, U, ab, bc, ac, res, fr): asks about the whole instance; the result is 0 if the answer is
no, and else the search begins. -/
def findBody (pNT pProbe : ℕ) : Stmt :=
  .call pNT [v N, v U, v AB, v BC, v AC, v Free] Reply ;;
  .ite (v Reply =' k 0) (.set 0 (k 0)) (searchStmt pProbe)

/-! ## Time and need -/

/-- The number of steps of probe, if the solver takes T. -/
def probeTime (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ := 3 * subCopyTime h + T h U + 54

/-- The number of steps of one question of a round, with the test of the answer. -/
def tryTime (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ := probeTime T h U + 46

/-- A bound on the number of steps of the round that goes to the side length h: eight questions,
each with the copying of three blocks. -/
def roundBound (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ := 8 * (T h U + 150 * h ^ 2 + 130)

/-- **The number of steps of find**, if the solver of Negative Triangle takes T: one question at
size n, and one round for each side length of the chain ⌈n/2⌉, ⌈⌈n/2⌉/2⌉, …, 1. -/
def findTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  40 + T n U + ((halvingChain n).map fun h => roundBound T h U).sum

/-- **What find needs**, if the solver needs r: room for three blocks, three more levels of calls,
and what the solver needs at any size up to n. -/
def findNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := n + 2 + (Finset.range (n + 1)).sup fun h => (r h U).word
  cells := (Finset.range (n + 1)).sup fun h => 3 * (h * h) + (r h U).cells
  depth := 3 + (Finset.range (n + 1)).sup fun h => (r h U).depth

/-- The procedures that the host appends to the program of a solver whose program has o procedures
and whose procedure number is p: copy, subCopy, probe, find, with the numbers o, o + 1, o + 2,
o + 3. -/
def findProcs (o p : ℕ) : Program :=
  [copyBody, subCopyBody o, probeBody p (o + 1), findBody p (o + 2)]

namespace Find

variable {P₀ R : Program} {p pProbe pSub pCopy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}

/-! ## The surroundings -/

/-- The surroundings of find: a solver of Negative Triangle, and the procedures probe, subCopy, copy
in the program. -/
structure Ctx (P₀ R : Program) (p pProbe pSub pCopy : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) :
    Prop where
  sol : Solves ntTask P₀ p T r
  probe : (P₀ ++ R)[pProbe]? = some (probeBody p pSub)
  sub : (P₀ ++ R)[pSub]? = some (subCopyBody pCopy)
  copy : (P₀ ++ R)[pCopy]? = some copyBody

/-- What find needs covers what the solver needs at a size h ≤ n, behind three blocks and up to
three levels further down. -/
theorem ok_sub {n U fr h : ℕ} (hok : (findNeed r n U).Ok lim fr d) (hh : h ≤ n) {fr' d' : ℕ}
    (hfr : fr' ≤ fr + 3 * (h * h)) (hd : d' ≤ d + 3) : (r h U).Ok lim fr' d' := by
  have hm : h ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hword := Finset.le_sup (f := fun h => (r h U).word) hm
  have hcells := Finset.le_sup (f := fun h => 3 * (h * h) + (r h U).cells) hm
  have hdepth := Finset.le_sup (f := fun h => (r h U).depth) hm
  refine hok.mono ?_ ?_ ?_ <;> simp only [findNeed] <;> omega

/-- What find needs covers the numbers up to n + 2 and three levels of calls. -/
private theorem word_depth_of_ok {n U fr : ℕ} (hok : (findNeed r n U).Ok lim fr d) :
    (n : ℤ) + 2 ≤ lim.word ∧ d + 3 ≤ lim.depth := by
  have hword := hok.word
  have hdepth := hok.depth
  simp only [findNeed] at hword hdepth
  omega

/-! ## One question -/

/-- The sub-instance of side h at the offsets a0, b0, c0, with its three blocks at fr, fr + h² and
fr + 2h². -/
def subInst (x : TriInst) (fr a0 b0 c0 h : ℕ) : TriInst :=
  ⟨h, x.U, fr, fr + h * h, fr + 2 * (h * h), subMat x.n h a0 b0 x.AB, subMat x.n h b0 c0 x.BC,
    subMat x.n h a0 c0 x.AC⟩

/-- The sub-instance is an instance, once its three blocks stand at their places. -/
theorem subInst_pre {x : TriInst} {μ μ' : ℕ → ℤ} {fr a0 b0 c0 h : ℕ} (hpre : x.Pre μ fr)
    (hh : 1 ≤ h) (sAB : Seg μ' fr (subMat x.n h a0 b0 x.AB))
    (sBC : Seg μ' (fr + h * h) (subMat x.n h b0 c0 x.BC))
    (sAC : Seg μ' (fr + h * h + h * h) (subMat x.n h a0 c0 x.AC)) :
    (subInst x fr a0 b0 c0 h).Pre μ' (fr + 3 * (h * h)) :=
  have hU : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  triPre_of_arrays hh hpre.U_pos
    { len := length_subMat .., seg := sAB, bound := abs_le_of_mem_subMat hU hpre.leAB }
    { len := length_subMat .., seg := sBC, bound := abs_le_of_mem_subMat hU hpre.leBC }
    { len := length_subMat .., bound := abs_le_of_mem_subMat hU hpre.leAC
      seg := (show fr + 2 * (h * h) = fr + h * h + h * h by omega) ▸ sAC }

/-- **probe** returns 1 if the sub-instance of side h at the offsets a0, b0, c0 has a negative
triangle, and 0 if not, and changes no cell below the free pointer. -/
theorem probe_meets (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}
    (a0 b0 c0 h : ℕ) (hpre : x.Pre μ fr) (hh : 1 ≤ h)
    (hin : a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n)
    (hok : (r h x.U).Ok lim (fr + 3 * (h * h)) (d + 1)) (hd : d + 1 < lim.depth) :
    Meets lim (P₀ ++ R) pProbe d [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, a0, b0, c0, h, fr] μ
      (probeTime T h x.U) fun res μ' =>
        res = flag (NegAt x.n x.AB x.BC x.AC a0 b0 c0 h) ∧ Kept μ μ' fr := by
  have hw := hok.space
  have hcells := hok.cells
  light_facts hpre
  refine .of_body C.probe ?_
  unfold probeBody probeTime
  -- area := h * h
  light_set (h * h : ℕ)
  -- subCopy(n, h, ab, a0, b0, fr)
  light_call (subCopy_meets C.sub C.copy h a0 b0 fr hpre.segAB hpre.lenAB (by omega)
    (by omega)) with _ μ₁ ⟨sAB, same₁⟩
  -- subCopy(n, h, bc, b0, c0, fr + area)
  light_call (subCopy_meets C.sub C.copy h b0 c0 (fr + h * h) hpre.segBC.keep hpre.lenBC
    (by omega) (by omega)) with _ μ₂ ⟨sBC, same₂⟩
  -- subCopy(n, h, ac, a0, c0, fr + area + area)
  light_call (subCopy_meets C.sub C.copy h a0 c0 (fr + h * h + h * h) hpre.segAC.keep
    hpre.lenAC (by omega) (by omega)) with _ μ₃ ⟨sAC, same₃⟩
  -- The solver is asked about the three blocks.
  refine Ends.callTo (T' := T h x.U) (C.sol.meets R (subInst x fr a0 b0 c0 h) (fr + 3 * (h * h))
    (subInst_pre hpre hh sAB.keep sBC.keep sAC) hok) ?_ (by light_side [ntTask, subInst])
  rintro _ μ₄ ⟨rfl, same₄⟩
  exact ⟨flag_congr (hasNegativeTriangle_subMat_iff ..), by light_keep⟩

/-! ## The questions of a round -/

/-- The state during the questions of a round: na, nb, nc are offsets of a sub-instance of side h',
and if Done holds (one of the questions asked so far had the answer yes), that sub-instance has a
negative triangle.  No cell below the free pointer has changed. -/
def TryInv (x : FindInst) (μ : ℕ → ℤ) (fr a0 b0 c0 h h' : ℕ) (Done : Prop) (σ : State) : Prop :=
  ∃ (na nb nc : ℕ) (reply : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, a0, b0, c0, h, h', (h - h' : ℕ), na, nb, nc,
      reply], μ'⟩ ∧
    Kept μ μ' fr ∧ (na + h' ≤ x.n ∧ nb + h' ≤ x.n ∧ nc + h' ≤ x.n) ∧
    (Done → NegAt x.n x.AB x.BC x.AC na nb nc h')

private theorem TryInv.imp {x : FindInst} {μ : ℕ → ℤ} {fr a0 b0 c0 h h' : ℕ} {Done Done' : Prop}
    {σ : State} (H : TryInv x μ fr a0 b0 c0 h h' Done σ) (hD : Done' → Done) :
    TryInv x μ fr a0 b0 c0 h h' Done' σ := by
  obtain ⟨na, nb, nc, reply, μ', hσ, hk, hin, hneg⟩ := H
  exact ⟨na, nb, nc, reply, μ', hσ, hk, hin, fun hd => hneg (hD hd)⟩

/-- The sub-instance that the triple t stands for has a negative triangle. -/
def NegOct (x : FindInst) (a0 b0 c0 h h' : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  NegAt x.n x.AB x.BC x.AC (a0 + t.1 * (h - h')) (b0 + t.2.1 * (h - h')) (c0 + t.2.2 * (h - h')) h'

/-- **One question** keeps the invariant, and notes the offsets of its sub-instance if the answer is
yes. -/
theorem try_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ}
    {fr a0 b0 c0 h h' : ℕ} (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d)
    (hh : 1 ≤ h' ∧ h' ≤ h) (hin : a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n) {t : ℕ × ℕ × ℕ}
    (ht : t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 ≤ 1) {Done : Prop} {σ : State}
    (hI : TryInv x μ fr a0 b0 c0 h h' Done σ) :
    Ends lim (P₀ ++ R) d (tryStmt pProbe t) σ (tryTime T h' x.U)
      (TryInv x μ fr a0 b0 c0 h h' (Done ∨ NegOct x a0 b0 c0 h h' t)) := by
  obtain ⟨na, nb, nc, reply, μ', rfl, hk, hcand, hneg⟩ := hI
  obtain ⟨t₁, t₂, t₃⟩ := t
  obtain ⟨hword, hdepth⟩ := word_depth_of_ok hok
  -- Each offset moves by 0 or by δ = h - h'.
  obtain ⟨ht₁, ht₂, ht₃⟩ : t₁ ≤ 1 ∧ t₂ ≤ 1 ∧ t₃ ≤ 1 := ht
  have hδ₁ : t₁ * (h - h') ≤ h - h' := by simpa using Nat.mul_le_mul_right (h - h') ht₁
  have hδ₂ : t₂ * (h - h') ≤ h - h' := by simpa using Nat.mul_le_mul_right (h - h') ht₂
  have hδ₃ : t₃ * (h - h') ≤ h - h' := by simpa using Nat.mul_le_mul_right (h - h') ht₃
  unfold tryStmt tryTime
  -- reply := probe(n, U, ab, bc, ac, a0 + t₁ δ, b0 + t₂ δ, c0 + t₃ δ, h', fr)
  light_call (probe_meets C (a0 + t₁ * (h - h')) (b0 + t₂ * (h - h'))
    (c0 + t₃ * (h - h')) h' hpre.toPre.keep hh.1 (by omega)
    (ok_sub hok (by omega) le_rfl (by omega)) (by omega)) with _ μ'' ⟨rfl, hk'⟩
  -- if reply = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- na := a0 + t₁ δ; nb := b0 + t₂ δ; nc := c0 + t₃ δ
    refine Ends.setToThen (a0 + t₁ * (h - h') : ℕ) ?_
    refine Ends.setToThen (b0 + t₂ * (h - h') : ℕ) ?_
    refine Ends.setTo (c0 + t₃ * (h - h') : ℕ) ?_
    exact ⟨_, _, _, _, μ'', rfl, hk.trans hk', by omega,
      fun _ => flag_eq_one_iff.1 (by simpa using hyes)⟩
  · refine Ends.skip ⟨na, nb, nc, _, μ'', rfl, hk.trans hk', hcand, ?_⟩
    rintro (hD | hD)
    · exact hneg hD
    · exact absurd (by simpa [NegOct] using flag_of hD) hno

/-- The questions for a list of triples keep the invariant: afterwards na, nb, nc are the offsets of
a sub-instance with a negative triangle, if one of the triples stands for such a sub-instance. -/
theorem tries_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ}
    {fr a0 b0 c0 h h' : ℕ} (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d)
    (hh : 1 ≤ h' ∧ h' ≤ h) (hin : a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n)
    (ts : List (ℕ × ℕ × ℕ)) (hts : ∀ t ∈ ts, t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 ≤ 1) {Done : Prop}
    {σ : State} (hI : TryInv x μ fr a0 b0 c0 h h' Done σ) :
    Ends lim (P₀ ++ R) d (triesStmt pProbe ts) σ (ts.length * tryTime T h' x.U)
      (TryInv x μ fr a0 b0 c0 h h' (Done ∨ ∃ t ∈ ts, NegOct x a0 b0 c0 h h' t)) := by
  induction ts generalizing Done σ with
  | nil => exact Ends.skip (hI.imp (by simp))
  | cons t ts ih =>
    refine Ends.seq (tryTime T h' x.U) (ts.length * tryTime T h' x.U) ?_
      (by simp only [List.length_cons]; ring_nf; omega)
    refine (try_spec C hpre hok hh hin (hts t (by simp)) hI).mono le_rfl fun σ' hσ' => ?_
    refine (ih (fun t' ht' => hts t' (by simp [ht'])) hσ').mono le_rfl fun σ'' hσ'' => hσ''.imp ?_
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-! ## A round, and the search -/

/-- The state between two rounds: the sub-instance of side h at the offsets a0, b0, c0 has a
negative triangle, and no cell below the free pointer has changed.  The six locals that a round uses
hold anything. -/
def LoopInv (x : FindInst) (μ : ℕ → ℤ) (fr h : ℕ) (σ : State) : Prop :=
  ∃ (a0 b0 c0 : ℕ) (z₁ z₂ z₃ z₄ z₅ z₆ : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, a0, b0, c0, h, z₁, z₂, z₃, z₄, z₅, z₆],
      μ'⟩ ∧
    Kept μ μ' fr ∧ (a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n) ∧
    NegAt x.n x.AB x.BC x.AC a0 b0 c0 h

private theorem LoopInv.loc_side {x : FindInst} {μ : ℕ → ℤ} {fr h : ℕ} {σ : State}
    (hI : LoopInv x μ fr h σ) : σ.loc Side = h := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl, -⟩ := hI
  rfl

/-- halfStmt puts ⌈h/2⌉ into h' and changes nothing else. -/
theorem half_spec {P : Program} {loc μ : ℕ → ℤ} {h : ℕ} (hside : loc Side = h)
    (hword : (h : ℤ) + 2 ≤ lim.word) :
    Ends lim P d halfStmt ⟨loc, μ⟩ (10 * ((h + 1) / 2) + 8) fun σ' =>
      σ' = ⟨Function.update loc Half ((h + 1) / 2 : ℕ), μ⟩ := by
  unfold halfStmt
  -- h' := 0
  refine Ends.setThen ?_
  -- while h' + h' < h: h' := h' + 1
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Half j, μ⟩) ((h + 1) / 2) (by simp)
    ?round ?done
  case round =>
    rintro j _ hj rfl
    exact ⟨by light_norm [Side, Half, hside, abs_le]; omega,
      by light_norm [Side, Half, hside]; omega, by light_norm [Stmt.BlockSafe, abs_le]; omega,
      by simp⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_norm [Side, Half, hside, abs_le]; omega,
      by light_norm [Side, Half, hside]; omega, rfl⟩

/-- The number of steps of the round that goes to the side length h'. -/
def roundTime (T : ℕ → ℕ → ℕ) (h' U : ℕ) : ℕ := 8 * tryTime T h' U + 10 * h' + 26

private theorem roundTime_le (T : ℕ → ℕ → ℕ) (h' U : ℕ) :
    roundTime T h' U + 4 ≤ roundBound T h' U := by
  have hsq : h' ≤ h' ^ 2 := Nat.le_self_pow (by norm_num) h'
  have hcopy : h' * (16 * h' + 31) = 16 * h' ^ 2 + 31 * h' := by ring
  unfold roundTime roundBound tryTime probeTime subCopyTime
  rw [hcopy]
  omega

/-- **One round** goes from a sub-instance of side h ≥ 2 with a negative triangle to one of side
⌈h/2⌉. -/
theorem round_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ} {fr h : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) (hh : 2 ≤ h) {σ : State}
    (hI : LoopInv x μ fr h σ) :
    Ends lim (P₀ ++ R) d (roundStmt pProbe) σ (roundTime T ((h + 1) / 2) x.U)
      (LoopInv x μ fr ((h + 1) / 2)) := by
  obtain ⟨a0, b0, c0, z₁, z₂, z₃, z₄, z₅, z₆, μ', rfl, hk, hin, hneg⟩ := hI
  obtain ⟨hword, -⟩ := word_depth_of_ok hok
  unfold roundStmt roundTime
  -- h' := ⌈h/2⌉
  light_piece (half_spec (h := h) rfl (by omega)) with _ rfl
  rw [update_frame_setLocal]
  generalize hh' : (h + 1) / 2 = h'
  -- δ := h - h'
  light_set (h - h' : ℕ)
  -- na := a0; nb := b0; nc := c0
  light_set a0
  light_set b0
  light_set c0
  -- The eight questions: one of them has the answer yes.
  refine Ends.next (8 * tryTime T h' x.U) ((tries_spec C hpre hok (h := h) (h' := h')
    ⟨by omega, by omega⟩ hin octants (fun _ => le_one_of_mem_octants) (Done := False)
    ⟨a0, b0, c0, z₆, μ', rfl, hk, by omega, False.elim⟩).mono (by simp [octants]) ?_)
  rintro _ ⟨na, nb, nc, reply, μ'', rfl, hk', hcand, hneg'⟩
  -- a0 := na; b0 := nb; c0 := nc; h := h'
  light_set na
  light_set nb
  light_set nc
  light_set h'
  exact ⟨na, nb, nc, _, _, _, _, _, _, μ'', rfl, hk', hcand,
    hneg' (.inr (hneg.split (by omega) (by omega)))⟩

/-- The number of steps of the search from the side length h on. -/
def loopTime (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ :=
  ((halvingChain h).map fun h' => roundBound T h' U).sum + 4

/-- The rounds end with a sub-instance of side 1 that has a negative triangle. -/
theorem loop_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) :
    ∀ (h : ℕ) (σ : State), 1 ≤ h → LoopInv x μ fr h σ →
      Ends lim (P₀ ++ R) d (.while (k 1 <' v Side) (roundStmt pProbe)) σ (loopTime T h x.U)
        (LoopInv x μ fr 1) := by
  obtain ⟨hword, -⟩ := word_depth_of_ok hok
  have one : ((1 : ℕ) : ℤ) ≤ lim.word := by push_cast; omega
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro σ h1 hI
    by_cases hh : 2 ≤ h
    · -- One round, and then the rounds from ⌈h/2⌉ on.
      refine Ends.whileStep (roundTime T ((h + 1) / 2) x.U) (loopTime T ((h + 1) / 2) x.U)
        ⟨one, trivial⟩ (by light_norm [hI.loc_side]; omega)
        ((round_spec C hpre hok hh hI).mono le_rfl fun σ' hσ' => ih _ (by omega) σ' (by omega) hσ')
        ?_
      have := roundTime_le T ((h + 1) / 2) x.U
      simp only [loopTime, halvingChain_of_le hh, List.map_cons, List.sum_cons, Cond.cost,
        Expr.cost]
      omega
    · obtain rfl : h = 1 := by omega
      exact Ends.whileDone ⟨one, trivial⟩ (by light_norm [hI.loc_side]; omega) hI
        (by simp [loopTime])

/-! ## The host -/

/-- **The search** finds a negative triangle if there is one. -/
theorem search_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ μ' : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) (hk : Kept μ μ' fr)
    (hyes : (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle) (reply : ℤ) :
    Ends lim (P₀ ++ R) d (searchStmt pProbe)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, 0, 0, 0, 0, 0, 0, 0, 0, 0, reply], μ'⟩
      (loopTime T x.n x.U + 23) fun σ' => findTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨hword, -⟩ := word_depth_of_ok hok
  have hcells := hok.cells
  light_facts hok hpre
  unfold searchStmt
  -- a0 := 0; b0 := 0; c0 := 0; h := n
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set x.n
  -- The rounds.
  light_piece (loop_spec C hpre hok x.n _ hpre.n_pos
    ⟨0, 0, 0, _, _, _, _, _, _, μ', rfl, hk, by omega,
      (hasNegativeTriangle_iff_negAt ..).1 hyes⟩)
    with _ ⟨a0, b0, c0, z₁, z₂, z₃, z₄, z₅, z₆, μ'', rfl, hk', hin, hneg⟩
  -- res[0] := a0; res[1] := b0; res[2] := c0; the result is 1
  light_store x.res a0
  light_store (x.res + 1) b0
  light_store (x.res + 2) c0
  light_set 1
  refine ⟨(flag_of hyes).symm, fun _ => ⟨⟨a0, by omega⟩, ⟨b0, by omega⟩, ⟨c0, by omega⟩, ?_, ?_, ?_,
    hneg.triangle ..⟩, by light_keep⟩
  · simp
  · simp
  · simp

/-- **find** returns 1 and writes a negative triangle to the cells from `res` if there is one, and
returns 0 if there is none (`findTask`), within `findTime` steps. -/
theorem find_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (findBody p pProbe) ⟨frame (findTask.args x ++ [(fr : ℤ)]), μ⟩
      (findTime T x.n x.U) fun σ' => findTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨hword, hdepth⟩ := word_depth_of_ok hok
  change Ends _ _ _ _ ⟨frame [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.res, fr], μ⟩ _ _
  unfold findBody findTime
  -- reply := solver(n, U, ab, bc, ac, fr)
  refine Ends.callToThen (T' := T x.n x.U) (C.sol.meets R x.toTriInst fr hpre.toPre
    (ok_sub hok le_rfl (by omega) (by omega))) ?_ (by simp [ntTask])
  rintro _ μ₀ ⟨rfl, hk⟩
  -- if reply = 0
  refine Ends.iteLast (fun hno => ?_) (fun hyes => ?_)
  · -- There is no negative triangle: the result is 0.
    refine Ends.setTo 0 ⟨?_, fun h01 => absurd h01 (by norm_num), by light_keep⟩
    simpa using hno.symm
  · -- There is one: the search finds it.
    refine (search_spec C hpre hok hk (by_contra fun hcon => hyes ?_) _).mono ?_ fun _ h => h
    · simpa using flag_of_not hcon
    · simp only [loopTime]
      light_time

/-! ## The need -/

/-- The need of find is polynomially bounded if the need of the solver is. -/
theorem polyNeed_find (hr : PolyNeed r) : PolyNeed (findNeed r) := by
  obtain ⟨s, e, hse⟩ := hr
  have hpoly := PolyBounded.polyBound PolyBounded.fst PolyBounded.snd s e
  have hle : ∀ {n h : ℕ}, h ∈ Finset.range (n + 1) → h ≤ n := fun hh =>
    Nat.le_of_lt_succ (Finset.mem_range.1 hh)
  refine PolyBounded.polyNeed ?_ ?_ ?_
  · refine PolyBounded.of_le (G := fun n U => n + 2 + _) (by growth_poly [hpoly]) fun n U =>
      Nat.add_le_add_left
        (Finset.sup_le fun h hh => (hse h U).1.trans (polyBound_cons_le (hle hh) ..)) _
  · refine PolyBounded.of_le (G := fun n U => 3 * (n * n) + _) (by growth_poly [hpoly]) fun n U =>
      Finset.sup_le fun h hh => Nat.add_le_add
        (Nat.mul_le_mul_left 3 (Nat.mul_le_mul (hle hh) (hle hh)))
        ((hse h U).2.1.trans (polyBound_cons_le (hle hh) ..))
  · refine PolyBounded.of_le (G := fun n U => 3 + _) (by growth_poly [hpoly]) fun n U =>
      Nat.add_le_add_left
        (Finset.sup_le fun h hh => (hse h U).2.2.trans (polyBound_cons_le (hle hh) ..)) _

end Find

open Find

/-- **[VW18, Lemma 4.1]: finding a negative triangle from deciding whether there is one.** -/
theorem isHost_find : IsHost ntTask findTask findTime findNeed := by
  refine ⟨fun P p T r hsol => ⟨findProcs P.length p, P.length + 3, ?_⟩,
    fun r hr => polyNeed_find hr⟩
  refine ⟨findBody p (P.length + 2), by simp [findProcs], fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  have C : Ctx P (findProcs P.length p ++ R') p (P.length + 2) (P.length + 1) P.length T r :=
    ⟨hsol, by simp [findProcs], by simp [findProcs], by simp [findProcs]⟩
  exact find_spec C hpre hok

end Light.Sec3
