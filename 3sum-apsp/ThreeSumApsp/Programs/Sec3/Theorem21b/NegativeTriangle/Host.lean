/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Programs.Tasks

/-!
# Negative Triangle from Exact Triangle, as a host

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): whether an instance with weights in
[−U, U] has a negative triangle is decided by asking O(log U) times whether there is a zero
triangle, each time after changing the weights, edge by edge, to numbers of absolute value O(U).

nt(n, U, ab, bc, ac, fr) computes L, the least number with 2^L > 6U, writes the shifted and doubled
weights 2(w(a,b) + U), 2(w(b,c) + U), 2(2U − w(a,c)) into an array r of 3n² cells, and zeros into an
array q of 3n² cells.  Then it makes L rounds.  A round moves one more bit of every number from r to
q (prefDown), so that q holds the prefixes of the level ℓ = L − 1, L − 2, …, 0; then, for e = 2 and
for e = 3, it writes e minus the prefixes of the third matrix to an array of n² cells and asks the
solver of Exact Triangle.  The answer is 1 if one of the 2L answers is 1.

The text is cut into parts, and each part has its lemma: `NegHost.init_spec`, `pow_spec`,
`fill_spec`, `probe_spec` (one question), `round_spec`, `rounds_spec`; `NegHost.nt_spec` puts them
together, and `isHost_nt` is the result.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The text -/

namespace NegHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the weights. -/
abbrev Bound : ℕ := 1
/-- The address of the first matrix. -/
abbrev MatAB : ℕ := 2
/-- The address of the second matrix. -/
abbrev MatBC : ℕ := 3
/-- The address of the third matrix. -/
abbrev MatAC : ℕ := 4
/-- The free pointer, where the array q begins: its first part. -/
abbrev PreAB : ℕ := 5
/-- n². -/
abbrev Cells : ℕ := 6
/-- 2^L. -/
abbrev Power : ℕ := 7
/-- The number L of levels. -/
abbrev Levels : ℕ := 8
/-- The number of the round. -/
abbrev Round : ℕ := 9
/-- The answer so far. -/
abbrev Ans : ℕ := 10
/-- The result of a call. -/
abbrev Res : ℕ := 11
/-- 6U. -/
abbrev Bound6 : ℕ := 12
/-- The first part of the array r. -/
abbrev RestAB : ℕ := 14
/-- The array for the third matrix of a question. -/
abbrev Third : ℕ := 15
/-- The free pointer for the solver. -/
abbrev SolverFree : ℕ := 16
/-- The third part of the array q. -/
abbrev PreAC : ℕ := 17
/-- The second part of the array q. -/
abbrev PreBC : ℕ := 18
/-- 3n². -/
abbrev Cells3 : ℕ := 19
/-- The second part of the array r. -/
abbrev RestBC : ℕ := 20
/-- The third part of the array r. -/
abbrev RestAC : ℕ := 21

end NegHost

open NegHost

/-- The beginning of nt: sizes and addresses. -/
def ntInit : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Bound6 (k 6 *' v Bound) ;;
  .set PreBC (v PreAB +' v Cells) ;;
  .set PreAC (v PreBC +' v Cells) ;;
  .set RestAB (v PreAC +' v Cells) ;;
  .set RestBC (v RestAB +' v Cells) ;;
  .set RestAC (v RestBC +' v Cells) ;;
  .set Third (v RestAC +' v Cells) ;;
  .set SolverFree (v Third +' v Cells) ;;
  .set Cells3 (k 3 *' v Cells) ;;
  .set Power (k 1) ;;
  .set Levels (k 0)

/-- The number of levels L and the power 2^L, by doubling. -/
def ntPow : Stmt :=
  .while (v Power ≤' v Bound6) (
    .set Power (k 2 *' v Power) ;;
    .set Levels (v Levels +' k 1))

/-- The arrays r and q at the top level. -/
def ntFill (pAff : ℕ) : Stmt :=
  .call pAff [v Cells, v MatAB, k 2, k 2 *' v Bound, v RestAB] Res ;;
  .call pAff [v Cells, v MatBC, k 2, k 2 *' v Bound, v RestBC] Res ;;
  .call pAff [v Cells, v MatAC, k 0 -' k 2, k 4 *' v Bound, v RestAC] Res ;;
  .call pAff [v Cells3, v RestAB, k 0, k 0, v PreAB] Res

/-- One question to the solver of Exact Triangle: the third matrix for the exact value e, the call,
and the note of a positive answer. -/
def ntProbe (pET pAff e : ℕ) : Stmt :=
  .call pAff [v Cells, v PreAC, k 0 -' k 1, k e, v Third] Res ;;
  .call pET [v Verts, v Bound6, v PreAB, v PreBC, v Third, v SolverFree] Res ;;
  .ite (v Res =' k 1) (.set Ans (k 1)) .skip

/-- One round: the next level, and its two questions. -/
def ntRound (pET pAff pDown : ℕ) : Stmt :=
  .call pDown [v Cells3, v PreAB, v RestAB, v Power] Res ;;
  ntProbe pET pAff 2 ;;
  ntProbe pET pAff 3

/-- The L rounds. -/
def ntRounds (pET pAff pDown : ℕ) : Stmt :=
  .set Ans (k 0) ;;
  .for Round (v Levels) (ntRound pET pAff pDown)

/-- nt(n, U, ab, bc, ac, fr). -/
def ntBody (pET pAff pDown : ℕ) : Stmt :=
  ntInit ;; ntPow ;; ntFill pAff ;; ntRounds pET pAff pDown ;; .set 0 (v Ans)

/-- The number of levels: for U ≥ 1, the least L with 2^L > 6U. -/
def ntLevels (U : ℕ) : ℕ := Nat.log 2 (6 * U) + 1

/-- The time of nt, if the solver of Exact Triangle takes T n U steps. -/
def ntTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  120 * (n * n) + 120 + ntLevels U * (154 * (n * n) + 92 + 2 * T n (6 * U))

/-- The need of nt, if the solver of Exact Triangle needs r n U. -/
def ntNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 24 * U + 8 + (r n (6 * U)).word
  cells := 7 * (n * n) + (r n (6 * U)).cells
  depth := (r n (6 * U)).depth + 1

private theorem lt_two_pow_ntLevels (U : ℕ) : 6 * U < 2 ^ ntLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

private theorem two_pow_ntLevels_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ ntLevels U ≤ 12 * U := by
  have := Nat.pow_log_le_self 2 (show 6 * U ≠ 0 by omega)
  rw [ntLevels, pow_succ]
  omega

/-! ## The local variables and the hypotheses -/

namespace NegHost

/-- The locals of nt after its beginning.  The last five arguments are those that change later: the
power of two, the number of levels, the number of the round, the answer so far and the result of the
last call.  Local 13 is not used and stays 0. -/
abbrev locals (x : TriInst) (fr : ℕ) (pw lv rd ans res : ℤ) : List ℤ :=
  [x.n, x.U, x.ab, x.bc, x.ac, fr, (x.n * x.n : ℕ), pw, lv, rd, ans, res, (6 * x.U : ℕ), 0,
    (fr + 3 * (x.n * x.n) : ℕ), (fr + 6 * (x.n * x.n) : ℕ), (fr + 7 * (x.n * x.n) : ℕ),
    (fr + 2 * (x.n * x.n) : ℕ), (fr + x.n * x.n : ℕ), (3 * (x.n * x.n) : ℕ),
    (fr + 4 * (x.n * x.n) : ℕ), (fr + 5 * (x.n * x.n) : ℕ)]

/-- The program has the solver and the two loops over arrays, the instance is as the task
prescribes, and the limits allow for the need of nt. -/
structure Ctx (P₀ R' : Program) (p pAff pDown : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves etTask P₀ p T r
  aff : (P₀ ++ R')[pAff]? = some affineBody
  down : (P₀ ++ R')[pDown]? = some prefDownBody
  pre : x.Pre μ fr
  ok : (ntNeed r x.n x.U).Ok lim fr d

variable {P₀ R' : Program} {p pAff pDown : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {lim : Limits}
  {d : ℕ} {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The arithmetic facts of the hypotheses as one conjunction: what the limits allow, and that the
three matrices have n² ≥ 1 entries each and lie below the free pointer. -/
private theorem Ctx.places (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 24 * (x.U : ℤ) + 8 + (r x.n (6 * x.U)).word ≤ lim.word ∧
      fr + (7 * (x.n * x.n) + (r x.n (6 * x.U)).cells) ≤ lim.space ∧
      d + ((r x.n (6 * x.U)).depth + 1) ≤ lim.depth) ∧ 1 ≤ x.n * x.n ∧
      (x.AB.length = x.n * x.n ∧ x.BC.length = x.n * x.n ∧ x.AC.length = x.n * x.n) ∧
      x.ab + x.n * x.n ≤ fr ∧ x.bc + x.n * x.n ≤ fr ∧ x.ac + x.n * x.n ≤ fr :=
  ⟨⟨C.ok.space, by exact_mod_cast C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.mul_pos C.pre.n_pos C.pre.n_pos, ⟨C.pre.lenAB, C.pre.lenBC, C.pre.lenAC⟩, C.pre.belowAB,
    C.pre.belowBC, C.pre.belowAC⟩

/-- **affine** as a procedure, for a source and a destination that lie apart, below the free pointer
of the solver. -/
private theorem Ctx.affine_meets (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {l : List ℤ} {src dst : ℕ} {m c : ℤ} (hl : Seg μ' src l)
    (hplace : src + l.length ≤ fr + 7 * (x.n * x.n) ∧ dst + l.length ≤ fr + 7 * (x.n * x.n) ∧
      (src + l.length ≤ dst ∨ dst + l.length ≤ src))
    (hfits : ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word) :
    Meets lim (P₀ ++ R') pAff (d + 1) [l.length, src, m, c, dst] μ' (20 * l.length + 6)
      fun _ μ'' => Seg μ'' dst (affL m c l) ∧ SameOutside μ' μ'' dst l.length := by
  have hplaces := C.places
  exact Sec3.affine_meets C.aff hl C.ok.space (by omega) (by omega) hplace.2.2 hfits

/-! ## The beginning -/

/-- **The beginning of nt** sets the sizes and the addresses. -/
private theorem init_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d ntInit ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ ntInit.blockCost
      fun σ' => σ' = ⟨frame (locals x fr 1 0 0 0 0), μ⟩ := by
  have hplaces := C.places
  have hsquare : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  unfold ntInit
  -- Cells := Verts * Verts ; Bound6 := 6 * Bound
  light_set (x.n * x.n : ℕ)
  light_set (6 * x.U : ℕ)
  -- PreBC := PreAB + Cells ; PreAC := PreBC + Cells
  light_set (fr + x.n * x.n : ℕ)
  light_set (fr + 2 * (x.n * x.n) : ℕ)
  -- RestAB := PreAC + Cells ; RestBC := RestAB + Cells ; RestAC := RestBC + Cells
  light_set (fr + 3 * (x.n * x.n) : ℕ)
  light_set (fr + 4 * (x.n * x.n) : ℕ)
  light_set (fr + 5 * (x.n * x.n) : ℕ)
  -- Third := RestAC + Cells ; SolverFree := Third + Cells ; Cells3 := 3 * Cells
  light_set (fr + 6 * (x.n * x.n) : ℕ)
  light_set (fr + 7 * (x.n * x.n) : ℕ)
  light_set (3 * (x.n * x.n) : ℕ)
  -- Power := 1 ; Levels := 0
  light_set 1
  light_set 0
  rfl

/-- The state of the loop that doubles after i rounds: Power = 2^i and Levels = i. -/
def PowInv (x : TriInst) (μ : ℕ → ℤ) (fr i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame (locals x fr (2 ^ i : ℕ) i 0 0 0), μ⟩

/-- **The loop that doubles** computes the number L of levels and 2^L. -/
private theorem pow_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d ntPow ⟨frame (locals x fr 1 0 0 0 0), μ⟩ (14 * ntLevels x.U + 6)
      fun σ' => σ' = ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) 0 0 0), μ⟩ := by
  have hplaces := C.places
  have hL := two_pow_ntLevels_le C.pre.U_pos
  -- while Power ≤ Bound6: Power := 2 * Power ; Levels := Levels + 1
  refine Ends.whileBlock (PowInv x μ fr) (ntLevels x.U) (by simp [PowInv]) ?round ?done
    (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ ntLevels x.U := Nat.pow_le_pow_right (by norm_num) hi
    have hlt : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize hpw : 2 ^ i = pw at hpow hlt ⊢
    exact ⟨by light_side, by simp; omega, by light_side,
      by simp [PowInv, pow_succ', hpw, update_frame_setLocal, locals]⟩
  case done =>
    rintro _ rfl
    have hlt := lt_two_pow_ntLevels x.U
    generalize 2 ^ ntLevels x.U = pw at hL hlt ⊢
    exact ⟨by light_side, by simp; omega, rfl⟩

/-! ## The memory -/

/-- The memory of nt at the level ℓ: the array q holds the prefixes, the array r the rests, and
nothing below the free pointer has changed. -/
def NtMem (x : TriInst) (μ : ℕ → ℤ) (fr ℓ : ℕ) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' fr ((negStart x.U x.AB x.BC x.AC).map (prefQ ℓ)) ∧
    Seg μ' (fr + 3 * (x.n * x.n))
      ((negStart x.U x.AB x.BC x.AC).map (prefR (ntLevels x.U) ℓ)) ∧
    Kept μ μ' fr

private theorem length_negStart {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) :
    (negStart x.U x.AB x.BC x.AC).length = 3 * (x.n * x.n) := by
  simp only [negStart, List.length_append, length_affL, hpre.lenAB, hpre.lenBC, hpre.lenAC]
  omega

/-- The numbers at the start are between 0 and 6U, and below 2^L. -/
private theorem negStart_range {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) :
    ∀ z ∈ negStart x.U x.AB x.BC x.AC, 0 ≤ z ∧ z ≤ 6 * (x.U : ℤ) ∧ z < 2 ^ ntLevels x.U := by
  intro z hz
  obtain ⟨h0, h1⟩ := bounds_of_mem_negStart hpre.leAB hpre.leBC hpre.leAC z hz
  have h2 : ((6 * x.U : ℕ) : ℤ) < ((2 ^ ntLevels x.U : ℕ) : ℤ) := by
    exact_mod_cast lt_two_pow_ntLevels x.U
  push_cast at h2
  exact ⟨h0, h1, by omega⟩

/-- The three shifted and doubled matrices, one after the other, are the array r at the start. -/
private theorem seg_negStart (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {a : ℕ}
    (h1 : Seg μ' (a + 3 * (x.n * x.n)) (affL 2 (2 * x.U) x.AB))
    (h2 : Seg μ' (a + 4 * (x.n * x.n)) (affL 2 (2 * x.U) x.BC))
    (h3 : Seg μ' (a + 5 * (x.n * x.n)) (affL (-2) (4 * x.U) x.AC)) :
    Seg μ' (a + 3 * (x.n * x.n)) (negStart x.U x.AB x.BC x.AC) := by
  rw [negStart, seg_append, seg_append]
  simp only [length_affL, hpre.lenAB, hpre.lenBC]
  rw [show a + 3 * (x.n * x.n) + x.n * x.n = a + 4 * (x.n * x.n) by omega,
    show a + 4 * (x.n * x.n) + x.n * x.n = a + 5 * (x.n * x.n) by omega]
  exact ⟨h1, h2, h3⟩

/-- The products and the sums that are formed in the first three calls of affine fit in a word. -/
private theorem fits_of_absLe {l : List ℤ} {U W : ℤ} (hl : AbsLe l U) (hW : 24 * U + 8 ≤ W) :
    (∀ w ∈ l, |2 * w| ≤ W ∧ |2 * w + 2 * U| ≤ W) ∧
      ∀ w ∈ l, |-2 * w| ≤ W ∧ |-2 * w + 4 * U| ≤ W := by
  constructor <;> intro w hw <;> have := abs_le.1 (hl w hw) <;> simp only [abs_le] <;> omega

/-- **The four calls of affine** fill the arrays r and q for the top level. -/
private theorem fill_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) (pw lv rd ans res : ℤ) :
    Ends lim (P₀ ++ R') d (ntFill pAff) ⟨frame (locals x fr pw lv rd ans res), μ⟩
      (120 * (x.n * x.n) + 60) fun σ' => ∃ res' μ',
        σ' = ⟨frame (locals x fr pw lv rd ans res'), μ'⟩ ∧ NtMem x μ fr (ntLevels x.U) μ' := by
  have hpre := C.pre
  have hplaces := C.places
  have hlenZ := length_negStart hpre
  have hZ := negStart_range hpre
  have hW : 24 * (x.U : ℤ) + 8 ≤ lim.word := by omega
  unfold ntFill
  -- Res := pAff(Cells, MatAB, 2, 2 * Bound, RestAB)
  refine Ends.callToThen (C.affine_meets (m := 2) (c := 2 * x.U) (dst := fr + 3 * (x.n * x.n))
    hpre.segAB (by omega) (fits_of_absLe hpre.leAB hW).1) ?_
    (ha := by light_side [hpre.lenAB]) (hT := by simp [hpre.lenAB]; omega)
  rintro r₁ μ₁ ⟨s₁, o₁⟩
  -- Res := pAff(Cells, MatBC, 2, 2 * Bound, RestBC)
  refine Ends.callToThen (C.affine_meets (m := 2) (c := 2 * x.U) (dst := fr + 4 * (x.n * x.n))
    hpre.segBC.keep (by omega) (fits_of_absLe hpre.leBC hW).1) ?_
    (ha := by light_side [hpre.lenBC]) (hT := by simp [hpre.lenAB, hpre.lenBC]; omega)
  rintro r₂ μ₂ ⟨s₂, o₂⟩
  -- Res := pAff(Cells, MatAC, 0 - 2, 4 * Bound, RestAC)
  refine Ends.callToThen (C.affine_meets (m := -2) (c := 4 * x.U) (dst := fr + 5 * (x.n * x.n))
    hpre.segAC.keep (by omega) (fits_of_absLe hpre.leAC hW).2) ?_ (ha := by light_side [hpre.lenAC])
    (hT := by simp [hpre.lenAB, hpre.lenBC, hpre.lenAC]; omega)
  rintro r₃ μ₃ ⟨s₃, o₃⟩
  have sZ : Seg μ₃ (fr + 3 * (x.n * x.n)) (negStart x.U x.AB x.BC x.AC) :=
    seg_negStart hpre s₁.keep s₂.keep s₃
  -- Res := pAff(Cells3, RestAB, 0, 0, PreAB)
  refine Ends.callTo (C.affine_meets (m := 0) (c := 0) (dst := fr) sZ (by omega)
    fun w _ => by simp; omega) ?_ (ha := by light_side [hlenZ])
    (hT := by simp [hpre.lenAB, hpre.lenBC, hpre.lenAC, hlenZ]; omega)
  rintro r₄ μ₄ ⟨s₄, o₄⟩
  refine ⟨r₄, μ₄, rfl, ?_, ?_, fun c hc => ?_⟩
  · rw [map_prefQ_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact s₄
  · rw [map_prefR_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact sZ.keep
  · light_keep

/-! ## One question -/

/-- The instance of Exact Triangle for the level ℓ and the exact value e, as it lies in the arrays
of nt. -/
def question (x : TriInst) (fr ℓ : ℕ) (e : ℤ) : TriInst :=
  ⟨x.n, 6 * x.U, fr, fr + x.n * x.n, fr + 6 * (x.n * x.n), (affL 2 (2 * x.U) x.AB).map (prefQ ℓ),
    (affL 2 (2 * x.U) x.BC).map (prefQ ℓ), negThird x.U ℓ e x.AC⟩

/-- The instance of Exact Triangle for the level ℓ and the exact value e has a zero triangle. -/
def NtYes (x : TriInst) (ℓ : ℕ) (e : ℤ) : Prop :=
  (triOf x.n ((affL 2 (2 * x.U) x.AB).map (prefQ ℓ)) ((affL 2 (2 * x.U) x.BC).map (prefQ ℓ))
    (negThird x.U ℓ e x.AC)).HasZeroTriangle

/-- The prefixes are between 0 and 6U. -/
private theorem prefQ_range (hpre : x.Pre μ fr) (ℓ : ℕ) {z : ℤ}
    (hz : z ∈ negStart x.U x.AB x.BC x.AC) :
    0 ≤ prefQ ℓ z ∧ prefQ ℓ z ≤ 6 * (x.U : ℤ) := by
  obtain ⟨h0, h1⟩ := bounds_of_mem_negStart hpre.leAB hpre.leBC hpre.leAC z hz
  exact ⟨prefQ_nonneg h0 ℓ, (prefQ_le h0 ℓ).trans h1⟩

/-- The three parts of the array q. -/
private theorem seg_parts (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hq : Seg μ' fr ((negStart x.U x.AB x.BC x.AC).map (prefQ ℓ))) :
    Seg μ' fr ((affL 2 (2 * x.U) x.AB).map (prefQ ℓ)) ∧
      Seg μ' (fr + x.n * x.n) ((affL 2 (2 * x.U) x.BC).map (prefQ ℓ)) ∧
      Seg μ' (fr + 2 * (x.n * x.n)) ((affL (-2) (4 * x.U) x.AC).map (prefQ ℓ)) := by
  simp only [negStart, List.map_append] at hq
  rw [seg_append, seg_append] at hq
  simp only [List.length_map, length_affL, hpre.lenAB, hpre.lenBC] at hq
  rwa [show fr + x.n * x.n + x.n * x.n = fr + 2 * (x.n * x.n) by omega] at hq

/-- The question is an instance of Exact Triangle as the task prescribes. -/
private theorem question_pre (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ} {e : ℤ} (he : e = 2 ∨ e = 3)
    (hq : Seg μ' fr ((negStart x.U x.AB x.BC x.AC).map (prefQ ℓ)))
    (hthird : Seg μ' (fr + 6 * (x.n * x.n)) (negThird x.U ℓ e x.AC)) :
    (question x fr ℓ e).Pre μ' (fr + 7 * (x.n * x.n)) := by
  obtain ⟨hqX, hqY, -⟩ := seg_parts hpre hq
  have hle : ∀ l : List ℤ, (∀ z ∈ l, z ∈ negStart x.U x.AB x.BC x.AC) →
      AbsLe (l.map (prefQ ℓ)) ((6 * x.U : ℕ) : ℤ) := by
    intro l hl y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_range hpre ℓ (hl z hz)
    push_cast
    exact abs_le.2 ⟨by omega, by omega⟩
  have hU := hpre.U_pos
  exact {
    n_pos := hpre.n_pos
    U_pos := by simp only [question]; omega
    lenAB := by simp [question, hpre.lenAB]
    lenBC := by simp [question, hpre.lenBC]
    lenAC := by simp [question, negThird, hpre.lenAC]
    segAB := hqX
    segBC := hqY
    segAC := hthird
    leAB := hle _ fun z hz => by simp [negStart, hz]
    leBC := hle _ fun z hz => by simp [negStart, hz]
    leAC := fun y hy => by
      simp only [question]
      push_cast
      exact abs_le_of_mem_negThird hpre.U_pos hpre.leAC ℓ he y hy
    belowAB := by simp only [question]; omega
    belowBC := by simp only [question]; omega
    belowAC := by simp only [question]; omega }

/-- The state of nt between two steps of a round: the locals, with some result of the last call,
and the memory at the level ℓ. -/
def St (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (rd ans : ℤ) (ℓ : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) rd ans res), μ'⟩ ∧
      NtMem x μ fr ℓ μ'

/-- The arrays q and r and the cells below the free pointer survive a question. -/
private theorem ntMem_of_question (hpre : x.Pre μ fr) {μ₀ μ₁ μ₂ : ℕ → ℤ} {ℓ : ℕ}
    (hm : NtMem x μ fr ℓ μ₀) (h₁ : SameOutside μ₀ μ₁ (fr + 6 * (x.n * x.n)) (x.n * x.n))
    (h₂ : Kept μ₁ μ₂ (fr + 7 * (x.n * x.n))) : NtMem x μ fr ℓ μ₂ := by
  obtain ⟨hq, hr, hk⟩ := hm
  have hlenZ := length_negStart hpre
  exact ⟨hq.keep (by light_keep [hlenZ]), hr.keep (by light_keep [hlenZ]),
    fun c hc => by light_keep⟩

/-- **One question** leaves the arrays as they are, and sets Ans to 1 if the instance for the level
ℓ and the exact value e has a zero triangle. -/
private theorem probe_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {ℓ e : ℕ}
    (he : e = 2 ∨ e = 3) {rd : ℤ} {A : Prop} {σ : State} (hσ : St x μ fr rd (flag A) ℓ σ) :
    Ends lim (P₀ ++ R') d (ntProbe p pAff e) σ (20 * (x.n * x.n) + 29 + T x.n (6 * x.U))
      (St x μ fr rd (flag (A ∨ NtYes x ℓ e)) ℓ) := by
  obtain ⟨res, μ₀, rfl, hm⟩ := hσ
  have hpre := C.pre
  have hplaces := C.places
  have he' : (e : ℤ) = 2 ∨ (e : ℤ) = 3 := by rcases he with rfl | rfl <;> simp
  have hlenV : ((affL (-2) (4 * x.U) x.AC).map (prefQ ℓ)).length = x.n * x.n := by
    simp [hpre.lenAC]
  unfold ntProbe
  -- Res := pAff(Cells, PreAC, 0 - 1, e, Third)
  refine Ends.callToThen (C.affine_meets (m := -1) (c := e) (dst := fr + 6 * (x.n * x.n))
    (seg_parts hpre hm.1).2.2 (by omega) fun w hx => ?_) ?_
    (ha := by light_side [hlenV]) (hT := by simp [hlenV]; omega)
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    have := prefQ_range hpre ℓ (z := z) (by simp [negStart, hz])
    simp only [abs_le]
    omega
  rintro r₁ μ₁ ⟨hthird, h₁⟩
  rw [hlenV] at h₁
  -- Res := pET(Verts, Bound6, PreAB, PreBC, Third, SolverFree)
  refine Ends.callToThen (C.solver.meets R' (question x fr ℓ e) (fr + 7 * (x.n * x.n))
    (question_pre hpre he' (hm.1.keep (by light_keep [length_negStart hpre])) hthird)
    { word := by simp only [etTask, question]; omega
      cells := by simp only [etTask, question]; omega
      space := C.ok.space
      depth := by simp only [etTask, question]; omega }) ?_ (by simp [etTask, question])
    (hT := by simp [etTask, question, hlenV]; omega)
  rintro r₂ μ₂ ⟨hres, h₂⟩
  replace hres : r₂ = flag (NtYes x ℓ e) := hres
  have hm₂ := ntMem_of_question hpre hm h₁ h₂
  -- if Res = 1 then Ans := 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp; omega)
    (by simp [etTask, question, hlenV]; omega)
  · have hc' : r₂ = 1 := by simpa using hc
    refine Ends.setTo 1 ⟨r₂, μ₂, ?_, hm₂⟩ (by simp; omega)
      (by simp [etTask, question, hlenV]; omega)
    rw [flag_of (Or.inr (flag_eq_one_iff.1 (hres ▸ hc')))]
    rfl
  · have hc' : ¬ r₂ = 1 := by simpa using hc
    refine Ends.skip ⟨r₂, μ₂, ?_, hm₂⟩
    rw [flag_congr (show (A ∨ NtYes x ℓ e) ↔ A from
      ⟨fun h => h.resolve_right fun hy => hc' (hres.trans (flag_of hy)), Or.inl⟩)]
    rfl

/-! ## The rounds -/

/-- One of the questions at the levels from ℓ₀ on has the answer yes. -/
def NtFound (x : TriInst) (L ℓ₀ : ℕ) : Prop :=
  ∃ ℓ, ℓ₀ ≤ ℓ ∧ ℓ < L ∧ ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ NtYes x ℓ e

private theorem ntFound_step (x : TriInst) {L ℓ : ℕ} (h : ℓ < L) :
    ((NtFound x L (ℓ + 1) ∨ NtYes x ℓ 2) ∨ NtYes x ℓ 3) ↔ NtFound x L ℓ := by
  constructor
  · rintro ((⟨ℓ', h1, h2, h3⟩ | h2) | h3)
    · exact ⟨ℓ', by omega, h2, h3⟩
    · exact ⟨ℓ, le_rfl, h, 2, Or.inl rfl, h2⟩
    · exact ⟨ℓ, le_rfl, h, 3, Or.inr rfl, h3⟩
  · rintro ⟨ℓ', h1, h2, e, he, h3⟩
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      rcases he with rfl | rfl
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h3
    · exact Or.inl (Or.inl ⟨ℓ', by omega, h2, e, he, h3⟩)

/-- The number of the round can be read and changed. -/
private theorem St.round {rd ans : ℤ} {ℓ : ℕ} {σ : State} (h : St x μ fr rd ans ℓ σ) (rd' : ℤ) :
    σ.loc Round = rd ∧ St x μ fr rd' ans ℓ { σ with loc := Function.update σ.loc Round rd' } := by
  obtain ⟨res, μ', rfl, hm⟩ := h
  exact ⟨rfl, res, μ', by rw [update_frame_setLocal]; rfl, hm⟩

/-- What prefDown needs holds at every level above 0. -/
private theorem down_pre (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ ntLevels x.U) (hm : NtMem x μ fr (ℓ + 1) μ') :
    PrefPre lim μ' fr (fr + 3 * (x.n * x.n)) (2 ^ ntLevels x.U)
      ((negStart x.U x.AB x.BC x.AC).map (prefQ (ℓ + 1)))
      ((negStart x.U x.AB x.BC x.AC).map (prefR (ntLevels x.U) (ℓ + 1))) := by
  have hplaces := C.places
  have hlenZ := length_negStart C.pre
  have hL : ((2 ^ ntLevels x.U : ℕ) : ℤ) ≤ ((12 * x.U : ℕ) : ℤ) := by
    exact_mod_cast two_pow_ntLevels_le C.pre.U_pos
  push_cast at hL
  refine ⟨hm.1, hm.2.1, by simp, C.ok.space, by simp [hlenZ]; omega, by simp [hlenZ]; omega,
    by simp [hlenZ], by omega, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_range C.pre (ℓ + 1) hz
    simp only [abs_le]
    omega
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h0 := prefR_nonneg (ntLevels x.U) (ℓ + 1) z
    have h1 := prefR_lt hℓ z
    simp only [abs_le]
    omega

/-- **One round**: from the level ℓ + 1 to the level ℓ, and the two questions at the level ℓ. -/
private theorem round_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ ntLevels x.U) {rd : ℤ} {σ : State}
    (hσ : St x μ fr rd (flag (NtFound x (ntLevels x.U) (ℓ + 1))) (ℓ + 1) σ) :
    Ends lim (P₀ ++ R') d (ntRound p pAff pDown) σ (154 * (x.n * x.n) + 70 + 2 * T x.n (6 * x.U))
      (St x μ fr rd (flag (NtFound x (ntLevels x.U) ℓ)) ℓ) := by
  obtain ⟨res, μ₀, rfl, hm⟩ := hσ
  have hplaces := C.places
  have hlenZ := length_negStart C.pre
  unfold ntRound
  -- Res := pDown(Cells3, PreAB, RestAB, Power)
  refine Ends.callToThen (prefDown_meets C.down (down_pre C hℓ hm)) ?_ (by simp [hlenZ])
    (hT := by simp [hlenZ]; omega)
  rintro r₁ μ₁ ⟨hq, hr, hrest⟩
  rw [zipWith_shiftQ hℓ] at hq
  rw [map_shiftR hℓ] at hr
  have hσ₁ : St x μ fr rd (flag (NtFound x (ntLevels x.U) (ℓ + 1))) ℓ
      ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) rd
        (flag (NtFound x (ntLevels x.U) (ℓ + 1))) r₁), μ₁⟩ :=
    ⟨r₁, μ₁, rfl, hq, hr,
      fun c hc => (hrest c (Or.inl hc) (Or.inl (by omega))).trans (hm.2.2 c hc)⟩
  -- the question for e = 2, then the question for e = 3
  refine Ends.next _ ((probe_spec C (Or.inl rfl) hσ₁).mono le_rfl fun σ₂ hσ₂ => ?_)
    (by simp [hlenZ]; omega)
  refine (probe_spec C (Or.inr rfl) hσ₂).mono (by simp [hlenZ]; omega) fun σ₃ hσ₃ => ?_
  rwa [flag_congr (by simpa using ntFound_step x (Nat.lt_of_succ_le hℓ))] at hσ₃

/-- **The L rounds**: in the end Ans says whether one of the questions at the levels below L was
answered yes. -/
private theorem rounds_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {res : ℤ} {μ' : ℕ → ℤ}
    (hm : NtMem x μ fr (ntLevels x.U) μ') :
    Ends lim (P₀ ++ R') d (ntRounds p pAff pDown)
      ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) 0 0 res), μ'⟩
      (8 + ntLevels x.U * (154 * (x.n * x.n) + 78 + 2 * T x.n (6 * x.U)))
      (St x μ fr (ntLevels x.U) (flag (NtFound x (ntLevels x.U) 0)) 0) := by
  have hplaces := C.places
  have hL : ((ntLevels x.U : ℕ) : ℤ) ≤ ((12 * x.U : ℕ) : ℤ) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := ntLevels x.U)).le.trans
      (two_pow_ntLevels_le C.pre.U_pos)
  push_cast at hL
  unfold ntRounds
  -- Ans := 0
  light_set 0
  -- for Round < Levels: the rounds
  refine Ends.for (fun t σ => St x μ fr t (flag (NtFound x (ntLevels x.U) (ntLevels x.U - t)))
    (ntLevels x.U - t) σ) (ntLevels x.U) (154 * (x.n * x.n) + 70 + 2 * T x.n (6 * x.U))
    ?start ?round ?done ?bound (by omega) ?time
  case start =>
    refine ⟨res, μ', ?_, hm⟩
    rw [flag_of_not (by rintro ⟨ℓ, h1, h2, -⟩; omega), update_frame_setLocal]
    rfl
  case round =>
    intro t σ ht _ hσ
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ntLevels x.U - t = ℓ + 1 := ⟨ntLevels x.U - t - 1, by omega⟩
    rw [show ntLevels x.U - (t + 1) = ℓ by omega]
    rw [hℓ] at hσ
    refine (round_spec C (by omega) hσ).mono le_rfl fun σ' hσ' => ?_
    exact_mod_cast hσ'.round ((t : ℤ) + 1)
  case done =>
    intro σ _ hσ
    simpa using hσ
  case bound =>
    rintro t _ - - ⟨res', μ'', rfl, -⟩
    exact ⟨trivial, rfl⟩
  case time =>
    simp
    ring_nf
    omega

/-! ## The procedure -/

/-- **nt is correct**, in every program that begins with the solver's program and has the two loops
over arrays. -/
theorem nt_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d (ntBody p pAff pDown) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (ntTime T x.n x.U) fun σ' =>
        σ'.loc 0 = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ σ'.mem fr := by
  have hpre := C.pre
  have hrounds : ntLevels x.U * (154 * (x.n * x.n) + 92 + 2 * T x.n (6 * x.U)) =
      ntLevels x.U * (154 * (x.n * x.n) + 78 + 2 * T x.n (6 * x.U)) + 14 * ntLevels x.U := by
    ring
  unfold ntBody ntTime
  -- ntInit
  refine Ends.next _ ((init_spec C).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ rfl
  -- ntPow
  refine Ends.next _ ((pow_spec C).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ rfl
  -- ntFill
  refine Ends.next _ ((fill_spec C _ _ _ _ _).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ ⟨res, μ₁, rfl, hm⟩
  -- ntRounds
  refine Ends.next _ ((rounds_spec C hm).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ ⟨res', μ₂, rfl, hm₂⟩
  -- the result is Ans
  refine Ends.setTo (flag (NtFound x (ntLevels x.U) 0)) ⟨?_, hm₂.2.2⟩ (hT := by
    simp [ntInit]; omega)
  have h3 : 3 * x.U < 2 ^ ntLevels x.U := by have := lt_two_pow_ntLevels x.U; omega
  refine flag_congr ?_
  rw [hasNegativeTriangle_iff_exists_level hpre.lenAB hpre.lenBC hpre.lenAC hpre.leAB hpre.leBC
    hpre.leAC h3]
  exact ⟨fun ⟨ℓ, _, h2, h⟩ => ⟨ℓ, h2, h⟩, fun ⟨ℓ, h2, h⟩ => ⟨ℓ, Nat.zero_le _, h2, h⟩⟩

end NegHost

/-- The need of nt is polynomially bounded if the need of the solver is. -/
theorem polyNeed_ntNeed {r : ℕ → ℕ → Need} (h : PolyNeed r) : PolyNeed (ntNeed r) := by
  unfold ntNeed
  poly_need [h.word, h.cells, h.depth]

/-- **Negative Triangle from Exact Triangle**: from every solver of Exact Triangle, the three
procedures affine, prefDown, nt make a solver of Negative Triangle. -/
theorem isHost_nt : IsHost etTask ntTask ntTime ntNeed := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, prefDownBody, ntBody p P.length (P.length + 1)],
    P.length + 2, ntBody p P.length (P.length + 1), by simp, fun R lim d x μ fr hpre hok => ?_⟩,
    fun r => polyNeed_ntNeed⟩
  rw [List.append_assoc]
  exact NegHost.nt_spec ⟨hsol, by simp, by simp, hpre, hok⟩

end Light.Sec3
