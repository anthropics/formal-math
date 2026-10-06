/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Compiler.WholeProgram
public import ThreeSumApsp.Lang.WordSize
public import ThreeSumApsp.Machine.Solving
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Size

/-!
# From runs of light programs to the running-time notions of the word RAM

`Solves` says what it means that a program of the word RAM solves a problem within a time bound, and
`IsDataStructure` that two programs form a data structure.  This file gives the corresponding
notions for light programs (`ProgramSolves`, `ProgramIsDataStructure`; what they ask on one instance
are the structures `ProgramSolvesAt` and `ProgramIsDataStructureAt`), which speak only about `Exec`,
and proves that the compiled programs satisfy the notions of the word RAM with time C · T + C, where
C depends on the compiled program only (`solves_of_programSolves`, `isDataStructure_of_program`).

1. **Word size.**  The limits of the run are polynomial in the parameters of the instance (`Small`),
   so they fit every admissible word size of slope `slopeOf` (`fits_of_small`).
2. **Time and space.**  c steps become at most C · c + C steps (`ramSteps_le`); calls nested d deep
   reach at most C · d + C cells below 0 (`lowCell_le`).
3. **Runs.**  Each run is one use of `compileProgram_correct`.  A solver is one run from the initial
   memory (`input_loadWords`).  A data structure is one such run for the preprocessing and then an
   induction on the list of queries, each of them one run (`serves_of_program`).
4. **From specifications.**  The runs that the two notions ask for come from specifications of the
   procedures (`Meets.main`, `AnswersQueries.of_meets`).
5. **The additive constant.**  If T ≥ 1, the bound C · (A · T) + C is at most C (A + 1) · T
   (`solves_of_programSolves_scaled`, `isDataStructure_of_program_scaled`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light

open ThreeSumApsp Compiler
open EndStatement (exec loadWords)

/-! ## The notion for light programs -/

/-- The limits are at most 2^s ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of the instance. -/
structure Small (s k : ℕ) (params : List ℕ) (lim : Limits) : Prop where
  nonneg : 0 ≤ lim.word
  word : lim.word ≤ (polyBound s k params : ℤ)
  space : lim.space ≤ polyBound s k params
  depth : lim.depth ≤ polyBound s k params

/-- What is asked of the run of procedure p0 on the instance x: within the limits lim it ends in the
state σ' after c steps. -/
structure ProgramSolvesAt (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (x : prob.Inst) (T : ℝ) (lim : Limits) (σ' : State) (c : ℕ) : Prop where
  /-- The run starts on the memory that holds the input of the problem. -/
  run : Exec lim P 0 (mainStmt p0) ⟨frame [0, 0, 0], memOf (prob.input x)⟩ σ' c
  /-- It ends within the time bound. -/
  time : (c : ℝ) ≤ T
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ prob.input x, |v| ≤ lim.word
  /-- The limits are polynomial in the parameters of the instance. -/
  small : Small s k (prob.params x) lim
  /-- The result gives the verdict, and the cells after the input hold the output. -/
  answer : prob.IsAnswer x (verdictOf dec (σ'.loc 0)) fun i => σ'.mem ((prob.input x).length + i)

/-- **A light program solves a problem.**  Procedure p0 of P, called on the memory that holds the
input of the problem, ends within T x steps and within limits that are polynomial in the
parameters; its result gives the verdict (if dec: accept exactly if the result is positive;
otherwise accept), and the cells after the input hold the output. -/
def ProgramSolves (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : Limits) (σ' : State) (c : ℕ),
    ProgramSolvesAt prob P p0 dec s k x (T x) lim σ' c

/-- **The outermost statement calls a procedure that meets a specification.**  The call costs four
steps, and B is any real bound for the time. -/
theorem Meets.main {lim : Limits} {P : Program} {p : ℕ} {i j : ℤ} {μ : ℕ → ℤ} {T : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop} {B : ℝ} (h : Meets lim P p 1 [i, j] μ T R) (hd : 0 < lim.depth)
    (hB : ((T + 4 : ℕ) : ℝ) ≤ B) :
    ∃ (σ' : State) (c : ℕ), Exec lim P 0 (mainStmt p) ⟨frame [0, i, j], μ⟩ σ' c ∧ (c : ℝ) ≤ B ∧
      R (σ'.loc 0) σ'.mem := by
  obtain ⟨σ', c, hex, hc, hR⟩ : Ends lim P 0 (mainStmt p) ⟨frame [0, i, j], μ⟩ (T + 4)
      fun σ' => R (σ'.loc 0) σ'.mem :=
    Ends.callTo h fun _ _ hR => hR
  exact ⟨σ', c, hex, le_trans (by exact_mod_cast hc) hB, hR⟩

/-! ## The word size -/

/-- A number that depends on the compiled program only: times the polynomial bound on the limits,
it exceeds all four numbers that have to fit in a word (`Fits`). -/
def textBound (P : Program) (dec : Bool) : ℕ := 32 + 8 * (frameSize P + 1) + 2 * dispPos P dec

/-- The number of binary digits of that number. -/
def textBoundBits (P : Program) (dec : Bool) : ℕ := Nat.size (textBound P dec)

/-- The slope of the word size for a compiled program: the exponents s and k of the bound
2^s ((p₁ + 1) ⋯ (p_r + 1))^k on the limits, and the bits for the numbers that the compiled code
itself forms (offsets in a frame, positions in the code). -/
def slopeOf (P : Program) (dec : Bool) (s k r : ℕ) : ℕ := textBoundBits P dec + s + k * r + k

/-- The word size fits the limits if the limits, the largest number N of the pool and the number Q
of cells of the stack, with the factors of `Fits`, are below a number B ≤ 2^W. -/
private theorem fits_of_lt {W : ℕ} {lim : Limits} {N Q B : ℕ} (hB : B ≤ 2 ^ W)
    (hword : 2 * (2 * lim.word + 2) < (B : ℤ)) (hspace : 2 * lim.space < B) (hstack : 4 * Q < B)
    (hpool : 2 * N < B) : Fits W lim N Q := by
  have hB' : (B : ℤ) ≤ (2 : ℤ) ^ W := by exact_mod_cast hB
  constructor <;> omega

/-- Limits that are polynomial in the parameters fit every admissible word size. -/
theorem fits_of_small {W s k r b : ℕ} {params : List ℕ} {lim : Limits} (P : Program) (dec : Bool)
    (h : Small s k params lim) (hadm : Admissible b params W) (hr : params.length ≤ r)
    (hb : slopeOf P dec s k r ≤ b) : Fits W lim (dispPos P dec) (stackCells P lim) := by
  have hword := h.word
  have hspace := h.space
  have hdepth := h.depth
  set pb := polyBound s k params with hpb
  have hpb_pos : 1 ≤ pb := one_le_polyBound s k params
  -- the text's constant times the polynomial is below 2^W
  have hB : 2 ^ textBoundBits P dec * pb ≤ 2 ^ W := by
    rw [hpb, polyBound_mul]
    exact polyBound_le hadm hr (by unfold slopeOf at hb; omega)
  have hlt : textBound P dec * pb < 2 ^ textBoundBits P dec * pb :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) hpb_pos
  have htext : textBound P dec * pb
      = 32 * pb + 8 * ((frameSize P + 1) * pb) + 2 * (dispPos P dec * pb) := by
    unfold textBound; ring
  -- and each of the four numbers is below the text's constant times the polynomial
  have hstack : (frameSize P + 1) * (lim.depth + 1) ≤ 2 * ((frameSize P + 1) * pb) :=
    (Nat.mul_le_mul_left _ (by omega : lim.depth + 1 ≤ 2 * pb)).trans_eq (by ring)
  have hpool : dispPos P dec ≤ dispPos P dec * pb := Nat.le_mul_of_pos_right _ hpb_pos
  refine fits_of_lt hB ?_ ?_ ?_ ?_
  · -- 2 (2 word + 2) ≤ 4 pb + 4 ≤ 8 pb
    have : ((8 * pb : ℕ) : ℤ) < ((2 ^ textBoundBits P dec * pb : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 8 * pb < 2 ^ textBoundBits P dec * pb)
    omega
  · -- 2 space ≤ 2 pb
    omega
  · -- 4 (4 + (F + 1) (depth + 1)) ≤ 16 pb + 8 (F + 1) pb
    unfold stackCells mainFrame
    omega
  · -- 2 N ≤ 2 N pb
    omega

/-! ## Time and space -/

/-- The constant of the time and space bounds of a compiled program: the two constants of the time,
and the extent of the negative cells that are in use before any call. -/
def timeConst (P : Program) (dec : Bool) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) + lowCell P dec ⟨0, 0, 0⟩

private theorem ramSteps_mono (P : Program) (dec : Bool) {c c' : ℕ} (h : c ≤ c') :
    ramSteps P dec c ≤ ramSteps P dec c' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

/-- The time of a compiled program. -/
theorem ramSteps_le (P : Program) (dec : Bool) (c : ℕ) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * (c : ℝ) + timeConst P dec := by
  have hstart : startCost P dec ≤ timeConst P dec := by unfold timeConst; omega
  have hsim : stepsPerStep (dispPos P dec) ≤ timeConst P dec := by unfold timeConst; omega
  have : ramSteps P dec c ≤ timeConst P dec * c + timeConst P dec :=
    (Nat.add_comm _ _).trans_le (Nat.add_le_add (Nat.mul_le_mul_right c hsim) hstart)
  exact_mod_cast this

private theorem ramSteps_le_of_le (P : Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * T + timeConst P dec :=
  (ramSteps_le P dec c).trans (by gcongr)

/-- The space of a compiled program below the cell 0. -/
private theorem lowCell_le (P : Program) (dec : Bool) (lim : Limits) :
    lowCell P dec lim ≤ timeConst P dec * lim.depth + timeConst P dec := by
  have hconst : lowCell P dec ⟨0, 0, 0⟩ ≤ timeConst P dec := by unfold timeConst; omega
  -- before any call the stack has 4 + (F + 1) cells; each level of calls adds F + 1
  have hstack₀ : 2 * (4 + (frameSize P + 1) * (0 + 1)) ≤ lowCell P dec ⟨0, 0, 0⟩ := le_max_left _ _
  have hstack : 2 * stackCells P lim
      = 2 * (frameSize P + 1) * lim.depth + 2 * (4 + (frameSize P + 1)) := by
    unfold stackCells mainFrame; ring
  have hframes : 2 * (frameSize P + 1) * lim.depth ≤ timeConst P dec * lim.depth :=
    Nat.mul_le_mul_right _ (by omega)
  -- the pool does not depend on the limits
  have hpool : 25 + 4 * dispPos P dec ≤ lowCell P dec ⟨0, 0, 0⟩ := le_max_right _ _
  exact max_le (by omega) (by omega)

/-- A cell that lies more than C · S + C cells before or after the input is out of the reach of a
run whose limits on addresses and on the nesting of calls are given by S. -/
private theorem far_of_space {P : Program} {dec : Bool} {lim : Limits} {len : ℕ} {S : ℝ} {a : ℤ}
    (hspace : (lim.space : ℝ) ≤ len + S) (hdepth : (lim.depth : ℝ) ≤ S)
    (ha : (a : ℝ) < -((timeConst P dec : ℝ) * S + timeConst P dec) ∨
      (len : ℝ) + ((timeConst P dec : ℝ) * S + timeConst P dec) < (a : ℝ)) :
    a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a := by
  have hS : 0 ≤ S := le_trans (by positivity) hdepth
  refine ha.imp (fun ha => ?_) fun ha => ?_
  · have hlow : (lowCell P dec lim : ℝ) ≤ (timeConst P dec : ℝ) * lim.depth + timeConst P dec := by
      exact_mod_cast lowCell_le P dec lim
    have : (a : ℝ) < -(lowCell P dec lim : ℝ) :=
      ha.trans_le (neg_le_neg (hlow.trans (by gcongr)))
    exact_mod_cast this
  · have h1 : (1 : ℝ) ≤ timeConst P dec := by
      exact_mod_cast (by unfold timeConst startCost; omega)
    -- space ≤ len + S ≤ len + (C S + C) < a
    have hCS : S ≤ (timeConst P dec : ℝ) * S := le_mul_of_one_le_left hS h1
    have : (lim.space : ℝ) ≤ (a : ℝ) := by linarith
    exact_mod_cast this

/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}

/-- The initial memory holds the input, and zeros in the cells of the two arguments. -/
theorem input_loadWords (W : ℕ) {ws : List ℤ} (h0 : 0 ≤ lim.word) (h : ∀ v ∈ ws, |v| ≤ lim.word) :
    Input lim (memOf ws) 0 0 (loadWords W ws) where
  rep := loadWords_mem_nat W ws
  bounded := AbsLe.abs_getD_le h0 h
  arg1 := loadWords_mem_neg W ws (by decide)
  arg2 := loadWords_mem_neg W ws (by decide)
  arg1_le := by simpa using h0
  arg2_le := by simpa using h0

/-- Reading the output: a cell of a memory that holds μ, as a signed word. -/
theorem Compiler.Holds.output {c : ℤ → BitVec W} (h : Holds W lim μ c) {N Q : ℕ}
    (hfit : Fits W lim N Q) (off i : ℕ) : WordRam.output c off i = μ (off + i) := by
  rw [WordRam.output, ← Nat.cast_add, h.rep]
  exact toInt_wd (hfit.inRange (h.bounded _))

end run

/-! ## Solvers -/

/-- **The compiled program solves the problem on the word RAM**, within C · T + C steps, C depending
on the compiled program only. -/
theorem solves_of_programSolves {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool} {s k r : ℕ}
    {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} (h : ProgramSolves prob P p0 dec s k dom T)
    (hr : ∀ x, (prob.params x).length ≤ r) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => (timeConst P dec : ℝ) * T x + timeConst P dec := by
  intro x hx W hadm
  obtain ⟨lim, σ', c, h⟩ := h x hx
  have hfit := fits_of_small P dec h.small hadm (hr x) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct h.run hfit (input_loadWords W h.small.nonneg h.input_fits)
  refine ⟨_, _, cfg, ramSteps_le_of_le P dec h.time, hrun, ?_⟩
  rw [show output cfg (prob.input x).length = fun i => σ'.mem ((prob.input x).length + i) from
    funext (out.holds.output hfit _)]
  exact h.answer

/-! ## The two-stage data structure -/

/-- From every memory with the property DS, procedure pQ, called on I and J, returns the entry
(I, J) of the product within T steps and leaves a memory with the property DS. -/
def AnswersQueries (lim : Limits) (P : Program) (pQ : ℕ) (x : ThinPair) (T : ℝ)
    (DS : (ℕ → ℤ) → Prop) : Prop :=
  ∀ μ, DS μ → ∀ I J : Fin x.N, ∃ (σ' : State) (c : ℕ),
    Exec lim P 0 (mainStmt pQ) ⟨frame [0, (I : ℕ), (J : ℕ)], μ⟩ σ' c ∧ (c : ℝ) ≤ T ∧
    σ'.loc 0 = (x.X * x.Y) I J ∧ DS σ'.mem

/-- Queries are answered if the procedure meets the corresponding specification. -/
theorem AnswersQueries.of_meets {lim : Limits} {P : Program} {pQ : ℕ} {x : ThinPair} {T : ℝ}
    {DS : (ℕ → ℤ) → Prop} {T' : ℕ} (hd : 0 < lim.depth) (hT : ((T' + 4 : ℕ) : ℝ) ≤ T)
    (h : ∀ μ, DS μ → ∀ I J : Fin x.N, Meets lim P pQ 1 [((I : ℕ) : ℤ), ((J : ℕ) : ℤ)] μ T'
      fun r μ' => r = (x.X * x.Y) I J ∧ DS μ') :
    AnswersQueries lim P pQ x T DS :=
  fun μ hμ I J => (h μ hμ I J).main hd hT

/-- What is asked of the two procedures on the instance x, with the limits lim and the property DS
of memories, "holds the data structure for X and Y". -/
structure ProgramIsDataStructureAt (P : Program) (pPre pQ : ℕ) (s k : ℕ) (extra : List ℤ)
    (x : ThinPair) (Tp Sp Tq : ℝ) (lim : Limits) (DS : (ℕ → ℤ) → Prop) : Prop where
  /-- The limits are polynomial in N and D. -/
  small : Small s k [x.N, x.D] lim
  /-- The indices of rows and columns fit in a word. -/
  index_fits : (x.N : ℤ) ≤ lim.word
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ x.input extra, |v| ≤ lim.word
  time_nonneg : 0 ≤ Tq
  /-- The space bounds the addresses after the input. -/
  space : (lim.space : ℝ) ≤ (x.input extra).length + Sp
  /-- The space bounds the nesting of calls. -/
  depth : (lim.depth : ℝ) ≤ Sp
  /-- The preprocessing, on the memory that holds the input, establishes DS. -/
  pre : ∃ (σ' : State) (c : ℕ),
    Exec lim P 0 (mainStmt pPre) ⟨frame [0, 0, 0], memOf (x.input extra)⟩ σ' c ∧
    (c : ℝ) ≤ Tp ∧ DS σ'.mem
  /-- Every query needs and keeps DS. -/
  query : AnswersQueries lim P pQ x Tq DS

/-- **A light program is a data structure for the entries of a thin matrix product.**  Procedure
pPre of P is the preprocessing, procedure pQ the query, with arguments I and J and the entry as its
result. -/
def ProgramIsDataStructure (P : Program) (pPre pQ : ℕ) (s k : ℕ) (extra : List ℤ)
    (dom : ThinPair → Prop) (Tp Sp Tq : ThinPair → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : Limits) (DS : (ℕ → ℤ) → Prop),
    ProgramIsDataStructureAt P pPre pQ s k extra x (Tp x) (Sp x) (Tq x) lim DS

/-- Writing a query into the cells of the two arguments does not touch the cells 0, 1, 2, …. -/
private theorem Compiler.Holds.withQuery {W : ℕ} {lim : Limits} {μ : ℕ → ℤ} {c : ℤ → BitVec W}
    (h : Holds W lim μ c) {I J : ℕ} (hI : (I : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word) :
    Input lim μ I J (withQuery c cARG1 cARG2 I J) where
  rep a := by
    simp only [WordRam.withQuery, cARG1, cARG2, show (a : ℤ) ≠ -1 by omega,
      show (a : ℤ) ≠ -2 by omega, if_false]
    exact h.rep a
  bounded := h.bounded
  arg1 := by simp [WordRam.withQuery, cARG1]
  arg2 := by simp [WordRam.withQuery, cARG1, cARG2]
  arg1_le := by rwa [abs_of_nonneg (by positivity)]
  arg2_le := by rwa [abs_of_nonneg (by positivity)]

/-- **The queries.**  From a memory that holds the data structure, the compiled query procedure
serves every list of queries: each query is one run, and leaves a memory that holds the data
structure. -/
private theorem serves_of_program {W : ℕ} {lim : Limits} {P : Program} {pQ : ℕ} {x : ThinPair}
    {DS : (ℕ → ℤ) → Prop} {T : ℝ} (hfit : Fits W lim (dispPos P false) (stackCells P lim))
    (hN : (x.N : ℤ) ≤ lim.word) (hq : AnswersQueries lim P pQ x T DS) :
    ∀ (qs : List (ℕ × ℕ)) (c : ℤ → BitVec W) (μ : ℕ → ℤ), DS μ → Holds W lim μ c →
      (∀ q ∈ qs, q.1 < x.N ∧ q.2 < x.N) →
      Serves (compileProgram P pQ false) cARG1 cARG2 cRESULT (ramSteps P false ⌊T⌋₊)
        (fun I J => if h : I < x.N ∧ J < x.N then (x.X * x.Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0) c qs
  | [], _, _, _, _, _ => trivial
  | q :: rest, c, μ, hDS, hc, hqs => by
    obtain ⟨hI, hJ⟩ := hqs q (by simp)
    obtain ⟨σ', n, hex, hn, hval, hDS'⟩ := hq μ hDS ⟨q.1, hI⟩ ⟨q.2, hJ⟩
    obtain ⟨c', hrun, out⟩ := compileProgram_correct (dec := false) hex hfit
      (hc.withQuery (by omega) (by omega))
    refine ⟨c', exec_mono (c := ⟨0, _⟩) hrun (ramSteps_mono P false (Nat.le_floor hn)), ?_,
      serves_of_program hfit hN hq rest c' σ'.mem hDS' out.holds
        fun q' hq' => hqs q' (by simp [hq'])⟩
    rw [out.result, hval]
    simp only [hI, hJ, and_self, dite_true]

/-- **The two compiled programs are a data structure on the word RAM**: queries are put into the
cells -1 and -2 (`cARG1`, `cARG2`) and answered in the cell -3 (`cRESULT`). -/
theorem isDataStructure_of_program {P : Program} {pPre pQ s k : ℕ} {extra : List ℤ}
    {dom : ThinPair → Prop} {Tp Sp Tq : ThinPair → ℝ}
    (h : ProgramIsDataStructure P pPre pQ s k extra dom Tp Sp Tq) :
    IsDataStructure (compileProgram P pPre false) (compileProgram P pQ false) cARG1 cARG2 cRESULT
      (slopeOf P false s k 2) extra dom
      (fun x => (timeConst P false : ℝ) * Tp x + timeConst P false)
      (fun x => (timeConst P false : ℝ) * Sp x + timeConst P false)
      (fun x => (timeConst P false : ℝ) * Tq x + timeConst P false) := by
  intro x hx W hadm
  obtain ⟨lim, DS, h⟩ := h x hx
  obtain ⟨σ₁, c₁, hex₁, hc₁, hDS₁⟩ := h.pre
  have hfit := fits_of_small P false h.small hadm (by simp) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct hex₁ hfit (input_loadWords W h.small.nonneg h.input_fits)
  exact ⟨_, _, cfg, ramSteps_le_of_le P false hc₁,
    ramSteps_le_of_le P false (Nat.floor_le h.time_nonneg), hrun,
    fun a ha => out.far a (far_of_space h.space h.depth ha),
    fun qs hqs => serves_of_program hfit h.index_fits h.query qs cfg σ₁.mem hDS₁ out.holds hqs⟩

/-! ## Absorbing the additive constant -/

/-- C · (A · T) + C ≤ C (A + 1) · T if T ≥ 1. -/
private theorem scaled_le {C A T : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T) :
    C * (A * T) + C ≤ C * (A + 1) * T := by
  nlinarith [mul_le_mul_of_nonneg_left hT hC]

/-- The form in which the running-time theorems need it: if the light program takes at most A · T
steps and T ≥ 1 on the domain, the compiled program takes at most C · T steps, where
C = timeConst · (A + 1). -/
theorem solves_of_programSolves_scaled {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool}
    {s k r : ℕ} {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} {A : ℝ}
    (h : ProgramSolves prob P p0 dec s k dom fun x => A * T x)
    (hr : ∀ x, (prob.params x).length ≤ r) (h1 : ∀ x, dom x → 1 ≤ T x) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => ((timeConst P dec : ℝ) * (A + 1)) * T x :=
  (solves_of_programSolves h hr).mono le_rfl (fun _ hx => hx) fun x hx =>
    scaled_le (by positivity) (h1 x hx)

/-- If preprocessing, space and queries of the light program are at most A times bounds that are at
least 1 on the domain, those of the compiled programs are at most C times these bounds, where
C = timeConst · (A + 1). -/
theorem isDataStructure_of_program_scaled {P : Program} {pPre pQ s k : ℕ} {extra : List ℤ}
    {dom : ThinPair → Prop} {Tp Sp Tq : ThinPair → ℝ} {A : ℝ}
    (h : ProgramIsDataStructure P pPre pQ s k extra dom (fun x => A * Tp x) (fun x => A * Sp x)
      fun x => A * Tq x)
    (h1 : ∀ x, dom x → 1 ≤ Tp x ∧ 1 ≤ Sp x ∧ 1 ≤ Tq x) :
    IsDataStructure (compileProgram P pPre false) (compileProgram P pQ false) cARG1 cARG2 cRESULT
      (slopeOf P false s k 2) extra dom (fun x => ((timeConst P false : ℝ) * (A + 1)) * Tp x)
      (fun x => ((timeConst P false : ℝ) * (A + 1)) * Sp x)
      (fun x => ((timeConst P false : ℝ) * (A + 1)) * Tq x) :=
  (isDataStructure_of_program h).mono le_rfl (fun _ hx => hx)
    (fun x hx => scaled_le (by positivity) (h1 x hx).1)
    (fun x hx => scaled_le (by positivity) (h1 x hx).2.1)
    fun x hx => scaled_le (by positivity) (h1 x hx).2.2

end Light
