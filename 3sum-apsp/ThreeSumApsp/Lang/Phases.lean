/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.ToMachine

/-!
# Programs that receive their input in phases

`RunsPhases` says what it means that programs of the word RAM, one for each phase, run one after the
other on a memory into which the inputs of the phases are written one after the other (Corollary
40).  Here is the corresponding notion for one light program with one procedure for each phase
(`LightPhases`), and the proof that the compiled programs run in phases on the word RAM
(`runsPhases_of_light`, and `runsPhases_start` from the empty memory at an admissible word size).

For the proof that a light program runs in phases there are two tools.  `InputsAt μ off ws` says
that the list `ws` of the inputs of the phases so far lies from cell 0 on and ends before cell
`off`; it holds again after the next input has been written (`InputsAt.next`).  A fact about the
body of a procedure, or a specification that the procedure meets, gives a run of a phase
(`phase_of_ends`, `phase_of_meets`).

The invariant between two phases is `Input lim μ 0 0 c`: the memory of the machine holds the memory
of the light program, and the cells of the two arguments hold 0.  Writing the input of a phase keeps
it (`input_withInput`), and so does a run of a compiled program (`input_run`), which may start on
whatever an earlier one has left, because its start-up code sets up all it needs.

What is left to show about a concrete program is collected in the structure `PhaseRun`: a run in
phases within limits that are polynomial in n, and bounds A (n^a + 1) on the numbers of steps.
`PhaseRun.compile` turns it into a run of the compiled phases, each a constant times as long
(`within_ramSteps`).
-/

@[expose] public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam Compiler
open EndStatement (Instr exec loadWords)

/-- The memory μ with the list ws written into the cells off, off + 1, …. -/
def overwrite (μ : ℕ → ℤ) (off : ℕ) (ws : List ℤ) : ℕ → ℤ :=
  fun a => if off ≤ a ∧ a < off + ws.length then ws.getD (a - off) 0 else μ a

/-- A cell outside the list that has been written keeps its content. -/
theorem overwrite_out {μ : ℕ → ℤ} {off : ℕ} {ws : List ℤ} {a : ℕ}
    (h : a < off ∨ off + ws.length ≤ a) : overwrite μ off ws a = μ a := by
  unfold overwrite
  rw [if_neg (by omega)]

/-- A cell of the list that has been written. -/
theorem overwrite_in {μ : ℕ → ℤ} {off : ℕ} {ws : List ℤ} {i : ℕ} (h : i < ws.length) :
    overwrite μ off ws (off + i) = ws[i] := by
  unfold overwrite
  rw [if_pos (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ h]

/-- After a list has been written, it is there. -/
theorem seg_overwrite (μ : ℕ → ℤ) (off : ℕ) (ws : List ℤ) : Seg (overwrite μ off ws) off ws :=
  fun _ hi => overwrite_in hi

/-- Writing one number. -/
theorem overwrite_single (μ : ℕ → ℤ) (off : ℕ) (z : ℤ) : overwrite μ off [z] off = z := by
  simpa using overwrite_in (μ := μ) (off := off) (ws := [z]) (i := 0) (by simp)

/-! ## The inputs of the phases so far -/

/-- The list `ws`, which consists of the inputs of the phases so far, one after the other, lies from
cell 0 on, and `off` is the first cell after it. -/
structure InputsAt (μ : ℕ → ℤ) (off : ℕ) (ws : List ℤ) : Prop where
  seg : Seg μ 0 ws
  off_eq : off = ws.length

/-- The input of the first phase is written from cell 0 on. -/
theorem InputsAt.first (μ : ℕ → ℤ) (ws : List ℤ) : InputsAt (overwrite μ 0 ws) (0 + ws.length) ws :=
  ⟨seg_overwrite μ 0 ws, Nat.zero_add _⟩

/-- The input of the next phase is written after the inputs so far. -/
theorem InputsAt.next {μ : ℕ → ℤ} {off : ℕ} {ws : List ℤ} (h : InputsAt μ off ws)
    (ws' : List ℤ) : InputsAt (overwrite μ off ws') (off + ws'.length) (ws ++ ws') := by
  obtain ⟨hseg, rfl⟩ := h
  exact ⟨seg_append.2 ⟨hseg.congr fun _ hi => overwrite_out (.inl (by omega)),
    by simpa using seg_overwrite μ ws.length ws'⟩, List.length_append.symm⟩

/-- Writing the input of the next phase changes only the cells of this input. -/
theorem InputsAt.sameOutside {μ : ℕ → ℤ} {off : ℕ} {ws : List ℤ} (_ : InputsAt μ off ws)
    (ws' : List ℤ) : SameOutside μ (overwrite μ off ws') off ws'.length :=
  fun _ h => overwrite_out h

/-- A phase that changes no cell below `off` keeps the inputs. -/
theorem InputsAt.keep {μ μ' : ℕ → ℤ} {off : ℕ} {ws : List ℤ} (h : InputsAt μ off ws)
    (hs : Kept μ μ' off := by light_keep) : InputsAt μ' off ws :=
  ⟨h.seg.congr fun i hi => hs _ (by have := h.off_eq; omega), h.off_eq⟩

/-! ## From a procedure to a phase -/

/-- A phase: the outermost call of procedure p. -/
theorem phase_of_ends {lim : Limits} {P : Program} {p : ℕ} {body : Stmt} (hp : P[p]? = some body)
    (hd : 0 < lim.depth) {μ : ℕ → ℤ} {T : ℕ} {Q : (ℕ → ℤ) → Prop}
    (h : Ends lim P 1 body ⟨frame [0, 0], μ⟩ T fun σ' => Q σ'.mem) :
    ∃ (σ' : State) (c : ℕ),
      Exec lim P 0 (mainStmt p) ⟨frame [0, 0, 0], μ⟩ σ' c ∧ c ≤ T + 4 ∧ Q σ'.mem :=
  Ends.call T (by simp) hp hd h (by simp; omega)

/-- A phase: the outermost call of a procedure that meets a specification. -/
theorem phase_of_meets {lim : Limits} {P : Program} {p : ℕ} {μ : ℕ → ℤ} {T : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop} (hd : 0 < lim.depth) (h : Meets lim P p 1 [0, 0] μ T R) :
    ∃ (σ' : State) (c : ℕ),
      Exec lim P 0 (mainStmt p) ⟨frame [0, 0, 0], μ⟩ σ' c ∧ c ≤ T + 4 ∧ ∃ r, R r σ'.mem := by
  obtain ⟨body, hp, hb⟩ := h
  exact Ends.call T (by simp) hp hd (hb.mono le_rfl fun _ hR => ⟨_, hR⟩) (by simp; omega)

/-! ## Runs in phases -/

/-- The phases of the list are run one after the other, starting from the memory μ.  A phase is the
number of a procedure of P, its input, and its number of steps.  The last memory, with the address
of the first cell after the last input, satisfies good. -/
def LightPhases (lim : Limits) (P : Program) (good : (ℕ → ℤ) → ℕ → Prop) :
    (ℕ → ℤ) → ℕ → List (ℕ × List ℤ × ℕ) → Prop
  | μ, off, [] => good μ off
  | μ, off, (p, ws, c) :: rest =>
    ∃ σ' : State, Exec lim P 0 (mainStmt p) ⟨frame [0, 0, 0], overwrite μ off ws⟩ σ' c ∧
      LightPhases lim P good σ'.mem (off + ws.length) rest

variable {W : ℕ} {lim : Limits} {P : Program} {μ : ℕ → ℤ} {c : ℤ → BitVec W}

/-- Writing the input of a phase. -/
private theorem input_withInput (h : Input lim μ 0 0 c) (off : ℕ) (ws : List ℤ)
    (hws : ∀ v ∈ ws, |v| ≤ lim.word) : Input lim (overwrite μ off ws) 0 0 (withInput c off ws) := by
  have neg (a : ℤ) (ha : a < 0) : withInput c off ws a = c a := if_neg (by omega)
  refine ⟨⟨fun a => ?_, fun a => ?_⟩, (neg _ (by decide)).trans h.arg1,
    (neg _ (by decide)).trans h.arg2, h.arg1_le, h.arg2_le⟩
  · have cast : ((off : ℤ) ≤ (a : ℤ) ∧ (a : ℤ) < (off : ℤ) + (ws.length : ℤ)) ↔
        (off ≤ a ∧ a < off + ws.length) := by omega
    simp only [withInput, overwrite, cast, show ((a : ℤ) - (off : ℤ)).toNat = a - off by omega]
    split_ifs
    exacts [rfl, h.rep a]
  · unfold overwrite
    split_ifs
    exacts [AbsLe.abs_getD_le ((abs_nonneg _).trans (h.bounded 0)) hws _, h.bounded a]

/-- One phase. -/
private theorem input_run {p : ℕ} {σ' : State} {n : ℕ} (h : Input lim μ 0 0 c)
    (hex : Exec lim P 0 (mainStmt p) ⟨frame [0, 0, 0], μ⟩ σ' n)
    (hfit : Fits W lim (dispPos P false) (stackCells P lim)) :
    ∃ c' : ℤ → BitVec W,
      exec (compileProgram P p false) (ramSteps P false n) 0 c = some (true, c') ∧
      Input lim σ'.mem 0 0 c' := by
  obtain ⟨c', hrun, out⟩ := compileProgram_correct (dec := false) hex hfit h
  exact ⟨c', hrun, out.holds, out.arg1.trans h.arg1, out.arg2.trans h.arg2, h.arg1_le, h.arg2_le⟩

/-- **All phases.**  If the procedures of a light program run in phases, the compiled programs run
in phases on the word RAM, phase j within ramSteps P false cⱼ steps. -/
private theorem runsPhases_of_light (hfit : Fits W lim (dispPos P false) (stackCells P lim))
    (good : (ℕ → ℤ) → ℕ → Prop) (good' : (ℤ → BitVec W) → ℕ → Prop)
    (hgood : ∀ μ c off, Input lim μ 0 0 c → good μ off → good' c off) :
    ∀ (l : List (ℕ × List ℤ × ℕ)) (off : ℕ) (μ : ℕ → ℤ) (c : ℤ → BitVec W), Input lim μ 0 0 c →
      (∀ q ∈ l, ∀ v ∈ q.2.1, |v| ≤ lim.word) → LightPhases lim P good μ off l →
      RunsPhases good' c off
        (l.map fun q => (compileProgram P q.1 false, q.2.1, ramSteps P false q.2.2))
  | [], off, μ, c, hB, _, h => hgood μ c off hB h
  | (p, ws, n) :: rest, off, μ, c, hB, hws, ⟨σ', hex, hrest⟩ => by
    obtain ⟨c', hrun, hB'⟩ :=
      input_run (input_withInput hB off ws (hws (p, ws, n) (by simp))) hex hfit
    exact ⟨c', hrun, runsPhases_of_light hfit good good' hgood rest _ _ _ hB'
      (fun q' hq' => hws q' (by simp [hq'])) hrest⟩

/-- **From the empty memory**, at every admissible word size. -/
theorem runsPhases_start {s k r b : ℕ} {params : List ℕ} (hsm : Small s k params lim)
    (hadm : Admissible b params W) (hr : params.length ≤ r) (hb : slopeOf P false s k r ≤ b)
    (good : (ℕ → ℤ) → ℕ → Prop) (l : List (ℕ × List ℤ × ℕ))
    (hws : ∀ q ∈ l, ∀ v ∈ q.2.1, |v| ≤ lim.word) (h : LightPhases lim P good (fun _ => 0) 0 l) :
    RunsPhases (fun c off => ∃ μ, good μ off ∧ ∀ i, WordRam.output c off i = μ (off + i))
      (loadWords W []) 0
      (l.map fun q => (compileProgram P q.1 false, q.2.1, ramSteps P false q.2.2)) :=
  have hfit := fits_of_small P false hsm hadm hr hb
  runsPhases_of_light hfit good _
    (fun μ _ off hB hg => ⟨μ, hg, fun i => hB.toHolds.output hfit off i⟩) l 0 _ _
    (input_loadWords W (ws := []) hsm.nonneg (by simp)) hws h

/-! ## Compiling the phases -/

/-- `RunsPhases` still holds if the condition on the last memory is weakened. -/
theorem runsPhases_mono {W : ℕ} {good good' : (ℤ → BitVec W) → ℕ → Prop}
    (h : ∀ c off, good c off → good' c off) :
    ∀ (l : List (List Instr × List ℤ × ℕ)) (c : ℤ → BitVec W) (off : ℕ),
      RunsPhases good c off l → RunsPhases good' c off l
  | [], c, off, hr => h c off hr
  | _ :: rest, _, _, ⟨c', h1, h2⟩ => ⟨c', h1, runsPhases_mono h rest c' _ h2⟩

/-- If a phase takes c ≤ A (n^a + 1) steps of the program, the compiled phase is `Within` the same
bound, with a constant that depends on the program and on A only. -/
theorem within_ramSteps (P : Program) {c n : ℕ} {A a : ℝ} (h : (c : ℝ) ≤ A * ((n : ℝ) ^ a + 1)) :
    Within (ramSteps P false c) ((timeConst P false : ℝ) * (A + 1)) n a := by
  have hK : (0 : ℝ) ≤ (timeConst P false : ℝ) := by positivity
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) a
  unfold Within
  calc (ramSteps P false c : ℝ) ≤ (timeConst P false : ℝ) * (c : ℝ) + timeConst P false :=
      ramSteps_le P false c
    _ ≤ (timeConst P false : ℝ) * (A * ((n : ℝ) ^ a + 1))
        + (timeConst P false : ℝ) * ((n : ℝ) ^ a + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left h hK) (le_mul_of_one_le_right hK (by linarith))
    _ = (timeConst P false : ℝ) * (A + 1) * ((n : ℝ) ^ a + 1) := by ring

/-- What is left to show about a program that runs in phases, at the size `n` and for given inputs.
The list `l` has, for each phase, the number of its procedure, its input and its number of steps. -/
structure PhaseRun (lim : Limits) (P : Program) (s k : ℕ) (A : ℝ) (n : ℕ) (sizes : List ℕ)
    (good : (ℕ → ℤ) → ℕ → Prop) (l : List (ℕ × List ℤ × ℕ)) (exps : List ℝ) : Prop where
  /-- The limits are polynomial in `n`. -/
  small : Small s k [n] lim
  /-- The sizes of the matrices fit in a word. -/
  sizes_le : ∀ m ∈ sizes, (m : ℤ) ≤ lim.word
  /-- The phase with the exponent `a` takes at most `A (n^a + 1)` steps. -/
  steps : List.Forall₂ (fun q a => Within q.2.2 A n a) l exps
  /-- The procedures run the phases within the limits, from the empty memory, and the memory is as
  it should be at the end. -/
  run : LightPhases lim P good (fun _ => 0) 0 l

/-- **The compiled phases.**  If every number of the inputs fits in a word, the compiled procedures
run the phases on the word RAM at every admissible word size, each a constant times as long as in
the program, and the output cells hold what the last memory of the program holds. -/
theorem PhaseRun.compile {lim : Limits} {P : Program} {s k : ℕ} {A : ℝ} {n : ℕ} {sizes : List ℕ}
    {good : (ℕ → ℤ) → ℕ → Prop} {l : List (ℕ × List ℤ × ℕ)} {exps : List ℝ} {bits : ℕ}
    (h : PhaseRun lim P s k A n sizes good l exps)
    (hadm : Admissible (slopeOf P false s k 1) [n] bits) (hws : ∀ q ∈ l, AbsLe q.2.1 lim.word)
    {good' : (ℤ → BitVec bits) → ℕ → Prop}
    (hgood : ∀ c off μ, good μ off → (∀ i, output c off i = μ (off + i)) → good' c off) :
    List.Forall₂
        (fun q a => Within (ramSteps P false q.2.2) ((timeConst P false : ℝ) * (A + 1)) n a)
        l exps ∧
      RunsPhases good' (loadWords bits []) 0
        (l.map fun q => (compileProgram P q.1 false, q.2.1, ramSteps P false q.2.2)) :=
  ⟨h.steps.imp fun _ _ hq => within_ramSteps P hq,
    runsPhases_mono (fun c off ⟨μ, hg, ho⟩ => hgood c off μ hg ho) _ _ _
      (runsPhases_start (r := 1) h.small hadm (by simp) le_rfl _ _ hws h.run)⟩

end Light
