/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
import ToTuring.Machine.Host

/-! # The host machine for a stepped computation whose result is a word

`exists_tmW`: a stepped computation on bit strings whose result is a list of bits, and whose init,
step and out are polynomial-time, runs on one of
Mathlib's multi-stack machines, with one constant q: a run of T steps on the input x with all states
of size at most S costs the machine at most
q·(T+1)·(|x|+S+1)^q steps, and the machine halts with the result on its output stack, first bit on
top. The machine and q are chosen before x, T and S.

The machine is that of `Groundwork.exists_tm` (proof/machines/ToTuring/Machine/Host.lean), whose
result is one bit, except that the loop stops at a result `some w` (`chkW`) and an
epilogue moves w onto the output stack. On the main stack a value is written as a word of bits and
brackets (proof/machines/ToTuring/Enc.lean). The epilogue takes the word of w apart:
each bit goes to stack a (`unpack`), comes back from there and is pushed on the output stack
(`emit`); the brackets are removed on the way, the last three by `pop3`. The two passes leave
the first bit of w on top. This takes 4|w| + 3 steps (`epilogue_within`). `stHostW` restates
`exists_tmW` as the interface statement `StHostW` of
`proof/consequences/CountKSat/Interfaces.lean`.

The proofs of `mainLoop_within` and `exists_tmW` follow `mainLoop_within` and `exists_tm` of
proof/machines/ToTuring/Machine/Host.lean. The bound
q·(T+1)·(|x|+S+1)^q has the size S of the states as a free parameter, where `exists_tm` asks S ≤
(|x|+2)^d. -/

namespace CountKSat.HostW

open Groundwork Groundwork.TM Groundwork.Host Turing

/-! ### The head of the loop and the epilogue -/

/-- The head of the loop: at `none` remove its word and go on with the body; at `some w` remove the
opening bracket only and leave the loop. -/
def chkW : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .main) (fun _ _ => none) <| .peek (some .main) (fun _ o => o) <|
    .branch (fun s => s == some .R)
      (.pop (some .main) (fun _ _ => none) <| .goto fun _ => ())
      (.load (fun _ => none) .halt)

/-- One round: take the first bit off the word of a list of bits and put it on stack a; its closing
bracket stays. At the empty list, remove its word and stop. -/
def unpackQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ o => o) <|
    .branch (fun s => s == some .R)
      (.load (fun _ => none) .halt)
      (.push (some .a) (fun s => s.getD .L) <| .load (fun _ => none) <| .goto fun _ => ())

/-- The first loop of the epilogue. -/
def unpack : FrIO := Frag.loop unpackQ skip

/-- One round: a bit comes back from stack a and is pushed on the stack of bits, and one closing
bracket is removed. When stack a is empty, stop. -/
def emitQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .a) (fun _ o => o) <|
    .branch (fun s => s.isSome)
      (.push none bitOf <| .pop (some .main) (fun _ _ => none) <| .goto fun _ => ())
      .halt

/-- The second loop of the epilogue. -/
def emit : FrIO := Frag.loop emitQ skip

section
variable (W : List Bool) (M A B N : List Sym)

theorem chkW_none : TM2.stepAux chkW none (withIO W (st (wd (none : Option (List Bool)) ++ M) A B N)) =
    ⟨some (), none, withIO W (st M A B N)⟩ := by
  simp [chkW, TM2.stepAux, wd_none]

theorem chkW_some (w : List Bool) : TM2.stepAux chkW none (withIO W (st (wd (some w) ++ M) A B N)) =
    ⟨none, none, withIO W (st (wd w ++ (.L :: .R :: .R :: M)) A B N)⟩ := by
  cases w <;> simp [chkW, TM2.stepAux, wd_some, wd_nil, wd_cons]

theorem unpackQ_nil : TM2.stepAux unpackQ none (withIO W (st (wd ([] : List Bool) ++ M) A B N)) =
    ⟨none, none, withIO W (st M A B N)⟩ := by
  simp [unpackQ, TM2.stepAux, wd_nil]

theorem unpackQ_cons (b : Bool) (l : List Bool) : TM2.stepAux unpackQ none (withIO W (st (wd (b :: l) ++ M) A B N)) =
    ⟨some (), none, withIO W (st (wd l ++ (.R :: M)) (.bit b :: A) B N)⟩ := by
  simp [unpackQ, TM2.stepAux, wd_cons, wd_bool]

theorem emitQ_nil : TM2.stepAux emitQ none (withIO W (st M [] B N)) = ⟨none, none, withIO W (st M [] B N)⟩ := by
  simp [emitQ, TM2.stepAux]

theorem emitQ_cons (b : Bool) : TM2.stepAux emitQ none (withIO W (st (.R :: M) (.bit b :: A) B N)) =
    ⟨some (), none, withIO (b :: W) (st M A B N)⟩ := by
  simp [emitQ, TM2.stepAux, bitOf]

end

theorem unpack_runs (W : List Bool) (B N : List Sym) : ∀ (w : List Bool) (M A : List Sym),
    unpack.Runs none (withIO W (st (wd w ++ M) A B N)) (2 * w.length + 1)
      (withIO W (st (List.replicate w.length .R ++ M) ((w.map Sym.bit).reverse ++ A) B N))
  | [], M, A => Frag.loop_runs_exit (unpackQ_nil W M A B N)
  | b :: w, M, A => by
    have h := Frag.loop_runs_iter (unpackQ_cons W M A B N b w) (skip_runs _) (unpack_runs W B N w (.R :: M) (.bit b :: A))
    have e1 : List.replicate w.length Sym.R ++ Sym.R :: M = List.replicate (b :: w).length Sym.R ++ M := by
      simp [List.replicate_succ']
    have e2 : (w.map Sym.bit).reverse ++ Sym.bit b :: A = ((b :: w).map Sym.bit).reverse ++ A := by simp
    have e3 : 1 + 1 + (2 * w.length + 1) = 2 * (b :: w).length + 1 := by simp only [List.length_cons]; omega
    rw [e1, e2, e3] at h
    exact h

theorem emit_runs (M B N : List Sym) : ∀ (l W : List Bool),
    emit.Runs none (withIO W (st (List.replicate l.length .R ++ M) (l.map Sym.bit) B N)) (2 * l.length + 1)
      (withIO (l.reverse ++ W) (st M [] B N))
  | [], W => Frag.loop_runs_exit (emitQ_nil W M B N)
  | b :: l, W => by
    have h := Frag.loop_runs_iter (emitQ_cons W (List.replicate l.length Sym.R ++ M) (l.map Sym.bit) B N b) (skip_runs _)
      (emit_runs M B N l (b :: W))
    have e1 : Sym.R :: (List.replicate l.length Sym.R ++ M) = List.replicate (b :: l).length Sym.R ++ M := by
      simp [List.replicate_succ]
    have e4 : Sym.bit b :: l.map Sym.bit = (b :: l).map Sym.bit := rfl
    have e2 : l.reverse ++ b :: W = (b :: l).reverse ++ W := by simp
    have e3 : 1 + 1 + (2 * l.length + 1) = 2 * (b :: l).length + 1 := by simp only [List.length_cons]; omega
    rw [e1, e4, e2, e3] at h
    exact h

/-- Remove the three symbols that are left of the word of `some w`. -/
def pop3 : FrIO := Frag.ofStmt (.pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ _ => none) <|
  .pop (some .main) (fun _ _ => none) .halt)

theorem pop3_runs (W : List Bool) (M A B N : List Sym) :
    pop3.Runs none (withIO W (st (.L :: .R :: .R :: M) A B N)) 1 (withIO W (st M A B N)) :=
  Frag.ofStmt_runs (by simp [TM2.stepAux])

/-- The epilogue: the bits of w move from the main stack to the empty stack of bits, first bit on
top; the three symbols below them are removed. -/
def epilogue : FrIO := (unpack.seq emit).seq pop3

theorem epilogue_within (w : List Bool) (M B N : List Sym) :
    Frag.Within epilogue (withIO [] (st (wd w ++ (.L :: .R :: .R :: M)) [] B N)) (4 * w.length + 3) (withIO w (st M [] B N)) := by
  have h1 : Frag.Within unpack _ _ _ := ⟨_, le_rfl, unpack_runs [] B N w (.L :: .R :: .R :: M) []⟩
  have h2 : Frag.Within emit _ _ _ := ⟨_, le_rfl, emit_runs (.L :: .R :: .R :: M) B N w.reverse []⟩
  have h3 : Frag.Within pop3 _ _ _ := ⟨_, le_rfl, pop3_runs w M [] B N⟩
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse, List.append_nil] at h1 h2
  exact ((h1.seq h2).seq h3).mono (by omega)

/-! ### The loop -/

section machine

variable {M : Stepped (List Bool) (List Bool)}

theorem size_le_of_reaches {S t : ℕ} {w : List Bool} {s : M.σ} (h : M.Reaches S w s t) : size s ≤ S := by
  cases h with
  | halt _ hs => exact hs
  | step _ hs _ => exact hs

variable [Enc M.σ]

/-- The loop. At its head the word of the output of the state lies on the word of the state. -/
def mainLoop (Ps Po : Fr) : FrIO := Frag.loop chkW (body Ps Po)

variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))

include hO in
theorem look_within (s : M.σ) (M' A B N : List Sym) : (look Po).Within (st (wd s ++ M') A B N)
    (3 * len s + 3 + tO (len s)) (st (wd (M.out s) ++ (wd s ++ M')) A B N) :=
  (dupF_within (Enc.toV s) M' A B N).seq (hO s _ A B N)

include hS hO in
/-- The loop, from a state that reaches the result w within t steps: at most t rounds. The last
state s' is left on the main stack, and on it what
the head leaves of the word of its output `some w`. -/
theorem mainLoop_within (mS : Monotone tS) (mO : Monotone tO) {S L : ℕ} (hL : ∀ s : M.σ, size s ≤ S → len s ≤ L) {w : List Bool}
    {s : M.σ} {t : ℕ} (h : M.Reaches S w s t) :
    ∃ s' : M.σ, size s' ≤ S ∧ M.out s' = some w ∧
      Frag.Within (mainLoop Ps Po) (withIO [] (st (wd (M.out s) ++ (wd s ++ [])) [] [] []))
        (t * (1 + (tS L + (3 * L + 3 + tO L))) + 1) (withIO [] (st (wd w ++ (.L :: .R :: .R :: (wd s' ++ []))) [] [] [])) := by
  induction h with
  | @halt s t ho hs =>
    refine ⟨s, hs, ho, 1, by omega, ?_⟩
    rw [ho]
    exact Frag.loop_runs_exit (chkW_some _ _ _ _ _ w)
  | @step s t ho hs hr ih =>
    obtain ⟨s', hs', ho', n, hn, hrun⟩ := ih
    obtain ⟨m, hm, hb⟩ := within_io ((hS s [] [] [] []).seq (look_within hO (M.step s) [] [] [] [])) []
    refine ⟨s', hs', ho', 1 + m + n, ?_, ?_⟩
    · have h1 := mS (hL s hs)
      have h2 := hL _ (size_le_of_reaches hr)
      have h3 := mO h2
      have e : (t + 1) * (1 + (tS L + (3 * L + 3 + tO L))) =
          t * (1 + (tS L + (3 * L + 3 + tO L))) + (1 + (tS L + (3 * L + 3 + tO L))) := Nat.succ_mul _ _
      omega
    · rw [ho]
      exact Frag.loop_runs_iter (chkW_none _ _ _ _ _) hb hrun

end machine

/-! ### The machine -/

/-- The whole program: prologue, init and the first output, the loop, the epilogue, and the last
state dropped. -/
def prog (Pi Ps Po : Fr) : FrIO :=
  (((prologue.seq (Pi.seq (look Po)).io).seq (mainLoop Ps Po)).seq epilogue).seq dropF.io

end CountKSat.HostW

namespace CountKSat

open Groundwork Groundwork.TM Groundwork.Host Turing HostW

/-- A stepped computation `M` on bit strings whose result is a list of bits, with polynomial-time
init, step and out, runs on one of Mathlib's
multi-stack machines `N` with finite alphabets. There is one number `q` such that, whenever `M` ends
on `x` with the result `w` within `T` steps and with
all states of size at most `S`, the machine `N` started on `x` halts with output `w` within q · (T + 1)
· (|x| + S + 1)^q steps. -/
public theorem exists_tmW (M : Stepped (List Bool) (List Bool)) [IsPolyT M] :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (w : List Bool), M.Runs x T S w →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (w.map N.outputAlphabet.invFun))
          (q * (T + 1) * (x.length + S + 1) ^ q)) := by
  obtain ⟨Pi, tI, pI, mI, hI, -⟩ := (IsPolyT.init (M := M)).elim
  obtain ⟨Ps, tS, pS, mS, hS, -⟩ := (IsPolyT.step (M := M)).elim
  obtain ⟨Po, tO, pO, mO, hO, lO⟩ := (IsPolyT.out (M := M)).elim
  have pL : PB fun m => 7 * m := (PB.const 7).mul PB.id'
  have pO' : PB fun m => tO (7 * m) := pO.comp pL
  have pK : PB fun m => 3 * (7 * m) + 3 + tO (7 * m) := (((PB.const 3).mul pL).add (PB.const 3)).add pO'
  have pG : PB fun m => 1 + (tS (7 * m) + (3 * (7 * m) + 3 + tO (7 * m))) := (PB.const 1).add ((pS.comp pL).add pK)
  have pQ : PB fun m => (4 * m + 3 + (tI (3 * m + 2) + (3 * (7 * m) + 3 + tO (7 * m))) + 1 + (4 * tO (7 * m) + 3) +
      (7 * m + 1)) + (1 + (tS (7 * m) + (3 * (7 * m) + 3 + tO (7 * m)))) :=
    (((((((PB.const 4).mul PB.id').add (PB.const 3)).add
      ((pI.comp (((PB.const 3).mul PB.id').add (PB.const 2))).add pK)).add (PB.const 1)).add
      (((PB.const 4).mul pO').add (PB.const 3))).add (pL.add (PB.const 1))).add pG
  obtain ⟨q, hq⟩ := pQ
  refine ⟨⟨tmOf (HostW.prog Pi Ps Po), Equiv.refl _, Equiv.refl _⟩, q, fun k => ?_, fun x T S w hr => ?_⟩
  · rcases k with _ | k
    · exact inferInstanceAs (Finite Bool)
    · exact inferInstanceAs (Finite Sym)
  · obtain ⟨m, hm⟩ : ∃ m, m = x.length + S := ⟨_, rfl⟩
    obtain ⟨L, hLdef⟩ : ∃ L, L = 7 * m := ⟨_, rfl⟩
    have hL : ∀ s : M.σ, size s ≤ S → len s ≤ L := fun s hs => by
      have h1 := Carried.le s
      omega
    obtain ⟨s', hs', ho', h3⟩ := HostW.mainLoop_within hS hO mS mO hL hr
    have h1 := prologue_within x
    have h2 := within_io ((hI x [] [] [] []).seq (HostW.look_within hO (M.init x) [] [] [] [])) []
    have h4 := epilogue_within w (wd s' ++ []) [] []
    have h5 := within_io (dropF_within (Enc.toV s') [] [] [] []) w
    rw [List.append_nil] at h2
    have h := (((h1.seq h2).seq h3).seq h4).seq h5
    have hq' := hq m
    dsimp only at hq'
    rw [← hLdef] at hq'
    refine outputs_of_within (h.mono ?_) (List.map_id x) (List.map_id w)
    have g1 := hL _ (HostW.size_le_of_reaches hr)
    have g2 := mO g1
    have g3 : (code (Enc.toV s')).length ≤ L := hL s' hs'
    have g4 : len x = 3 * x.length + 2 := len_bools x
    have g6 : tI (3 * x.length + 2) ≤ tI (3 * m + 2) := mI (by omega)
    have g7 : w.length ≤ tO L := by
      have a1 := lO s'
      rw [ho', len_some, len_bools] at a1
      have a2 := mO (hL s' hs')
      omega
    rw [g4]
    obtain ⟨G, hG⟩ : ∃ G, G = 1 + (tS L + (3 * L + 3 + tO L)) := ⟨_, rfl⟩
    rw [← hG] at hq' ⊢
    rw [← hm]
    obtain ⟨Y, hY⟩ : ∃ Y, Y = q * (m + 1) ^ q := ⟨_, rfl⟩
    have e : q * (T + 1) * (m + 1) ^ q = T * Y + Y := by rw [hY]; ring
    rw [e]
    rw [← hY] at hq'
    have g5 : T * G ≤ T * Y := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The host with a word as output: the interface statement `StHostW`. -/
public theorem stHostW : StHostW := fun M _ => exists_tmW M

end CountKSat
