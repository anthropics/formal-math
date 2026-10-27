/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Machine.Lift
public import ToTuring.PolyT
public import ToTuring.EncLemmas

/-! The host: one of Mathlib's multi-stack machines that runs a stepped computation (`Stepped`)
whose init, step and out are
polynomial-time (`exists_tm`). Prologue: each bit of the input is popped off the stack of bits and
pushed on stack a, with a
closing bracket on the main stack; then ⟨⟩, the word of the empty list, is pushed on the main stack;
then the bits come back from
stack a, each followed by an opening bracket. The main stack now holds the word of the input list.
Then the fragment of init.
Then the word of the state is duplicated and the fragment of out runs on the copy. Then a loop,
whose head removes the word of
the output: at `none` it runs the fragment of step, duplicates the word of the new state, runs the
fragment of out on the copy
and starts again; at `some b` it pushes b on the stack of bits and leaves the loop. Finally the word
of the state is dropped.
Each time at the head of the loop the main stack holds the word of the output on the word of the
state, and all other stacks are
empty.

The prologue takes 4|x| + 3 steps (`prologue_within`). Each round of the loop takes one step for the
head, plus the steps of
step, plus 3·len + 3 for the copy, plus the steps of out (`mainLoop_within`). So the whole run takes
at most
c·(T + 1)·(|x| + 1)^c steps (`exists_tm`). -/

@[expose] public section

namespace Groundwork

open TM Turing

namespace Host

/-! ### Fragments on the five stacks -/

/-- Fragments of the final machine, over the four work stacks and the stack of bits. -/
abbrev FrIO := Frag Γio (Option Sym)

/-- A fragment over the work stacks keeps its bound in the final machine. -/
theorem within_io {P : Fr} {S S' : Stk → List Sym} {t : ℕ} (h : P.Within S t S') (W : List Bool) :
    P.io.Within (withIO W S) t (withIO W S') := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn, Frag.io_runs hr W⟩

@[simp] theorem withIO_none (W : List Bool) (S : Stk → List Sym) : withIO W S none = W := rfl
@[simp] theorem withIO_some (W : List Bool) (S : Stk → List Sym) (k : Stk) : withIO W S (some k) = S k := rfl

@[simp] theorem upd_none (W W' : List Bool) (S : Stk → List Sym) : Function.update (withIO W S) none W' = withIO W' S := by
  funext k; cases k <;> simp [Function.update, withIO]

/-- The fragment that does nothing, in one step. -/
def skip : FrIO := Frag.ofStmt .halt

theorem skip_runs (S : ∀ k, List (Γio k)) : skip.Runs none S 1 S := Frag.ofStmt_runs rfl

/-! ### The prologue -/

/-- Pop a bit off the stack of bits; push it on stack a, and a closing bracket on the main stack. -/
def pourQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop none (fun _ o => o.map Sym.bit) <|
    .branch (fun s => s.isSome)
      (.push (some .a) (fun s => s.getD .L) <| .push (some .main) (fun _ => .R) <| .load (fun _ => none) <|
        .goto fun _ => ())
      .halt

/-- The first loop of the prologue. -/
def pour : FrIO := Frag.loop pourQ skip

/-- Pop a symbol off stack a; push it, and then an opening bracket, on the main stack. -/
def buildQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .a) (fun _ o => o) <|
    .branch (fun s => s.isSome)
      (.push (some .main) (fun s => s.getD .L) <| .push (some .main) (fun _ => .L) <| .load (fun _ => none) <|
        .goto fun _ => ())
      .halt

/-- The second loop of the prologue. -/
def build : FrIO := Frag.loop buildQ skip

section
variable (W : List Bool) (M A B N : List Sym)

theorem pourQ_nil : TM2.stepAux pourQ none (withIO [] (st M A B N)) = ⟨none, none, withIO [] (st M A B N)⟩ := by
  simp [pourQ, TM2.stepAux]

theorem pourQ_cons (b : Bool) : TM2.stepAux pourQ none (withIO (b :: W) (st M A B N)) =
    ⟨some (), none, withIO W (st (.R :: M) (.bit b :: A) B N)⟩ := by
  simp [pourQ, TM2.stepAux]

theorem buildQ_nil : TM2.stepAux buildQ none (withIO W (st M [] B N)) = ⟨none, none, withIO W (st M [] B N)⟩ := by
  simp [buildQ, TM2.stepAux]

theorem buildQ_cons (s : Sym) : TM2.stepAux buildQ none (withIO W (st M (s :: A) B N)) =
    ⟨some (), none, withIO W (st (.L :: s :: M) A B N)⟩ := by
  simp [buildQ, TM2.stepAux]

end

theorem pour_runs (B N : List Sym) : ∀ (x : List Bool) (M A : List Sym),
    pour.Runs none (withIO x (st M A B N)) (2 * x.length + 1)
      (withIO [] (st (List.replicate x.length .R ++ M) ((x.map Sym.bit).reverse ++ A) B N))
  | [], M, A => Frag.loop_runs_exit (pourQ_nil M A B N)
  | b :: x, M, A => by
    have h := Frag.loop_runs_iter (pourQ_cons x M A B N b) (skip_runs _) (pour_runs B N x (.R :: M) (.bit b :: A))
    have e1 : List.replicate x.length Sym.R ++ Sym.R :: M = List.replicate (b :: x).length Sym.R ++ M := by
      simp [List.replicate_succ']
    have e2 : (x.map Sym.bit).reverse ++ Sym.bit b :: A = ((b :: x).map Sym.bit).reverse ++ A := by simp
    have e3 : 1 + 1 + (2 * x.length + 1) = 2 * (b :: x).length + 1 := by simp only [List.length_cons]; omega
    rw [e1, e2, e3] at h
    exact h

theorem build_runs (W : List Bool) (B N : List Sym) : ∀ (l suf : List Bool),
    build.Runs none (withIO W (st (wd suf ++ List.replicate l.length .R) (l.map Sym.bit) B N)) (2 * l.length + 1)
      (withIO W (st (wd (l.reverse ++ suf)) [] B N))
  | [], suf => by
    have h : build.Runs none _ 1 _ := Frag.loop_runs_exit (buildQ_nil W (wd suf) B N)
    simpa using h
  | b :: l, suf => by
    have h := Frag.loop_runs_iter (buildQ_cons W (wd suf ++ List.replicate (b :: l).length .R) (l.map Sym.bit) B N (.bit b))
      (skip_runs _)
      (by
        have := build_runs W B N l (b :: suf)
        have e : wd (b :: suf) ++ List.replicate l.length Sym.R =
            Sym.L :: Sym.bit b :: (wd suf ++ List.replicate (b :: l).length Sym.R) := by
          simp [wd_cons, wd_bool, List.replicate_succ]
        rw [e] at this
        exact this)
    have e2 : l.reverse ++ b :: suf = (b :: l).reverse ++ suf := by simp
    have e3 : 1 + 1 + (2 * l.length + 1) = 2 * (b :: l).length + 1 := by simp only [List.length_cons]; omega
    rw [e2, e3] at h
    exact h

/-- The prologue: from the bits of the input to the word of the list of these bits. -/
def prologue : FrIO := (pour.seq (pushW [.L, .R]).io).seq build

theorem prologue_within (x : List Bool) :
    Frag.Within prologue (withIO x (st [] [] [] [])) (4 * x.length + 3) (withIO [] (st (wd x) [] [] [])) := by
  have h1 : Frag.Within pour _ _ _ := ⟨_, le_rfl, pour_runs [] [] x [] []⟩
  have h2 := within_io (pushW_within (List.replicate x.length .R ++ []) ((x.map Sym.bit).reverse ++ []) [] [] [.L, .R]) []
  have h3 : Frag.Within build _ _ _ := ⟨_, le_rfl, build_runs [] [] [] x.reverse []⟩
  have e : st ([Sym.L, Sym.R] ++ (List.replicate x.length Sym.R ++ [])) ((x.map Sym.bit).reverse ++ []) [] [] =
      st (wd ([] : List Bool) ++ List.replicate x.reverse.length Sym.R) (x.reverse.map Sym.bit) [] [] := by
    simp [wd_nil]
  rw [e] at h2
  have h := (h1.seq h2).seq h3
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h
  exact h.mono (by omega)

/-! ### The loop -/

/-- The bit held in the local state, false if it holds none. Used on the second symbol of the word
of `some b`. -/
def bitOf : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

/-- The head of the loop looks at the word of an optional bit on top of the main stack and removes
it. At `none` it goes on
with the body; at `some b` it pushes b on the stack of bits and leaves the loop. -/
def chkQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ o => o) <|
    .branch (fun s => s == some .R)
      (.load (fun _ => none) <| .goto fun _ => ())
      (.push none bitOf <| .pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ _ => none) <|
        .pop (some .main) (fun _ _ => none) .halt)

section
variable (W : List Bool) (M A B N : List Sym)

theorem chkQ_none : TM2.stepAux chkQ none (withIO W (st (wd (none : Option Bool) ++ M) A B N)) =
    ⟨some (), none, withIO W (st M A B N)⟩ := by
  simp [chkQ, TM2.stepAux, wd_none]

theorem chkQ_some (b : Bool) : TM2.stepAux chkQ none (withIO W (st (wd (some b) ++ M) A B N)) =
    ⟨none, none, withIO (b :: W) (st M A B N)⟩ := by
  simp [chkQ, TM2.stepAux, wd_some, wd_bool, bitOf]

end

section machine

variable {M : Stepped (List Bool) Bool}

theorem size_le_of_reaches {S t : ℕ} {b : Bool} {s : M.σ} (h : M.Reaches S b s t) : size s ≤ S := by
  cases h with
  | halt _ hs => exact hs
  | step _ hs _ => exact hs

variable [Enc M.σ]

/-- Duplicate the word of the state and turn the copy on top into the word of its output. -/
def look (Po : Fr) : Fr := dupF.seq Po

/-- The body of the loop: one step of the computation, then the output of the new state. -/
def body (Ps Po : Fr) : FrIO := (Ps.seq (look Po)).io

/-- The loop. At its head the word of the output of the state lies on the word of the state. -/
def mainLoop (Ps Po : Fr) : FrIO := Frag.loop chkQ (body Ps Po)

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
/-- The loop, from a state that reaches the result b within t steps: at most t rounds, and the last
state is left on the
main stack. -/
theorem mainLoop_within (mS : Monotone tS) (mO : Monotone tO) {S L : ℕ} (hL : ∀ s : M.σ, size s ≤ S → len s ≤ L) {b : Bool}
    {s : M.σ} {t : ℕ} (h : M.Reaches S b s t) :
    ∃ s' : M.σ, size s' ≤ S ∧ Frag.Within (mainLoop Ps Po) (withIO [] (st (wd (M.out s) ++ (wd s ++ [])) [] [] []))
      (t * (1 + (tS L + (3 * L + 3 + tO L))) + 1) (withIO [b] (st (wd s' ++ []) [] [] [])) := by
  induction h with
  | @halt s t ho hs =>
    refine ⟨s, hs, 1, by omega, ?_⟩
    rw [ho]
    exact Frag.loop_runs_exit (chkQ_some _ _ _ _ _ b)
  | @step s t ho hs hr ih =>
    obtain ⟨s', hs', n, hn, hrun⟩ := ih
    obtain ⟨m, hm, hb⟩ := within_io ((hS s [] [] [] []).seq (look_within hO (M.step s) [] [] [] [])) []
    refine ⟨s', hs', 1 + m + n, ?_, ?_⟩
    · have h1 := mS (hL s hs)
      have h2 := hL _ (size_le_of_reaches hr)
      have h3 := mO h2
      have e : (t + 1) * (1 + (tS L + (3 * L + 3 + tO L))) =
          t * (1 + (tS L + (3 * L + 3 + tO L))) + (1 + (tS L + (3 * L + 3 + tO L))) := Nat.succ_mul _ _
      omega
    · rw [ho]
      exact Frag.loop_runs_iter (chkQ_none _ _ _ _ _) hb hrun

end machine

/-! ### The machine -/

/-- The whole program: prologue, init and the first output, the loop, and the last state dropped. -/
def prog (Pi Ps Po : Fr) : FrIO := ((prologue.seq (Pi.seq (look Po)).io).seq (mainLoop Ps Po)).seq dropF.io

/-- A fragment on the five stacks as one of Mathlib's bundled machines; input and output on the
stack of bits. -/
def tmOf (H : FrIO) : FinTM2 where
  K := Option Stk
  k₀ := none
  k₁ := none
  Γ := Γio
  Λ := H.Λ
  main := H.entry
  σ := Option Sym
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := H.m

theorem initList_tmOf (H : FrIO) (x : List Bool) :
    @Eq (TM2.Cfg Γio H.Λ (Option Sym)) (initList (tmOf H) x) ⟨some H.entry, none, withIO x (st [] [] [] [])⟩ := by
  unfold initList
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

theorem haltList_tmOf (H : FrIO) (x : List Bool) :
    @Eq (TM2.Cfg Γio H.Λ (Option Sym)) (haltList (tmOf H) x) ⟨none, none, withIO x (st [] [] [] [])⟩ := by
  unfold haltList
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

/-- A run of the fragment is a run of the bundled machine, in Mathlib's terms. -/
theorem outputs_of_within {H : FrIO} {x y : List Bool} {t : ℕ}
    (h : Frag.Within H (withIO x (st [] [] [] [])) t (withIO y (st [] [] [] []))) {x' y' : List Bool} (hx : x' = x)
    (hy : y' = y) : Nonempty (TM2OutputsInTime (tmOf H) x' (some y') t) := by
  subst hx hy
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨⟨⟨n, ?_⟩, hn⟩⟩
  have e := hr.iterate
  rw [← initList_tmOf H x', ← haltList_tmOf H y'] at e
  exact e

end Host

open Host in
/-- A stepped computation on bit strings with polynomial-time init, step and out runs on one of
Mathlib's multi-stack
machines with finite alphabets. If it ends on x within T steps with states of size at most (|x| + 2)^d,
the machine takes
at most c · (T + 1) · (|x| + 1)^c steps, where c depends on the computation and d only. -/
theorem exists_tm (M : Stepped (List Bool) Bool) [IsPolyT M] (d : ℕ) :
    ∃ (N : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (b : Bool), M.Runs x T S b → S ≤ (x.length + 2) ^ d →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some ([b].map N.outputAlphabet.invFun))
          (c * (T + 1) * (x.length + 1) ^ c)) := by
  obtain ⟨Pi, tI, pI, -, hI, -⟩ := (IsPolyT.init (M := M)).elim
  obtain ⟨Ps, tS, pS, mS, hS, -⟩ := (IsPolyT.step (M := M)).elim
  obtain ⟨Po, tO, pO, mO, hO, -⟩ := (IsPolyT.out (M := M)).elim
  have pL : PB fun n => 7 * (n + 2) ^ d := (PB.const 7).mul ((PB.id'.add (PB.const 2)).pow d)
  have pK : PB fun n => 3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d) :=
    (((PB.const 3).mul pL).add (PB.const 3)).add (pO.comp pL)
  have pG : PB fun n => 1 + (tS (7 * (n + 2) ^ d) + (3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d))) :=
    (PB.const 1).add ((pS.comp pL).add pK)
  have pQ : PB fun n => (4 * n + 3 + (tI (3 * n + 2) + (3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d))) + 1 +
      (7 * (n + 2) ^ d + 1)) + (1 + (tS (7 * (n + 2) ^ d) + (3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d)))) :=
    ((((((PB.const 4).mul PB.id').add (PB.const 3)).add
      ((pI.comp (((PB.const 3).mul PB.id').add (PB.const 2))).add pK)).add (PB.const 1)).add
      (pL.add (PB.const 1))).add pG
  obtain ⟨c, hc⟩ := pQ
  refine ⟨⟨tmOf (prog Pi Ps Po), Equiv.refl _, Equiv.refl _⟩, c, fun k => ?_, fun x T S b hr hSd => ?_⟩
  · rcases k with _ | k
    · exact inferInstanceAs (Finite Bool)
    · exact inferInstanceAs (Finite Sym)
  · obtain ⟨L, hLdef⟩ : ∃ L, L = 7 * (x.length + 2) ^ d := ⟨_, rfl⟩
    have hL : ∀ s : M.σ, size s ≤ S → len s ≤ L := fun s hs => by
      have h1 := Carried.le s
      have h2 := hs.trans hSd
      omega
    obtain ⟨s', hs', h3⟩ := mainLoop_within hS hO mS mO hL hr
    have h1 := prologue_within x
    have h2 := within_io ((hI x [] [] [] []).seq (look_within hO (M.init x) [] [] [] [])) []
    have h4 := within_io (dropF_within (Enc.toV s') [] [] [] []) [b]
    rw [List.append_nil] at h2
    have h := ((h1.seq h2).seq h3).seq h4
    have hc' := hc x.length
    dsimp only at hc'
    rw [← hLdef] at hc'
    refine outputs_of_within (h.mono ?_) (List.map_id x) (List.map_id [b])
    have g1 := hL _ (size_le_of_reaches hr)
    have g2 := mO g1
    have g3 : (code (Enc.toV s')).length ≤ L := hL s' hs'
    have g4 : len x = 3 * x.length + 2 := len_bools x
    rw [g4]
    obtain ⟨G, hG⟩ : ∃ G, G = 1 + (tS L + (3 * L + 3 + tO L)) := ⟨_, rfl⟩
    rw [← hG] at hc' ⊢
    obtain ⟨Y, hY⟩ : ∃ Y, Y = c * (x.length + 1) ^ c := ⟨_, rfl⟩
    have e : c * (T + 1) * (x.length + 1) ^ c = T * Y + Y := by rw [hY]; ring
    rw [e]
    rw [← hY] at hc'
    have g5 : T * G ≤ T * Y := Nat.mul_le_mul_left _ (by omega)
    omega

end Groundwork
