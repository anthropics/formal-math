/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/

instance Cond.decidableHolds (σ : State) : (c : Cond) → Decidable (c.Holds σ)
  | .lt a b => inferInstanceAs (Decidable (a.val σ < b.val σ))
  | .eq a b => inferInstanceAs (Decidable (a.val σ = b.val σ))

/-- The state after a block (σ itself for a loop or a call, which are not blocks). -/
@[simp] def Stmt.after : Stmt → State → State
  | .set x e, σ => { σ with loc := Function.update σ.loc x (e.val σ) }
  | .store a e, σ => { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
  | .seq s t, σ => t.after (s.after σ)
  | .ite c s t, σ => if c.Holds σ then s.after σ else t.after σ
  | _, σ => σ

/-- A bound on the number of steps of a block: the longer side of each branch counts (0 for a loop
or a call). -/
@[simp] def Stmt.blockCost : Stmt → ℕ
  | .set _ e => e.cost + 1
  | .store a e => a.cost + e.cost + 1
  | .seq s t => s.blockCost + t.blockCost
  | .ite c s t => c.cost + 1 + max s.blockCost t.blockCost
  | _ => 0

/-- The statement is a block, and its run from σ stays within the limits. -/
@[simp] def Stmt.BlockSafe (lim : Limits) : Stmt → State → Prop
  | .skip, _ => True
  | .set _ e, σ => e.Safe lim σ
  | .store a e, σ => a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ)
  | .seq s t, σ => s.BlockSafe lim σ ∧ t.BlockSafe lim (s.after σ)
  | .ite c s t, σ =>
    c.Safe lim σ ∧ (c.Holds σ → s.BlockSafe lim σ) ∧ (¬ c.Holds σ → t.BlockSafe lim σ)
  | _, _ => False

/-- The block s, started in σ, stays within the limits and ends in a state that satisfies R. -/
abbrev Stmt.Runs (lim : Limits) (s : Stmt) (σ : State) (R : State → Prop) : Prop :=
  s.BlockSafe lim σ ∧ R (s.after σ)

/-! ## The default proofs -/

/-- `light_time [t₁, t₂]` compares two numbers of steps, after computing the costs of the
expressions, tests, blocks and argument lists that occur and unfolding the running times `t₁`,
`t₂`. -/
macro "light_time" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, $ts,*]
       first | omega | (ring_nf; omega))
    | omega
    | (simp [$ts,*] <;> first | omega | (ring_nf; omega)))

/-- Compares two numbers of steps, after computing the costs of the expressions, tests, blocks and
argument lists that occur. -/
macro "light_time" : tactic => `(tactic| light_time [])

/-- `light_side [h₁, h₂]` proves that an expression or a test stays within the limits, has a given
value, or holds, after putting in the values of the variables.  The facts `h₁`, `h₂` say what the
cells hold that are read, or are definitions to be unfolded; everything else is linear arithmetic
over the hypotheses in the context, to which the two fields of a hypothesis `Std lim` are added. -/
macro "light_side" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    ((try have := Std.space_le (by assumption))
     (try have := Std.const_le (by assumption))
     simp [Limits.Addr, abs_le, -abs_mul, $ts,*] <;> omega))

/-- Proves that an expression or a test stays within the limits, has a given value, or holds, after
putting in the values of the variables, by linear arithmetic over the hypotheses in the context. -/
macro "light_side" : tactic => `(tactic| light_side [])

/-- Proves an inequality between addresses, sizes and bounds by linear arithmetic over the
hypotheses in the context.  A field of a record that is written out, such as
`{ dst := a, len := n }.len`, is computed first. -/
macro "light_arith" : tactic => `(tactic| first | omega | light_side)

/-! ## Rules for blocks -/

/-- A weaker conclusion. -/
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩

/-- Two blocks, one after the other. -/
theorem Stmt.Runs.seq {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ fun σ' => t.Runs lim σ' R) : (s ;; t).Runs lim σ R :=
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- A branch whose test holds. -/
theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by light_side) (hs : c.Safe lim σ := by light_side) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩

/-- A branch whose test fails. -/
theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by light_side) (hs : c.Safe lim σ := by light_side) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩

theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by light_time) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by light_time) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  h

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by light_time) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.next T₁ (h.mono le_rfl rest) hT

/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by light_time) :
    Ends lim P d s σ T Q :=
  h.mono hT rest

/-- An assignment at the end of the program. -/
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h

/-- An assignment, followed by the rest of the program. -/
theorem Ends.setThen {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩ (T - (e.cost + 1)) Q)
    (hs : e.Safe lim ⟨loc, μ⟩ := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.set hs le_rfl h) hT

/-- A store at the end of the program. -/
theorem Ends.storeLast {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {Q : State → Prop}
    (h : Q ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) : Ends lim P d (.store a e) ⟨loc, μ⟩ T Q :=
  Ends.store hs.1 hs.2.1 hs.2.2 hT h

/-- A store, followed by the rest of the program. -/
theorem Ends.storeThen {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩
      (T - (a.cost + e.cost + 1)) Q)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.store a e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.storeLast h hs le_rfl) hT

/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by light_side) (hT : c.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by light_side) (hT : c.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by light_side)
    (hT : c.cost + 1 ≤ T := by light_time) : Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by light_time) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

/-! ## Counting loops -/

/-- for i = 0, …, hi - 1 do body. -/
abbrev Stmt.for (i : ℕ) (hi : Expr) (body : Stmt) : Stmt :=
  .set i (k 0) ;; .while (v i <' hi) (body ;; .set i (v i +' k 1))

/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (v i +' k 1).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(v i +' k 1).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light
