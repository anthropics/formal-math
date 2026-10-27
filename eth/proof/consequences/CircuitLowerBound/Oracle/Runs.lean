/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Oracle.Machine
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): from a machine that is started again after every answer to an oracle machine: the runs

The three kinds of loops (`run_mv`, `run_dr`, `run_cp`), each with its exact number of steps; the
part of a round before M runs (`run_build`); M's run and the step after it (`run_round`); the end
(`run_finish`); a query with its answer (`run_query`); and, by induction on the rounds, the whole
run (`run_protocol`). Between two rounds the machine is at the label `cpA`, all stacks of M and the
spare stack are empty,
`io` holds x and `ans` holds the answers so far, the last one on top. -/

public section

namespace CircuitLowerBound.Oracle

open ENP Turing Groundwork.TM

variable {M : TM2ComputableAux Bool Bool} (O : Lang)

/-! ### The new stacks after a loop -/

theorem upd_cons {s d : NS} (hsd : s ≠ d) (n : NS → List Bool) (b : Bool) (l : List Bool) :
    Function.update (Function.update (Function.update (Function.update n s l) d (b :: n d)) s []) d (l.reverse ++ b :: n d)
      = Function.update (Function.update n s []) d ((b :: l).reverse ++ n d) := by
  have hds : d ≠ s := hsd.symm
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### The loops -/

/-- The loop that moves the stack s to the stack d takes one step for each bit and one more. -/
theorem run_mv {s d : NS} (hsd : s ≠ d) {me : Ctl} {nx : Λ' M} (hme : prog M (.inr me) = mvS M s d (.inr me) nx) (hask : me ≠ .ask)
    (v : M.tm.σ) (T : ∀ k, List (M.tm.Γ k)) (l : List Bool) : ∀ n : NS → List Bool, n s = l →
    Run (stp M O) ⟨some (.inr me), (v, none), stk M T n⟩ (l.length + 1)
      ⟨some nx, (v, none), stk M T (Function.update (Function.update n s []) d (l.reverse ++ n d))⟩ := by
  have hl : (Sum.inr me : Λ' M) ≠ .inr .ask := by simpa using hask
  induction l with
  | nil =>
    intro n h
    refine Run.one ?_
    rw [stp_of_ne O hl, hme]
    have e : Function.update (Function.update n s []) d (n d) = Function.update n s [] := by
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    simp [mvS, TM2.stepAux, h, e]
  | cons b l ih =>
    intro n h
    have h1 : stp M O ⟨some (.inr me), (v, none), stk M T n⟩
        = some ⟨some (.inr me), (v, none), stk M T (Function.update (Function.update n s l) d (b :: n d))⟩ := by
      rw [stp_of_ne O hl, hme]
      simp [mvS, TM2.stepAux, h, Function.update_of_ne hsd.symm]
    have h2 := ih (Function.update (Function.update n s l) d (b :: n d)) (by simp [Function.update_of_ne hsd])
    rw [Function.update_self, upd_cons hsd] at h2
    exact ⟨_, h1, h2⟩

/-- The loop that empties the stack s. -/
theorem run_dr {s : NS} {me : Ctl} {nx : Λ' M} (hme : prog M (.inr me) = drS M s (.inr me) nx) (hask : me ≠ .ask)
    (v : M.tm.σ) (T : ∀ k, List (M.tm.Γ k)) (l : List Bool) : ∀ n : NS → List Bool, n s = l →
    Run (stp M O) ⟨some (.inr me), (v, none), stk M T n⟩ (l.length + 1) ⟨some nx, (v, none), stk M T (Function.update n s [])⟩ := by
  have hl : (Sum.inr me : Λ' M) ≠ .inr .ask := by simpa using hask
  induction l with
  | nil =>
    intro n h
    refine Run.one ?_
    rw [stp_of_ne O hl, hme]
    simp [drS, TM2.stepAux, h]
  | cons b l ih =>
    intro n h
    have h1 : stp M O ⟨some (.inr me), (v, none), stk M T n⟩ = some ⟨some (.inr me), (v, none), stk M T (Function.update n s l)⟩ := by
      rw [stp_of_ne O hl, hme]
      simp [drS, TM2.stepAux, h]
    have h2 := ih (Function.update n s l) (by simp)
    rw [Function.update_idem] at h2
    exact ⟨_, h1, h2⟩

/-- What the copying loop pushes on the input stack of M, above L, when it reads the bits l. -/
def pushed (M : TM2ComputableAux Bool Bool) (mark : Bool) : List Bool → List (M.tm.Γ M.tm.k₀) → List (M.tm.Γ M.tm.k₀)
  | [], L => L
  | b :: l, L => pushed M mark l (if mark then M.inputAlphabet.invFun true :: M.inputAlphabet.invFun b :: L else M.inputAlphabet.invFun b :: L)

theorem pushed_false (l : List Bool) : ∀ L, pushed M false l L = l.reverse.map M.inputAlphabet.invFun ++ L := by
  induction l with
  | nil => intro L; rfl
  | cons b l ih => intro L; simp [pushed, ih]

theorem pushed_true (l : List Bool) : ∀ L, pushed M true l L = (l.reverse.flatMap fun b => [true, b]).map M.inputAlphabet.invFun ++ L := by
  induction l with
  | nil => intro L; rfl
  | cons b l ih => intro L; simp [pushed, ih]

/-- The copying loop. -/
theorem run_cp {s d : NS} (hsd : s ≠ d) {mark : Bool} {me : Ctl} {nx : Λ' M} (hme : prog M (.inr me) = cpS M s d mark (.inr me) nx)
    (hask : me ≠ .ask) (v : M.tm.σ) (l : List Bool) : ∀ (L : List (M.tm.Γ M.tm.k₀)) (n : NS → List Bool), n s = l →
    Run (stp M O) ⟨some (.inr me), (v, none), stk M (one M.tm.k₀ L) n⟩ (l.length + 1)
      ⟨some nx, (v, none), stk M (one M.tm.k₀ (pushed M mark l L)) (Function.update (Function.update n s []) d (l.reverse ++ n d))⟩ := by
  have hl : (Sum.inr me : Λ' M) ≠ .inr .ask := by simpa using hask
  induction l with
  | nil =>
    intro L n h
    refine Run.one ?_
    rw [stp_of_ne O hl, hme]
    have e : Function.update (Function.update n s []) d (n d) = Function.update n s [] := by
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    simp [cpS, TM2.stepAux, h, e, pushed]
  | cons b l ih =>
    intro L n h
    have h1 : stp M O ⟨some (.inr me), (v, none), stk M (one M.tm.k₀ L) n⟩
        = some ⟨some (.inr me), (v, none), stk M (one M.tm.k₀
            (if mark then M.inputAlphabet.invFun true :: M.inputAlphabet.invFun b :: L else M.inputAlphabet.invFun b :: L))
          (Function.update (Function.update n s l) d (b :: n d))⟩ := by
      rw [stp_of_ne O hl, hme]
      cases mark <;> simp [cpS, TM2.stepAux, h, Function.update_of_ne hsd.symm]
    have h2 := ih (if mark then M.inputAlphabet.invFun true :: M.inputAlphabet.invFun b :: L else M.inputAlphabet.invFun b :: L)
      (Function.update (Function.update n s l) d (b :: n d)) (by simp [Function.update_of_ne hsd])
    rw [Function.update_self, upd_cons hsd] at h2
    exact ⟨_, h1, h2⟩

/-! ### A round -/

/-- Before M runs: the input of the round is written on the input stack of M; x and the answers are
kept. -/
theorem run_build (v : M.tm.σ) (x ans : List Bool) :
    Run (stp M O) ⟨some (.inr .cpA), (v, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ (2 * ans.length + 2 * x.length + 5)
      ⟨some (.inl M.tm.main), (v, none), stk M (one M.tm.k₀ ((roundInput x ans).map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
  have r1 := run_cp O (M := M) (s := .ans) (d := .sp) (by decide) (mark := false) (me := .cpA) rfl (by decide) v ans.reverse [] (ns x ans.reverse []) rfl
  have r2 := run_mv O (M := M) (s := .sp) (d := .ans) (by decide) (me := .mvA) rfl (by decide) v (one M.tm.k₀ (ans.map M.inputAlphabet.invFun)) ans (ns x [] ans) rfl
  have r3 : Run (stp M O) ⟨some (.inr .sep), (v, none), stk M (one M.tm.k₀ (ans.map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ 1
      ⟨some (.inr .mvX), (v, none), stk M (one M.tm.k₀ (M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
    refine Run.one ?_
    rw [stp_of_ne O (by simp)]
    simp [prog, TM2.stepAux]
  have r4 := run_mv O (M := M) (s := .io) (d := .sp) (by decide) (me := .mvX) rfl (by decide) v
    (one M.tm.k₀ (M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun)) x (ns x ans.reverse []) rfl
  have r5 := run_cp O (M := M) (s := .sp) (d := .io) (by decide) (mark := true) (me := .cpX) rfl (by decide) v x.reverse
    (M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun) (ns [] ans.reverse x.reverse) rfl
  simp only [pushed_false, pushed_true, upd_io, upd_ans, upd_sp, ns_io, ns_ans, ns_sp, List.reverse_reverse, List.append_nil, List.length_reverse] at r1 r2 r4 r5
  have e : (x.flatMap fun b => [true, b]).map M.inputAlphabet.invFun ++ M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun
      = (roundInput x ans).map M.inputAlphabet.invFun := by simp [roundInput]
  rw [e] at r5
  have r := (((r1.trans r2).trans r3).trans r4).trans r5
  have hn : ans.length + 1 + (ans.length + 1) + 1 + (x.length + 1) + (x.length + 1) = 2 * ans.length + 2 * x.length + 5 := by ring
  rw [hn] at r
  exact r

theorem liftCfg_init (n : NS → List Bool) (s : List (M.tm.Γ M.tm.k₀)) :
    liftCfg n (initList M.tm s) = ⟨some (.inl M.tm.main), (M.tm.initialState, none), stk M (one M.tm.k₀ s) n⟩ := by
  unfold liftCfg
  rw [initList_stk]
  rfl

theorem liftCfg_halt (n : NS → List Bool) (s : List (M.tm.Γ M.tm.k₁)) :
    liftCfg n (haltList M.tm s) = ⟨some (.inr .after), (M.tm.initialState, none), stk M (one M.tm.k₁ s) n⟩ := by
  unfold liftCfg
  rw [haltList_stk]
  rfl

/-- A whole round up to the step after M's run: the first bit c of the output of M is gone and has
decided where the machine goes on. -/
theorem run_round {T : ℕ} {x ans : List Bool} {c : Bool} {w : List Bool} (h : Round M T x ans (c :: w)) :
    ∃ t ≤ 2 * ans.length + 2 * x.length + T + 6,
      Run (stp M O) ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ t
        ⟨some (if c then .inr .ask else .inr .drX), (M.tm.initialState, none),
          stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
  obtain ⟨E⟩ := h
  have r1 := run_build O (M := M) M.tm.initialState x ans
  have r2 := run_lift O (ns x ans.reverse []) (run_of_iterate E.evals_in_steps)
  rw [liftCfg_init, liftCfg_halt] at r2
  have r3 : Run (stp M O) ⟨some (.inr .after), (M.tm.initialState, none), stk M (one M.tm.k₁ ((c :: w).map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ 1
      ⟨some (if c then .inr .ask else .inr .drX), (M.tm.initialState, none),
        stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
    refine Run.one ?_
    rw [stp_of_ne O (by simp)]
    cases c <;> simp [prog, TM2.stepAux]
  refine ⟨_, ?_, (r1.trans r2).trans r3⟩
  have := E.steps_le_m
  omega

/-- The end: x and the answers are dropped, the result goes to the output stack. -/
theorem run_finish (x ans : List Bool) (b : Bool) :
    Run (stp M O) ⟨some (.inr .drX), (M.tm.initialState, none), stk M (one M.tm.k₁ ([b].map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩
      (x.length + ans.length + 3) ⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ := by
  have r1 := run_dr O (M := M) (s := .io) (me := .drX) rfl (by decide) M.tm.initialState (one M.tm.k₁ ([b].map M.outputAlphabet.invFun)) x
    (ns x ans.reverse []) rfl
  have r2 := run_dr O (M := M) (s := .ans) (me := .drA) rfl (by decide) M.tm.initialState (one M.tm.k₁ ([b].map M.outputAlphabet.invFun)) ans.reverse
    (ns [] ans.reverse []) rfl
  simp only [upd_io, upd_ans, List.length_reverse] at r1 r2
  have r3 : Run (stp M O) ⟨some (.inr .fin), (M.tm.initialState, none), stk M (one M.tm.k₁ ([b].map M.outputAlphabet.invFun)) (ns [] [] [])⟩ 1
      ⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ := by
    refine Run.one ?_
    rw [stp_of_ne O (by simp), one_nil M.tm.k₀ M.tm.k₁]
    simp [prog, TM2.stepAux]
  have r := (r1.trans r2).trans r3
  have hn : x.length + 1 + (ans.length + 1) + 1 = x.length + ans.length + 3 := by ring
  rw [hn] at r
  exact r

open Classical in
/-- A query and its answer: two steps. -/
theorem run_query (x ans w : List Bool) :
    Run (stp M O) ⟨some (.inr .ask), (M.tm.initialState, none), stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ 2
      ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x (ans ++ [decide (O w)]).reverse [])⟩ := by
  have hw : (w.map M.outputAlphabet.invFun).map M.outputAlphabet = w := by
    rw [List.map_map]
    have : (M.outputAlphabet : _ → Bool) ∘ M.outputAlphabet.invFun = id := funext M.outputAlphabet.right_inv
    rw [this, List.map_id]
  have h1 := stp_ask O (M := M) (M.tm.initialState, none) (stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse []))
  rw [stk_inl, one_self, hw, update_inl, update_one, one_nil M.tm.k₁ M.tm.k₀] at h1
  refine ⟨_, h1, Run.one ?_⟩
  by_cases h : O w
  · rw [if_pos h, stp_of_ne O (by simp)]
    simp [prog, TM2.stepAux, h]
  · rw [if_neg h, stp_of_ne O (by simp)]
    simp [prog, TM2.stepAux, h]

/-- The whole run, from a point between two rounds. -/
theorem run_protocol {T : ℕ} {x : List Bool} {b : Bool} {ans : List Bool} {r : ℕ} (h : Protocol M T x b ans r) :
    ∃ t ≤ (r + 1) * (3 * (ans.length + r) + 3 * x.length + T + 12),
      Run (stp M SAT) ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ t
        ⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ := by
  induction h with
  | @done ans r hR =>
    obtain ⟨t, ht, r1⟩ := run_round SAT hR
    refine ⟨_, ?_, r1.trans (run_finish SAT x ans b)⟩
    have : 1 * (3 * (ans.length + r) + 3 * x.length + T + 12) ≤ (r + 1) * (3 * (ans.length + r) + 3 * x.length + T + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  | @query ans w r hR _ ih =>
    obtain ⟨t, ht, r1⟩ := run_round SAT hR
    obtain ⟨t', ht', r3⟩ := ih
    refine ⟨_, ?_, (r1.trans (run_query SAT x ans w)).trans r3⟩
    rw [List.length_append, List.length_singleton] at ht'
    have e : ans.length + 1 + r = ans.length + (r + 1) := by ring
    rw [e] at ht'
    have : (r + 1 + 1) * (3 * (ans.length + (r + 1)) + 3 * x.length + T + 12)
        = (r + 1) * (3 * (ans.length + (r + 1)) + 3 * x.length + T + 12) + (3 * (ans.length + (r + 1)) + 3 * x.length + T + 12) := by ring
    omega

end CircuitLowerBound.Oracle
