/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs
public import ClauseBound.ParityChecks.Run
public import PaddedDescent.F.LenList

/-! # The choice of the checks in the program is the run

In the program every growing list is cut off by the pad. This file shows that no cut-off is active
when the pad is long enough: the program's `runF` is the function `run`
of proof/rates/ClauseBound/ParityChecks/RunDefs.lean. The proof uses nothing about the two functions
`oA` and `oB` that the run queries: a check is a list of different clauses below m, because each
decision appends the clause that is being
decided or nothing; so its word is short, and there are at most r checks. -/

public section

namespace ClauseBound.ParityChecks.RunF

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run

variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)

/-- The first e decisions for one check, with the list cut off by the pad after each. -/
@[expose] def runToC (Ls : List Chk) (e : ℕ) : Chk := (List.range e).foldl (fun cur x => cap pad [] (q.decide1 oA oB Ls cur x)) (cap pad [] [])

/-- All checks, with the list cut off by the pad after each. -/
@[expose] def runC : List Chk := (List.range q.r).foldl (fun Ls _ => cap pad [] (Ls ++ [runToC pad q oA oB Ls q.m])) (cap pad [] [])

/-- A bound for the length of the word of a check. -/
@[expose] def lenChk (m : ℕ) : ℕ := m * (3 * Nat.size m + 4) + 2

variable {pad q oA oB}

/-- After e decisions the check is a list of at most e clauses, all below e. -/
theorem runTo_shape (Ls : List Chk) (e : ℕ) : (q.runTo oA oB Ls e).length ≤ e ∧ ∀ x ∈ q.runTo oA oB Ls e, x < e := by
  induction e with
  | zero => exact ⟨le_rfl, fun x hx => absurd hx (List.not_mem_nil)⟩
  | succ e ih =>
    rw [runTo_succ]
    unfold Par.decide1
    split_ifs
    · refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with h | h
      · exact (ih.2 x h).trans (Nat.lt_succ_self e)
      · rw [List.mem_singleton.1 h]; exact Nat.lt_succ_self e
    · exact ⟨ih.1.trans (Nat.le_succ e), fun x hx => (ih.2 x hx).trans (Nat.lt_succ_self e)⟩

/-- The word of a check is short. -/
theorem len_runTo_le (Ls : List Chk) {e : ℕ} (he : e ≤ q.m) : len (q.runTo oA oB Ls e) ≤ lenChk q.m := by
  obtain ⟨h1, h2⟩ := runTo_shape (q := q) (oA := oA) (oB := oB) Ls e
  refine Lists.len_list_le' _ (3 * Nat.size q.m + 4) (h1.trans he) fun x hx => ?_
  have := Nat.size_le_size ((h2 x hx).le.trans he)
  rw [len_nat]
  omega

/-- No cut-off is active in the decisions for one check. -/
theorem runToC_eq (hp : lenChk q.m ≤ pad.length) (Ls : List Chk) {e : ℕ} (he : e ≤ q.m) : runToC pad q oA oB Ls e = q.runTo oA oB Ls e := by
  induction e with
  | zero => exact cap_eq ((len_runTo_le (q := q) (oA := oA) (oB := oB) Ls (Nat.zero_le _)).trans hp)
  | succ e ih =>
    have e1 : runToC pad q oA oB Ls (e + 1) = cap pad [] (q.decide1 oA oB Ls (runToC pad q oA oB Ls e) e) := by
      unfold runToC
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e1, ih (by omega), ← runTo_succ]
    exact cap_eq ((len_runTo_le Ls he).trans hp)

/-- The first j checks are j lists with short words. -/
theorem runChecks_shape (j : ℕ) : (q.runChecks oA oB j).length = j ∧ ∀ L ∈ q.runChecks oA oB j, len L ≤ lenChk q.m := by
  induction j with
  | zero => exact ⟨rfl, fun L hL => absurd hL (List.not_mem_nil)⟩
  | succ j ih =>
    rw [runChecks_succ]
    refine ⟨by rw [List.length_append, ih.1]; rfl, fun L hL => ?_⟩
    rcases List.mem_append.1 hL with h | h
    · exact ih.2 L h
    · rw [List.mem_singleton.1 h]; exact len_runTo_le _ le_rfl

/-- The word of the list of the first j ≤ r checks is short. -/
theorem len_runChecks_le {j : ℕ} (hj : j ≤ q.r) : len (q.runChecks oA oB j) ≤ q.r * (lenChk q.m + 2) + 2 := by
  obtain ⟨h1, h2⟩ := runChecks_shape (q := q) (oA := oA) (oB := oB) j
  exact Lists.len_list_le' _ (lenChk q.m + 2) (h1.le.trans hj) fun L hL => Nat.add_le_add_right (h2 L hL) 2

/-- No cut-off is active in the whole choice. -/
theorem runC_eq (hp : q.r * (lenChk q.m + 2) + 2 ≤ pad.length) (hp' : lenChk q.m ≤ pad.length) : runC pad q oA oB = q.run oA oB := by
  have key : ∀ j ≤ q.r, (List.range j).foldl (fun Ls _ => cap pad [] (Ls ++ [runToC pad q oA oB Ls q.m])) (cap pad [] []) = q.runChecks oA oB j := by
    intro j
    induction j with
    | zero => exact fun _ => cap_eq ((len_runChecks_le (q := q) (oA := oA) (oB := oB) (Nat.zero_le _)).trans hp)
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      change cap pad [] (q.runChecks oA oB j ++ [runToC pad q oA oB (q.runChecks oA oB j) q.m]) = _
      rw [runToC_eq hp' _ le_rfl, ← runChecks_succ]
      exact cap_eq ((len_runChecks_le hj).trans hp)
  exact key q.r le_rfl

/-- The bound for one check, in terms of bounds for m. -/
theorem lenChk_add_two_le {n Δ : ℕ} (hm : q.m ≤ Δ * n) : lenChk q.m + 2 ≤ 8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2)) := by
  have hs := Nat.size_le_size hm
  unfold lenChk
  have h2 : q.m * (3 * Nat.size q.m + 4) ≤ (Δ * n) * (3 * Nat.size (Δ * n) + 4) := Nat.mul_le_mul hm (by omega)
  nlinarith

/-- The length that the program asks of the pad, written as a product. -/
theorem big_eq (n Δ : ℕ) : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) = 6 * n * (8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2))) + 8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2)) := by
  ring

/-- The word of a check is shorter than the length that the program asks of the pad. -/
theorem lenChk_le_big {n Δ : ℕ} (hm : q.m ≤ Δ * n) : lenChk q.m ≤ 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 := by
  have h1 := lenChk_add_two_le (q := q) hm
  rw [big_eq]
  omega

/-- So is the word of the list of all checks. -/
theorem all_le_big {n Δ : ℕ} (hr : q.r ≤ 6 * n) (hm : q.m ≤ Δ * n) :
    q.r * (lenChk q.m + 2) + 2 ≤ 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 := by
  have h3 : q.r * (lenChk q.m + 2) ≤ (6 * n) * (8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2))) := Nat.mul_le_mul hr (lenChk_add_two_le hm)
  rw [big_eq]
  omega

variable {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par) (ψ : Fml)

/-- The choice of the checks in the program is the run. -/
theorem runF_eq (hF : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ pad.length) (hr : q.r ≤ 6 * n) (hm : q.m ≤ Δ * n) :
    runF S k pad i n Δ q ψ = q.run (orcA S k pad i n Δ q ψ) (orcB S k pad i n Δ q ψ) :=
  runC_eq ((all_le_big hr hm).trans hF) ((lenChk_le_big hm).trans hF)

end ClauseBound.ParityChecks.RunF
