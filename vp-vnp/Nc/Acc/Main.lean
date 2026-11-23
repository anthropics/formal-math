/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.Prog
import NS1.Main

/-!
# The size of the program of low degree
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

section Size

theorem size_quote (c : Tree) : (Fm.quote c).code.size = c.size + 2 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_id : Fm.id.code.size = 5 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_hd (a : Fm) : (Fm.hd a).code.size = a.code.size + 6 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_tl (a : Fm) : (Fm.tl a).code.size = a.code.size + 8 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_cons (a b : Fm) : (Fm.cons a b).code.size = a.code.size + b.code.size + 11 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_ite (a b c : Fm) : (Fm.ite a b c).code.size = a.code.size + b.code.size + c.code.size + 14 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_run (a b : Fm) : (Fm.run a b).code.size = a.code.size + b.code.size + 15 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_guess : Fm.guess.code.size = 17 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_mul (a : Fm) : (Fm.mul a).code.size = a.code.size + 22 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_app (p : Tree) (e : Fm) : (app p e).code.size = p.size + e.code.size + 17 := by
  rw [app, size_run, size_quote]; ring

theorem size_lett (e b : Fm) : (lett e b).code.size = b.code.size + e.code.size + 17 := by
  rw [lett, size_run, size_quote]; ring

theorem size_gwd (M : ℕ) : (gwd M).code.size = 50 * M + 3 := by
  induction M with
  | zero => simp [gwd, size_quote, Tree.size]
  | succ M ih =>
    rw [gwd, size_cons, size_ite, size_guess, size_quote, size_quote, ih]
    simp only [one, Tree.size]
    ring

theorem size_walkF (m : ℕ) : (walkF m).code.size = (stepW.code.size + 17) * m + 5 := by
  induction m with
  | zero => simp [walkF, size_id]
  | succ m ih =>
    rw [walkF, size_lett, ih]
    ring

theorem size_pairsF (m : ℕ) (l : Fm) : (pairsF m l).code.size = l.code.size + (2 * pairB.code.size + 30) * m := by
  induction m generalizing l with
  | zero => simp [pairsF]
  | succ m ih =>
    rw [pairsF, ih, size_app, size_cons, size_quote]
    ring

/-- The size of the program. -/
theorem size_accF : ∃ c : ℕ, ∀ (M m d : ℕ) (out : List Bool), out.length = M →
    (accF M m d out).code.size ≤ c * (M + m + 1) + 2 * d := by
  obtain ⟨c1, hc1⟩ : ∃ n, n = stepW.code.size := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ n, n = leafB.code.size := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ n, n = intB.code.size := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ n, n = pairB.code.size := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ n, n = (wordB lt0 lt1).code.size := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ n, n = lt2.size := ⟨_, rfl⟩
  obtain ⟨c7, hc7⟩ : ∃ n, n = (ofBits [true, false]).size := ⟨_, rfl⟩
  obtain ⟨c8, hc8⟩ : ∃ n, n = Fm.fail.code.size := ⟨_, rfl⟩
  have hloop : ∀ M m, (loopF M m).code.size ≤ 200 * M + (c1 + 17) * m + (c2 + c3 + c8 + 500) := by
    intro M m
    rw [loopF, size_ite, size_ite, leafF, intF, size_lett, size_ite, size_lett, size_cons, size_cons, size_cons, size_lett,
      size_cons, size_gwd, size_walkF]
    simp only [size_hd, size_tl, size_id, size_guess, size_quote, Tree.size, ← hc1, ← hc2, ← hc3, ← hc8]
    omega
  refine ⟨2 * (200 + c1 + 17 + c2 + c3 + c8 + 500) + (2 * c4 + 30) + 2 * c5 + c6 + c7 + 500, fun M m d out ho => ?_⟩
  have h1 := hloop M m
  have h2 := size_ofBits out
  rw [ho] at h2
  rw [accF, size_ite, size_mul, size_app, size_cons, size_cons, size_cons, treeF, size_hd, size_pairsF, size_app, size_cons,
    size_cons]
  simp only [size_guess, size_quote, size_id, size_num, ← hc4, ← hc5, ← hc6, ← hc7, List.map_cons, List.map_nil, listT,
    Tree.size]
  have h3 : (c1 + 17) * m ≤ (c1 + 17) * (M + m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : (2 * c4 + 30) * m ≤ (2 * c4 + 30) * (M + m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : c2 + c3 + c8 + 500 ≤ (c2 + c3 + c8 + 500) * (M + m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : 2 * c5 + c6 + c7 + 400 ≤ (2 * c5 + c6 + c7 + 400) * (M + m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : (2 * (200 + c1 + 17 + c2 + c3 + c8 + 500) + (2 * c4 + 30) + 2 * c5 + c6 + c7 + 500) * (M + m + 1) =
      400 * (M + m + 1) + 2 * ((c1 + 17) * (M + m + 1)) + 2 * ((c2 + c3 + c8 + 500) * (M + m + 1)) +
      (2 * c4 + 30) * (M + m + 1) + (2 * c5 + c6 + c7 + 400) * (M + m + 1) + 100 * (M + m + 1) := by ring
  omega

end Size

end NS1
