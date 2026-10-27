/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces

/-! # The exponent of a pad that suffices for all levels (`StNeedG`)

`FitsG P F …` lists what the descent through a schedule needs of the length F of the pad: one
inequality «… ≤ F» for every loop and every state. `needG P …` is the largest of
the exponents of these inequalities and of the label length and the numbers of binary digits of B
and of the number of nodes (these three are there for the computation of `needG` under a
bound). Here: a pad of length at least 2^needG satisfies all the inequalities (`fitsG_of_le`,
`stNeedG`). -/

public section

namespace ClauseBound.Alg.Need

open PaddedDescent.F

/-- A number with at most n binary digits is at most F if 2^n ≤ F. -/
theorem le_of_size_le {x n F : ℕ} (h : 2 ^ n ≤ F) (hx : Nat.size x ≤ n) : x ≤ F :=
  (Nat.lt_size_self x).le.trans ((Nat.pow_le_pow_right (by norm_num) hx).trans h)

/-- 2^a ≤ F if a ≤ n and 2^n ≤ F. -/
theorem pow_le_of_le {a n F : ℕ} (h : 2 ^ n ≤ F) (ha : a ≤ n) : 2 ^ a ≤ F :=
  (Nat.pow_le_pow_right (by norm_num) ha).trans h

/-- K^p ≤ 2^(p · number of binary digits of K). -/
theorem pow_le_two_pow_size (K p : ℕ) : K ^ p ≤ 2 ^ (p * Nat.size K) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self K).le p

/-- The budgets hold for every pad of length at least 2^n, as soon as n is at least `needG`. -/
theorem fitsG_of_le (P : PiecesF) {F n : ℕ} (hF : 2 ^ n ≤ F) : ∀ (sched : List Step) (Kup lam B cnt z : ℕ),
    needG P Kup lam B cnt z sched ≤ n → FitsG P F Kup lam B cnt z sched
  | [], Kup, lam, B, cnt, z, h => by
    simp only [needG, max_le_iff] at h
    exact ⟨le_of_size_le hF h.1.1, pow_le_of_le hF h.2⟩
  | s :: r, Kup, lam, B, cnt, z, h => by
    simp only [needG, max_le_iff] at h
    obtain ⟨⟨h0, -⟩, ⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7⟩ := h
    refine ⟨le_of_size_le hF h0, ?_, fitsG_of_le P hF r _ _ _ _ _ h7⟩
    exact
      { pieces := pow_le_of_le hF h1
        pat := le_of_size_le hF h2
        col := (pow_le_two_pow_size _ _).trans (pow_le_of_le hF h3)
        st := pow_le_of_le hF ((Nat.mul_le_mul_left _ (Nat.le_succ _)).trans h4)
        lab := pow_le_of_le hF ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans h4)
        tab := pow_le_of_le hF h5
        enumLab := fun ht => by
          rw [if_pos ht] at h6
          exact pow_le_of_le hF ((le_max_left _ _).trans h6)
        enumSt := fun ht => by
          rw [if_pos ht] at h6
          exact pow_le_of_le hF ((le_max_right _ _).trans h6) }

/-- `StNeedG`: a pad of length at least 2^needG suffices for all levels. -/
theorem stNeedG (P : PiecesF) : StNeedG P := fun _ Kup lam B cnt z sched h => fitsG_of_le P h sched Kup lam B cnt z le_rfl

end ClauseBound.Alg.Need
