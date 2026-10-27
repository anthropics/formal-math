/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces

/-! # The exponent of the pad, computed under a bound (`StNeedC`)

`needC P b Kup lam B sched` goes through the schedule with a state that holds the current label
length, entry size, length of the work list, size of the sum, number of nodes, and the largest
exponent so far. After every step the state is thrown away if its word is longer than 100·(b + 2).
Here: if the computation gives a number, that number is `needG`; and if `needG` is at most
b, the computation gives it.

* Without cut-offs the computation gives `needG` (`needFin_foldl`).
* A state that was thrown away stays away (`foldl_none`), so a result comes from the computation
  without cut-offs (`eq_of_foldl_eq_some`).
* The word of a state has 4·lam + 3·(the binary digits of B, cnt, z, the number of nodes and the
  largest exponent so far) + 26 symbols, and each of these six numbers is at most the largest
  exponent
  so far or `needG` of the rest of the schedule (`len_some_le`); that maximum is the same at every
  step (`tot_cons`). -/

public section

namespace ClauseBound.Alg.NeedC

open Groundwork PaddedDescent.F

/-- The larger of the largest exponent so far and `needG` of the rest of the schedule. -/
@[expose] def tot (P : PiecesF) (st : NState) (sched : List Step) : ℕ :=
  max st.2.2.2 (needG P st.2.2.1 st.1.1.length st.1.2 st.2.1.1 st.2.1.2 sched)

/-- A step does not change `tot`. -/
theorem tot_cons (P : PiecesF) (st : NState) (s : Step) (r : List Step) : tot P (needStep P st s) r = tot P st (s :: r) := by
  simp only [tot, needStep, needG, List.length_replicate, max_assoc]

/-- Without cut-offs the computation gives the larger of the largest exponent at the start and
`needG`. -/
theorem needFin_foldl (P : PiecesF) (sched : List Step) (st : NState) : needFin (sched.foldl (needStep P) st) = tot P st sched := by
  induction sched generalizing st with
  | nil => rfl
  | cons s r ih => rw [List.foldl_cons, ih, tot_cons]

/-- The bounds of the first step (the binary digits of the first sum, lam, and the binary digits of
B and of Kup) are at most `needG`. -/
theorem first_le_needG (P : PiecesF) (Kup lam B cnt z : ℕ) (sched : List Step) :
    max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup))) ≤ needG P Kup lam B cnt z sched := by
  cases sched <;> exact le_max_left _ _

/-- A number has at most as many binary digits as its value. -/
theorem size_le_self (m : ℕ) : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self

/-- The word of a state is short. -/
theorem len_some_le (P : PiecesF) (st : NState) (sched : List Step) {b : ℕ} (h : tot P st sched ≤ b) : len (some st) ≤ 100 * (b + 2) := by
  obtain ⟨⟨lamU, B⟩, ⟨cnt, z⟩, ⟨Kup, mx⟩⟩ := st
  have h1 : mx ≤ b := (le_max_left _ _).trans h
  have h2 := (first_le_needG P Kup lamU.length B cnt z sched).trans ((le_max_right _ _).trans h)
  simp only [max_le_iff] at h2
  obtain ⟨h3, h4, h5, h6⟩ := h2
  have h7 : Nat.size cnt ≤ b := by
    refine (Nat.size_le_size ?_).trans h3
    have : cnt * 1 ≤ cnt * instLen Kup lamU.length B := Nat.mul_le_mul_left _ (by unfold instLen; omega)
    omega
  have h8 : Nat.size z ≤ b := (Nat.size_le_size (by omega)).trans h3
  have h9 : Nat.size mx ≤ b := (size_le_self mx).trans h1
  rw [len_some, len_pair, len_pair, len_pair, len_pair, len_pair, len_units, len_nat, len_nat, len_nat, len_nat, len_nat]
  omega

/-- A state that was thrown away stays away. -/
theorem foldl_none (P : PiecesF) (pad : U) (sched : List Step) :
    sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (none : Option NState) = none := by
  induction sched with
  | nil => rfl
  | cons s r ih =>
    have h : cap pad none ((none : Option NState).map fun st => needStep P st s) = none := by
      unfold cap
      split_ifs <;> rfl
    rw [List.foldl_cons, h, ih]

/-- A result of the computation with cut-offs is the result of the computation without. -/
theorem eq_of_foldl_eq_some (P : PiecesF) (pad : U) (sched : List Step) (st st' : NState)
    (h : sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (some st) = some st') :
    st' = sched.foldl (needStep P) st := by
  induction sched generalizing st with
  | nil => exact (Option.some.inj h).symm
  | cons s r ih =>
    rw [List.foldl_cons, Option.map_some] at h
    by_cases hl : len (some (needStep P st s)) ≤ pad.length
    · rw [cap_eq hl] at h
      exact ih _ h
    · rw [show cap pad none (some (needStep P st s)) = none from if_neg hl, foldl_none] at h
      cases h

/-- If the bound b is at least the largest exponent at the start and `needG`, no cut-off at 100·(b + 2)
is active. -/
theorem foldl_eq_some (P : PiecesF) {pad : U} {b : ℕ} (hp : 100 * (b + 2) ≤ pad.length) (sched : List Step) (st : NState)
    (h : tot P st sched ≤ b) :
    sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (some st) = some (sched.foldl (needStep P) st) := by
  induction sched generalizing st with
  | nil => rfl
  | cons s r ih =>
    rw [← tot_cons] at h
    rw [List.foldl_cons, List.foldl_cons, Option.map_some, cap_eq ((len_some_le P _ r h).trans hp)]
    exact ih _ h

/-- `StNeedC`: the computation under the bound b gives nothing but `needG`, and it gives `needG` if
that is at most b. -/
theorem stNeedC (P : PiecesF) : StNeedC P := by
  intro b Kup lam B sched
  have ht : tot P ((List.replicate lam (), B), (1, 1), (Kup, 0)) sched = needG P Kup lam B 1 1 sched := by
    simp only [tot, List.length_replicate]
    exact max_eq_right (Nat.zero_le _)
  constructor
  · intro v hv
    unfold needC at hv
    obtain ⟨st', h1, h2⟩ := Option.bind_eq_some_iff.1 hv
    by_cases hl : len (some (((List.replicate lam (), B), (1, 1), (Kup, 0)) : NState)) ≤ (List.replicate (100 * (b.length + 2)) ()).length
    · rw [cap_eq hl] at h1
      have h3 := eq_of_foldl_eq_some P _ sched _ _ h1
      split_ifs at h2
      rw [← Option.some.inj h2, h3, needFin_foldl, ht]
    · rw [show cap (List.replicate (100 * (b.length + 2)) ()) none (some (((List.replicate lam (), B), (1, 1), (Kup, 0)) : NState)) = none from
        if_neg hl, foldl_none] at h1
      cases h1
  · intro h
    have hp : 100 * (b.length + 2) ≤ (List.replicate (100 * (b.length + 2)) ()).length := by rw [List.length_replicate]
    rw [← ht] at h
    unfold needC
    rw [cap_eq ((len_some_le P _ sched h).trans hp), foldl_eq_some P hp sched _ h, Option.bind_some, needFin_foldl, if_pos h, ht]

end ClauseBound.Alg.NeedC
