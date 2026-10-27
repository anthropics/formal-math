/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces
import CountKSat.InOut
import Batteries.Data.Nat.Lemmas
import all StepMachines.Prog.Decode

/-! # Exhaustive counting is correct

`bruteN k (x, pad)` of proof/consequences/CountKSatRate/Defs.lean reads the formula written in x,
the code of an instance of k-SAT, and counts, among the assignments number 0, …, 2^n − 1
that the pad reaches, those that satisfy it. Assignment number y gives the variable i the i-th
binary digit of y, so these numbers stand for the 2^n assignments, each exactly once.
With a pad of at least 2^n units nothing is cut off, and the result is the count (`stBruteC`, which
proves the interface statement `StBruteC` of
proof/consequences/CountKSatRate/Interfaces.lean).
The file is the counting version of `bruteA_enc_of_le` in proof/rates/PaddedDescent/BrutePad.lean. -/

namespace CountKSatRate.Brute

open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)

/-- Assignment number y satisfies the formula, with variables written as natural numbers, exactly
when its binary digits make a literal of every clause true. -/
theorem satAt_toN {n : ℕ} (φ : CNF n) (y : ℕ) : satAt (toN φ) y = true ↔ ∀ C ∈ φ, ∃ l ∈ C, y.testBit l.1 = l.2 := by
  simp [satAt, toN]

/-- Among the numbers below 2^n, as many satisfy the formula as there are satisfying assignments. -/
theorem length_filter_satAt {n : ℕ} (φ : CNF n) : ((List.range (2 ^ n)).filter fun y => satAt (toN φ) y).length = numSat φ := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), numSat]
  refine Finset.card_bij' (fun y _ => fun i : Fin n => y.testBit i) (fun a _ => Nat.ofBits a) ?_ ?_ ?_ ?_
  · intro y hy
    have h := (List.mem_filter.1 (List.mem_toFinset.1 hy)).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (satAt_toN φ y).1 h⟩
  · intro a ha
    refine List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 (Nat.ofBits_lt_two_pow a), (satAt_toN φ _).2 fun C hC => ?_⟩)
    obtain ⟨l, hl, h⟩ := (Finset.mem_filter.1 ha).2 C hC
    exact ⟨l, hl, by rw [Nat.testBit_ofBits_lt a _ l.1.2]; exact h⟩
  · intro y hy
    have h := List.mem_range.1 (List.mem_filter.1 (List.mem_toFinset.1 hy)).1
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt h]
  · intro a _
    funext i
    exact Nat.testBit_ofBits_lt a _ i.2

/-- `outW` writes N as n + 1 bits, lowest bit first, exactly as `binary n N`. -/
theorem outW_eq_binary (n : ℕ) (ψ : Fml) (N : ℕ) : outW ((List.replicate n (), ψ), N) = binary n N := by
  rw [outW, List.length_replicate, toWord_eq]
  rfl

end CountKSatRate.Brute

namespace CountKSatRate

open CountKSatRate.Brute

/-- With a pad of at least 2^n units, exhaustive counting returns the number of satisfying
assignments. -/
public theorem stBruteC : StBruteC := fun k n φ hk hφ w hw => by
  rw [bruteN, nK, CountKSat.stDecU k n φ hk hφ.1]
  simp only [List.length_replicate, PaddedDescent.F.rng, Nat.min_eq_left hw]
  rw [length_filter_satAt]

end CountKSatRate
