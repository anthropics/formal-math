/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatRateStatement
public import PaddedDescent.Params
public import PaddedDescent.Pad
import PaddedDescent.RateLemmas

/-! From a polynomial-time function of the padded input to the rate statement. `inRateTM_of_padded`:
let A be a polynomial-time
function (`PolyT`) of a bit string and a pad, and e a polynomial-time function that says how long
the pad is to be, namely 2^(e x). If on
the code of every instance of 3-SAT on n variables e is at most C₀·(n / 2^(sOf n) + 1), and A with
the pad of that length returns the bit
«satisfiable», then `Sat3.InRateTM (3/19)` holds: one Turing machine decides 3-SAT within
C·2^{C·n/(log₂(n+2))^{3/19}} steps, for some constant C.
The work here is to absorb the polynomial in the length of the input, (n+2)^{4q}, into the bound:
⌊log₂(n+2)⌋·2^s ≤ 8·(n + 2^s) whenever
2^s ≤ ⌊log₂(n+2)⌋, which holds for s = sOf n. -/

namespace PaddedDescent

open Groundwork Sat3 Turing

/-- L² ≤ 4·2^L. -/
theorem sq_le_four_mul_two_pow (L : ℕ) : L * L ≤ 4 * 2 ^ L := by
  have h1 : L / 2 < 2 ^ (L / 2) := Nat.lt_two_pow_self
  have h2 : L ≤ 2 * 2 ^ (L / 2) := by omega
  calc L * L ≤ (2 * 2 ^ (L / 2)) * (2 * 2 ^ (L / 2)) := Nat.mul_le_mul h2 h2
    _ = 4 * 2 ^ (L / 2 + L / 2) := by rw [pow_add]; ring
    _ ≤ 4 * 2 ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- If 2^s ≤ ⌊log₂(n+2)⌋ then ⌊log₂(n+2)⌋·2^s ≤ 8·(n + 2^s). -/
theorem log2_mul_two_pow_le {n s : ℕ} (hs : 2 ^ s ≤ Nat.log2 (n + 2)) : Nat.log2 (n + 2) * 2 ^ s ≤ 8 * (n + 2 ^ s) := by
  have h1 : 2 ^ Nat.log2 (n + 2) ≤ n + 2 := Nat.log2_self_le (by omega)
  have h2 := sq_le_four_mul_two_pow (Nat.log2 (n + 2))
  have h3 : Nat.log2 (n + 2) * 2 ^ s ≤ Nat.log2 (n + 2) * Nat.log2 (n + 2) := Nat.mul_le_mul_left _ hs
  have h4 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  omega

/-- 2^(sOf n) ≤ ⌊log₂(n+2)⌋, for every n. -/
public theorem two_pow_sOf_le (n : ℕ) : 2 ^ sOf n ≤ Nat.log2 (n + 2) := by
  have hmono : Nat.log2 n ≤ Nat.log2 (n + 2) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hs : sOf n ≤ Nat.log2 (Nat.log2 n) := by unfold sOf; omega
  by_cases h0 : Nat.log2 n = 0
  · have : sOf n = 0 := by
      have : Nat.log2 (Nat.log2 n) = 0 := by rw [h0]; rfl
      omega
    rw [this]
    exact (Nat.le_log2 (by omega)).2 (by omega)
  · calc 2 ^ sOf n ≤ 2 ^ Nat.log2 (Nat.log2 n) := Nat.pow_le_pow_right (by norm_num) hs
      _ ≤ Nat.log2 n := Nat.log2_self_le h0
      _ ≤ _ := hmono

/-- The arithmetic, for one n. Let 2^s ≤ ⌊log₂(n+2)⌋ and E·2^s ≤ C₀·(n + 2^s). Then the time
q·(25(n+2)^4 + 2^E)^q of the padded machine
is at most q·2^e' for e' = q·(E + 4·⌊log₂(n+2)⌋ + 10), and e'·2^s ≤ q·(C₀ + 42)·(n + 2^s). -/
public theorem padded_time_le (q C₀ : ℕ) {n s E : ℕ} (hs : 2 ^ s ≤ Nat.log2 (n + 2)) (hE : E * 2 ^ s ≤ C₀ * (n + 2 ^ s)) :
    q * (25 * (n + 2) ^ 4 + 2 ^ E) ^ q ≤ q * 2 ^ (q * (E + 4 * Nat.log2 (n + 2) + 10)) ∧
      q * (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s ≤ q * (C₀ + 42) * (n + 2 ^ s) := by
  constructor
  · have h2 : (n + 2) ^ 4 ≤ 2 ^ (4 * Nat.log2 (n + 2) + 4) := by
      calc (n + 2) ^ 4 ≤ (2 ^ (Nat.log2 (n + 2) + 1)) ^ 4 := Nat.pow_le_pow_left Nat.lt_log2_self.le 4
        _ = 2 ^ (4 * Nat.log2 (n + 2) + 4) := by rw [← pow_mul]; congr 1; ring
    have h3 : 25 * (n + 2) ^ 4 ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) := by
      calc 25 * (n + 2) ^ 4 ≤ 2 ^ 5 * 2 ^ (4 * Nat.log2 (n + 2) + 4) := Nat.mul_le_mul (by norm_num) h2
        _ = 2 ^ (4 * Nat.log2 (n + 2) + 9) := by rw [← pow_add]; congr 1; ring
        _ ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ E ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 25 * (n + 2) ^ 4 + 2 ^ E ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 10) := by
      have : 2 ^ (E + 4 * Nat.log2 (n + 2) + 10) = 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) * 2 := pow_succ 2 _
      omega
    calc q * (25 * (n + 2) ^ 4 + 2 ^ E) ^ q ≤ q * (2 ^ (E + 4 * Nat.log2 (n + 2) + 10)) ^ q :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 q)
      _ = _ := by rw [← pow_mul, Nat.mul_comm q (E + 4 * Nat.log2 (n + 2) + 10)]
  · have h1 := log2_mul_two_pow_le hs
    have h2 : (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s ≤ (C₀ + 42) * (n + 2 ^ s) := by
      calc (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s
          = E * 2 ^ s + 4 * (Nat.log2 (n + 2) * 2 ^ s) + 10 * 2 ^ s := by ring
        _ ≤ C₀ * (n + 2 ^ s) + 4 * (8 * (n + 2 ^ s)) + 10 * (n + 2 ^ s) := by
            have : 2 ^ s ≤ n + 2 ^ s := Nat.le_add_left _ _
            omega
        _ = (C₀ + 42) * (n + 2 ^ s) := by ring
    calc q * (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s = q * ((E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s) := Nat.mul_assoc _ _ _
      _ ≤ q * ((C₀ + 42) * (n + 2 ^ s)) := Nat.mul_le_mul_left _ h2
      _ = _ := (Nat.mul_assoc _ _ _).symm

variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

/-- Without division. Let `e` and `A` be polynomial-time, and let E be a function of the number n of
variables with
E n · 2^(sOf n) ≤ C₀ · (n + 2^(sOf n)), that is E n ≤ C₀·n/2^(sOf n) + C₀. If on the code x of every
instance of 3-SAT e x ≤ E n, and
A (x, the list of 2^(e x) units) is the bit «satisfiable», then the rate statement holds with c =
3/19. -/
public theorem inRateTM_of_padded_mul (he : PolyT e) (hA : PolyT A) (C₀ : ℕ) (E : ℕ → ℕ)
    (hE : ∀ n, E n * 2 ^ sOf n ≤ C₀ * (n + 2 ^ sOf n))
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      e (enc φ) ≤ E n ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) : InRateTM (3 / 19) := by
  obtain ⟨N, q, hfin, hN⟩ := decidesTM_of_padded he hA
  exact inRateTM_of_mulForm N hfin q (q * (C₀ + 42)) _ (fun n => q * (E n + 4 * Nat.log2 (n + 2) + 10)) (hN E h)
    (fun n => (padded_time_le q C₀ (two_pow_sOf_le n) (hE n)).1) fun n => (padded_time_le q C₀ (two_pow_sOf_le n) (hE n)).2

/-- Let `e` (from bit strings to numbers) and `A` (from a bit string and a list of units to a bit)
be polynomial-time. If on the code x
of every instance of 3-SAT on n variables e x ≤ C₀ · (n / 2^(sOf n) + 1) (division rounded down),
and A (x, the list of 2^(e x) units) is
the bit «satisfiable», then one Turing machine decides 3-SAT within C·2^{C·n/(log₂(n+2))^{3/19}}
steps, for some constant C. -/
public theorem inRateTM_of_padded (he : PolyT e) (hA : PolyT A) (C₀ : ℕ)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      e (enc φ) ≤ C₀ * (n / 2 ^ sOf n + 1) ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) : InRateTM (3 / 19) := by
  refine inRateTM_of_padded_mul he hA C₀ (fun n => C₀ * (n / 2 ^ sOf n + 1)) (fun n => ?_) h
  have h1 : n / 2 ^ sOf n * 2 ^ sOf n ≤ n := Nat.div_mul_le_self _ _
  calc C₀ * (n / 2 ^ sOf n + 1) * 2 ^ sOf n = C₀ * (n / 2 ^ sOf n * 2 ^ sOf n + 2 ^ sOf n) := by ring
    _ ≤ C₀ * (n + 2 ^ sOf n) := Nat.mul_le_mul_left _ (Nat.add_le_add_right h1 _)

end PaddedDescent
