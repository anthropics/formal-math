/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.PadRate
public import PaddedDescent.BrutePad
import ToTuring.Poly.Decode

/-! The rate statement reduced to one function, in one theorem. `inRateTM_of_algorithm`: fix numbers
C₀ and s₀ with 2^s₀ ≤ C₀. Let A be a
polynomial-time function (`PolyT`) of a bit string and a pad. Suppose that for every n with sOf n ≥
s₀ and every instance φ of 3-SAT on n
variables, A applied to the code of φ and the pad of length 2^(C₀·(n / 2^(sOf n) + 1)) returns the
bit «satisfiable». Then
`Sat3.InRateTM (3/19)` holds. For the n with sOf n < s₀ the machine uses exhaustive search, for
which that pad is long enough.
-/

namespace PaddedDescent

open Groundwork Groundwork.Decode Sat3 Turing

/-- The logarithm of the length of the pad, as a function of the number n of variables: C₀·(n /
2^(sOf n) + 1), division rounded down. -/
@[expose] public def padLog (C₀ n : ℕ) : ℕ := C₀ * (n / 2 ^ sOf n + 1)

/-- The same, read off the input string. -/
@[expose] public def eOf (C₀ : ℕ) (x : List Bool) : ℕ := padLog C₀ (nOf x)

/-- `sOf` of a polynomial-time function is polynomial-time. -/
public theorem sOf_polyT {α : Type} [Enc α] {f : α → ℕ} (hf : PolyT f) : PolyT fun x => sOf (f x) :=
  PolyT.div (PolyT.mul (PolyT.const 3) (PolyT.sub (PolyT.log2' (PolyT.log2' hf)) (PolyT.const 911))) (PolyT.const 19)

/-- The logarithm of the length of the pad is computed from the input in polynomial time. -/
public theorem eOf_polyT (C₀ : ℕ) : PolyT (eOf C₀) := by
  have h1 := nOf_polyT
  have h2 : PolyT fun x : List Bool => sOf (nOf x) := sOf_polyT h1
  unfold eOf padLog; fun_prop

/-- On the code of an instance on n variables, `eOf` is `padLog` of n. -/
public theorem eOf_enc (C₀ : ℕ) {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : eOf C₀ (enc φ) = padLog C₀ n := by
  rw [eOf, nOf_enc h]

/-- If 2^(sOf n) ≤ C₀ then n ≤ C₀·(n / 2^(sOf n) + 1): the pad is long enough for exhaustive search. -/
public theorem le_padLog {C₀ n : ℕ} (h : 2 ^ sOf n ≤ C₀) : n ≤ padLog C₀ n := by
  have h1 : n < 2 ^ sOf n * (n / 2 ^ sOf n + 1) := Nat.lt_mul_div_succ n (Nat.two_pow_pos _)
  exact h1.le.trans (Nat.mul_le_mul_right _ h)

/-- The algorithm with its two branches: exhaustive search where sOf n < s₀, and A elsewhere. -/
@[expose] public def withBrute (s₀ : ℕ) (A : List Bool × List Unit → Bool) (p : List Bool × List Unit) : Bool :=
  bif decide (sOf (nOf p.1) < s₀) then bruteA p else A p

/-- The algorithm with its two branches is polynomial-time if `A` is. -/
public theorem withBrute_polyT (s₀ : ℕ) {A : List Bool × List Unit → Bool} (hA : PolyT A) : PolyT (withBrute s₀ A) := by
  have h1 := nOf_polyT
  have h2 : PolyT fun p : List Bool × List Unit => sOf (nOf p.1) := sOf_polyT (by fun_prop)
  have h3 := bruteA_polyT
  unfold withBrute; fun_prop

/-- The reduction. Let 2^s₀ ≤ C₀ and let `A` be a polynomial-time function of a bit string and a
list of units. If for every n with
sOf n ≥ s₀ and every instance φ of 3-SAT on n variables A (code of φ, the list of 2^(C₀·(n / 2^(sOf
n) + 1)) units) is the bit «satisfiable»,
then one Turing machine decides 3-SAT within C·2^{C·n/(log₂(n+2))^{3/19}} steps, for some constant
C. The division rounds down. -/
public theorem inRateTM_of_algorithm (C₀ s₀ : ℕ) (hC : 2 ^ s₀ ≤ C₀) {A : List Bool × List Unit → Bool} (hA : PolyT A)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → s₀ ≤ sOf n → (A (enc φ, pad (padLog C₀ n)) = true ↔ Satisfiable φ)) :
    InRateTM (3 / 19) := by
  refine inRateTM_of_padded (eOf_polyT C₀) (withBrute_polyT s₀ hA) C₀ fun n φ h3 => ?_
  rw [eOf_enc C₀ h3]
  refine ⟨le_rfl, ?_⟩
  by_cases hs : sOf n < s₀
  · have e1 : withBrute s₀ A (enc φ, pad (padLog C₀ n)) = bruteA (enc φ, pad (padLog C₀ n)) := by
      simp [withBrute, nOf_enc h3, hs]
    rw [e1]
    refine bruteA_enc_of_le h3 ?_
    have h4 : 2 ^ sOf n ≤ C₀ := (Nat.pow_le_pow_right (by norm_num) hs.le).trans hC
    simpa [pad] using Nat.pow_le_pow_right (by norm_num : 0 < 2) (le_padLog h4)
  · have e1 : withBrute s₀ A (enc φ, pad (padLog C₀ n)) = A (enc φ, pad (padLog C₀ n)) := by
      simp [withBrute, nOf_enc h3, hs]
    rw [e1]
    exact h n φ h3 (not_lt.1 hs)

end PaddedDescent
