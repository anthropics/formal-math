/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Toy.Defs

/-! # A toy recursion: the sum

What the proofs of Toy/Meets.lean need about `sumF`: it is the sum over all bit strings of length ℓ,
it reads only the entries of these strings, it is at most 2^ℓ times the largest entry, and the value
of a callee is the sum over the strings that begin with its bit. -/

public section

namespace QueryMachines.Tower.Toy

open Groundwork

/-- F(ℓ, f) is the sum of f over all bit strings of length ℓ. -/
theorem sumF_eq : ∀ (l : ℕ) (f : List Bool → Option ℕ), sumF l f = ((words l).map fun q => (f q).getD 0).sum
  | 0, f => by simp [sumF, words]
  | l + 1, f => by simp [sumF, words, sumF_eq l, List.map_map, Function.comp_def]

/-- F(ℓ, f) reads only the entries of the strings of length ℓ. -/
theorem sumF_congr : ∀ (l : ℕ) (f g : List Bool → Option ℕ), (∀ q, q.length = l → f q = g q) → sumF l f = sumF l g
  | 0, f, g, h => by simp only [sumF, h [] rfl]
  | l + 1, f, g, h => by
    simp only [sumF]
    rw [sumF_congr l _ _ fun q hq => h (false :: q) (by simp [hq]), sumF_congr l _ _ fun q hq => h (true :: q) (by simp [hq])]

/-- F(ℓ, f) is at most 2^ℓ times a bound on the entries. -/
theorem sumF_le (M0 : ℕ) : ∀ (l : ℕ) (f : List Bool → Option ℕ), (∀ q, q.length = l → ∃ a, a ≤ M0 ∧ f q = some a) → sumF l f ≤ 2 ^ l * M0
  | 0, f, h => by
    obtain ⟨a, ha, e⟩ := h [] rfl
    simp only [sumF, e, Option.getD_some]; omega
  | l + 1, f, h => by
    have h0 := sumF_le M0 l (fun q => f (false :: q)) fun q hq => h (false :: q) (by simp [hq])
    have h1 := sumF_le M0 l (fun q => f (true :: q)) fun q hq => h (true :: q) (by simp [hq])
    simp only [sumF, pow_succ]
    have e : 2 ^ l * 2 * M0 = 2 ^ l * M0 + 2 ^ l * M0 := by rw [Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
    omega

/-- The value of a callee is the sum over the strings that begin with its bit. -/
theorem val_child (ℓ0 M0 l : ℕ) (b : Bool) (f : List Bool → Option ℕ) : (spec ℓ0 M0).val (l, b) ((spec ℓ0 M0).tab (l, b) f) = sumF l fun q => f (b :: q) :=
  sumF_congr l _ _ fun _ hq => if_pos hq

end QueryMachines.Tower.Toy
