/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Monotone.Basic

/-! Polynomial bounds: functions ℕ → ℕ below c·(n+1)^c for some c, and their closure properties. -/

@[expose] public section

namespace Groundwork

/-- t is below a polynomial. -/
def PB (t : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, t n ≤ c * (n + 1) ^ c

namespace PB

variable {t s : ℕ → ℕ}

/-- The bound a·(n+1)^b grows with a and with b. -/
theorem bound_le {a b a' b' n : ℕ} (ha : a ≤ a') (hb : b ≤ b') : a * (n + 1) ^ b ≤ a' * (n + 1) ^ b' :=
  Nat.mul_le_mul ha (Nat.pow_le_pow_right (Nat.succ_pos n) hb)

/-- A bound of this form put into another one is again below a bound of this form. -/
theorem bound_comp (c c' n : ℕ) : c * (c' * (n + 1) ^ c' + 1) ^ c ≤ (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by
  have h1 : 1 ≤ (n + 1) ^ c' := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h2 : c' * (n + 1) ^ c' + 1 ≤ (c' + 1) * (n + 1) ^ c' := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left h1 _
  calc c * (c' * (n + 1) ^ c' + 1) ^ c ≤ c * ((c' + 1) * (n + 1) ^ c') ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 c)
    _ = (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by rw [Nat.mul_pow, ← pow_mul, Nat.mul_assoc]

theorem const (a : ℕ) : PB fun _ => a := by
  exact ⟨a, fun n => Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos n))⟩

theorem id' : PB fun n => n := by
  refine ⟨1, fun n => ?_⟩
  rw [pow_one, Nat.one_mul]
  exact Nat.le_succ n

theorem add (ht : PB t) (hs : PB s) : PB fun n => t n + s n := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨c + c', fun n => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hc n).trans (bound_le le_rfl (Nat.le_add_right _ _)))
    ((hc' n).trans (bound_le le_rfl (Nat.le_add_left _ _)))

theorem mul (ht : PB t) (hs : PB s) : PB fun n => t n * s n := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨c * c' + (c + c'), fun n => ?_⟩
  calc t n * s n ≤ c * (n + 1) ^ c * (c' * (n + 1) ^ c') := Nat.mul_le_mul (hc n) (hc' n)
    _ = c * c' * (n + 1) ^ (c + c') := by rw [pow_add]; ring
    _ ≤ _ := bound_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem pow (ht : PB t) (k : ℕ) : PB fun n => t n ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul ht

theorem comp (ht : PB t) (hs : PB s) : PB fun n => t (s n) := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨c * (c' + 1) ^ c + c' * c, fun n => ?_⟩
  calc t (s n) ≤ c * (s n + 1) ^ c := hc _
    _ ≤ c * (c' * (n + 1) ^ c' + 1) ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ (hc' n)) c)
    _ ≤ (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := bound_comp c c' n
    _ ≤ _ := bound_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- The bound c·(n+1)^c is itself below a polynomial, and it is monotone in n. -/
theorem mono_bound (c : ℕ) : PB (fun n => c * (n + 1) ^ c) ∧ Monotone fun n => c * (n + 1) ^ c := by
  exact ⟨⟨c, fun _ => le_rfl⟩, fun _ _ h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ h) c)⟩

end PB

end Groundwork
