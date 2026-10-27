/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.RunDefs

/-! # Integers determined by their residues modulo a power of 2

An integer of absolute value below 2^{β−1} is determined by its residue modulo 2^β, an integer in
[0, 2^n] by its residue modulo 2^{n+1}, and exact division by 2^r carries a congruence over. -/

public section

namespace ClauseBound.ParityChecks

open Finset _root_.ParityChecks

namespace Congr

end Congr

open Congr

variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)

/-- A number of absolute value below 2^{β−1} is the balanced representative of any number congruent
to it modulo 2^β. -/
theorem bal_eq {β : ℕ} (hβ : 1 ≤ β) {a b : ℤ} (ha : |a| < 2 ^ (β - 1)) (hab : b ≡ a [ZMOD 2 ^ β]) : bal β b = a := by
  have hN : (2 : ℤ) ^ β = 2 * 2 ^ (β - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 := abs_lt.1 ha
  have h2 : (b + 2 ^ (β - 1)) % 2 ^ β = (a + 2 ^ (β - 1)) % 2 ^ β := hab.add_right _
  unfold bal
  rw [h2, Int.emod_eq_of_lt (by linarith) (by rw [hN]; linarith)]
  ring

/-- A number in [0, 2^n] is the remainder modulo 2^{n+1} of any number congruent to it. -/
theorem emod_eq {n : ℕ} {a b : ℤ} (h0 : 0 ≤ a) (ha : a ≤ 2 ^ n) (hab : b ≡ a [ZMOD 2 ^ (n + 1)]) : b % 2 ^ (n + 1) = a := by
  have h : b % 2 ^ (n + 1) = a % 2 ^ (n + 1) := hab
  rw [h, Int.emod_eq_of_lt h0]
  have : (0 : ℤ) < 2 ^ n := by positivity
  rw [pow_succ]
  linarith

/-- If a ≡ 2^r·b modulo 2^{β+r}, then a/2^r ≡ b modulo 2^β (the division is exact). -/
theorem div_congr {β r : ℕ} {a b : ℤ} (h : a ≡ 2 ^ r * b [ZMOD 2 ^ (β + r)]) : a / 2 ^ r ≡ b [ZMOD 2 ^ β] := by
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.1 h)
  have ha : a = 2 ^ r * (b - 2 ^ β * t) := by
    have : a = 2 ^ r * b - 2 ^ (β + r) * t := by linarith
    rw [this, pow_add]
    ring
  have h2 : (2 : ℤ) ^ r ≠ 0 := by positivity
  rw [ha, Int.mul_ediv_cancel_left _ h2]
  refine Int.modEq_iff_dvd.2 ⟨t, ?_⟩
  ring

end ClauseBound.ParityChecks
