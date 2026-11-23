/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.End.Thm
import Nc.RunMn

/-!
# Roots and logarithms; substitutions at a code
-/

set_option linter.unusedSectionVars false

namespace NS1

open Finset MvPolynomial

variable {A : Type} [CommRing A]

/-- The largest number whose power is at most `M`. -/
theorem exists_root (B Z₀ M : ℕ) (hB : 0 < B) (hM : Z₀ ^ B ≤ M) : ∃ Z, Z₀ ≤ Z ∧ Z ^ B ≤ M ∧ M < (Z + 1) ^ B := by
  have hex : ∃ n, M < n ^ B := ⟨M + 1, lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_self_pow (by omega) _)⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n, M < n ^ B ∧ ∀ k < n, ¬ M < k ^ B := by
    classical
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hn
    omega
  obtain ⟨Z, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨Z, ?_, not_lt.1 (hmin Z (Nat.lt_succ_self Z)), hn⟩
  by_contra hlt
  have h1 : (Z + 1) ^ B ≤ Z₀ ^ B := Nat.pow_le_pow_left (by omega) B
  have h2 : M < (Z + 1) ^ B := hn
  omega

theorem aux3 {v : ℕ} (hv : 2 ≤ v) : v + 1 ≤ v ^ 2 := by nlinarith

theorem eval_code1 {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] {bt : Bool → Γ}
    (hb : Function.Injective bt) (N : ℕ) (w : List Bool) (p : MvPolynomial (Fin N × Option Γ) K) :
    eval (codeB K N w) (aeval (letS K bt N) p) =
      eval (fun q => if Nc.code1 N (w.map bt) q then (1 : K) else 0) p := by
  rw [eval_sub hb]
  congr 2
  funext q
  simp [Nc.code, Nc.code1, Nc.wordOf]

/-- A substitution of affine polynomials followed by the naming of letters by bits is affine. -/
theorem isAffine_aeval_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ)
    {p : MvPolynomial (Fin N × Option Γ) K} (hp : Nc.IsAffine p) : Nc.IsAffine (aeval (letS K bt N) p) := by
  rcases hp with ⟨b, rfl⟩ | ⟨i, a, b, rfl⟩
  · exact Or.inl ⟨b, by simp [algebraMap_eq]⟩
  · rw [map_add, map_mul, aeval_C, aeval_C, aeval_X]
    rcases isAffine_letS (K := K) bt N i with ⟨b', hb'⟩ | ⟨j, a', b', hb'⟩
    · exact Or.inl ⟨a * b' + b, by simp [hb']⟩
    · exact Or.inr ⟨j, a * a', a * b' + b, by simp [hb']; ring⟩

/-- If `M ≤ v ^ b` and `(lg M) ^ (2 * b * E * a) ≤ M`, then `(lg v) ^ (E * (a + 1)) ≤ v` at large `v`. -/
theorem lg_pow_transport {v M b E a : ℕ} (hb : b ≠ 0) (hvM : v ≤ M) (hMv : M ≤ v ^ b)
    (ha : lg M ^ (2 * b * E * a) ≤ M) (hv : lg v ^ (2 * E) ≤ v) : lg v ^ (E * (a + 1)) ≤ v := by
  have h1 : lg v ^ (2 * E * a) ≤ v := by
    refine (Nat.pow_le_pow_iff_left hb).1 ?_
    calc (lg v ^ (2 * E * a)) ^ b ≤ (lg M ^ (2 * E * a)) ^ b :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left (lg_mono hvM) _) _
      _ = lg M ^ (2 * b * E * a) := by rw [← pow_mul]; congr 1; ring
      _ ≤ v ^ b := ha.trans hMv
  refine (Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num)).1 ?_
  calc (lg v ^ (E * (a + 1))) ^ 2 = lg v ^ (2 * E * a) * lg v ^ (2 * E) := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ v * v := Nat.mul_le_mul h1 hv
    _ = v ^ 2 := (pow_two v).symm

end NS1
