/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatRateStatement
public import PaddedDescent.Params
public import ToTuring.EndLemmas

/-! # From an integer time bound to the rate statement, and what «2^{o(n)} with one machine» implies

1. `inRateTM_of_mulForm`: a machine with finite alphabets that decides 3-SAT within A·2^(e n) steps,
   where e n·2^(sOf n) ≤ C₁·(n + 2^(sOf n))
   (that is, A·2^(C₁·n / 2^(sOf n) + C₁) steps, in natural numbers without division; the arithmetic
   step is also proved in real numbers, `le_rateBound_of_real`)
   witnesses `Sat3.InRateTM (3/19)`, that is time C·2^{C·n/(log₂(n+2))^{3/19}}, for all n. The rate
   theorem uses
   `inRateTM_of_mulForm`, which `inRateTM_of_padded_mul` (proof/rates/PaddedDescent/PadRate.lean)
   applies.
2. Checks on `ThreeSatRateStatement.lean`: `rateBound` decreases when c grows, so the claim for c
   implies the claim for every c' ≤ c;
   and «2^{o(n)} with one machine» (`SubexpTM`) implies `InTimeTM δ` for every δ > 0, which refutes
   `ETH_TM`.

Only `ThreeSatStatement.lean`, `ThreeSatRateStatement.lean`, the definition of `sOf` and the file
`proof/machines/ToTuring/EndLemmas.lean` (monotonicity of
`DecidesTM`, and ¬ETH_TM ↔ ∀ δ > 0, InTimeTM δ) are used. -/

public section

namespace Sat3

open Turing
open scoped NNReal ENNReal

/-! ### The logarithm -/

/-- log₂(n+2) ≥ 1. -/
theorem one_le_logb (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  norm_num

/-- (log₂(n+2))^c > 0 for every real c. -/
theorem logb_rpow_pos (n : ℕ) (c : ℝ) : (0 : ℝ) < Real.logb 2 ((n : ℝ) + 2) ^ c :=
  Real.rpow_pos_of_pos (zero_lt_one.trans_le (one_le_logb n)) c

/-- m + 2 ≤ 2^(⌊log₂ m⌋ + 2), for every m (with `Nat.log2 0 = 0`). -/
theorem add_two_le_two_pow (m : ℕ) : m + 2 ≤ 2 ^ (Nat.log2 m + 2) := by
  have h1 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have h2 : 2 ^ 1 ≤ 2 ^ (Nat.log2 m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (Nat.log2 m + 2) = 2 * 2 ^ (Nat.log2 m + 1) := by ring
  omega

/-- log₂(n+2) ≤ 2^(⌊log₂⌊log₂ n⌋⌋ + 2), for every n. -/
theorem logb_le_two_pow (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2) := by
  have h1 : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log2 n + 2) := by exact_mod_cast add_two_le_two_pow n
  have h2 : (Nat.log2 n : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2) := by
    exact_mod_cast add_two_le_two_pow (Nat.log2 n)
  have h3 : Real.logb 2 ((n : ℝ) + 2) ≤ (Nat.log2 n : ℝ) + 2 := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)]
    refine h1.trans_eq ?_
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  exact h3.trans h2

/-- If p·(⌊log₂⌊log₂ n⌋⌋ + 2) ≤ q·(s+b) then (log₂(n+2))^{p/q} ≤ 2^{s+b}: so 2^{-s} ≤ 2^b /
(log₂(n+2))^{p/q}. -/
theorem logb_rpow_le_two_pow {p q b s n : ℕ} (hq : 0 < q) (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b)) :
    Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q) ≤ (2 : ℝ) ^ (s + b) := by
  have hL := one_le_logb n
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs' : (p : ℝ) * ((Nat.log2 (Nat.log2 n) + 2 : ℕ) : ℝ) ≤ q * ((s + b : ℕ) : ℝ) := by exact_mod_cast hs
  calc Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q)
      ≤ ((2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2)) ^ ((p : ℝ) / q) :=
        Real.rpow_le_rpow (by linarith) (logb_le_two_pow n) (by positivity)
    _ = (2 : ℝ) ^ (((Nat.log2 (Nat.log2 n) + 2 : ℕ) : ℝ) * ((p : ℝ) / q)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    _ ≤ (2 : ℝ) ^ ((s + b : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le one_le_two
        rw [mul_div_assoc', div_le_iff₀ hq']
        linarith
    _ = (2 : ℝ) ^ (s + b) := Real.rpow_natCast _ _

/-! ### From natural numbers to `rateBound` -/

/-- The arithmetic core, for one n. Let s be tied to n by p·(⌊log₂⌊log₂ n⌋⌋ + 2) ≤ q·(s+b). Then a
number t of steps that is at most
A·2^{C₁·n/2^s + C₁} (real exponent) is at most C·2^{C·n/(log₂(n+2))^{p/q}} with C = A·2^{C₁} +
C₁·2^b. -/
theorem le_rateBound_of_real {p q b A C₁ s n t : ℕ} (hq : 0 < q) (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b))
    (ht : (t : ℝ) ≤ A * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s + C₁)) :
    t ≤ rateBound (A * 2 ^ C₁ + C₁ * 2 ^ b) ((p : ℝ) / q) n := by
  unfold rateBound
  apply Nat.le_floor
  refine ht.trans ?_
  have hLpos := logb_rpow_pos n ((p : ℝ) / q)
  have hL := logb_rpow_le_two_pow hq hs
  generalize Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q) = L at hLpos hL ⊢
  have hA : (0 : ℝ) ≤ (A : ℝ) * 2 ^ C₁ := by positivity
  have hB : (0 : ℝ) ≤ (C₁ : ℝ) * 2 ^ b := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (C₁ : ℝ) * n / 2 ^ s ≤ (C₁ * 2 ^ b) * n / L := by
    calc (C₁ : ℝ) * n / 2 ^ s = (C₁ * 2 ^ b) * n / 2 ^ (s + b) := by
          rw [pow_add]
          field_simp
      _ ≤ (C₁ * 2 ^ b) * n / L := div_le_div_of_nonneg_left (by positivity) hLpos hL
  push_cast
  calc (A : ℝ) * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s + C₁)
      = (A * 2 ^ C₁) * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s) := by
        rw [Real.rpow_add two_pos, Real.rpow_natCast]
        ring
    _ ≤ (A * 2 ^ C₁ + C₁ * 2 ^ b) * (2 : ℝ) ^ ((A * 2 ^ C₁ + C₁ * 2 ^ b) * n / L) := by
      apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      refine h1.trans ?_
      apply div_le_div_of_nonneg_right _ hLpos.le
      apply mul_le_mul_of_nonneg_right (by linarith) hn

/-- The same in natural numbers and without division: the exponent e satisfies e·2^s ≤ C₁·(n + 2^s),
that is e ≤ C₁·n/2^s + C₁. -/
theorem le_rateBound_of_mul_le {p q b A C₁ s e n : ℕ} (hq : 0 < q)
    (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b)) (he : e * 2 ^ s ≤ C₁ * (n + 2 ^ s)) :
    A * 2 ^ e ≤ rateBound (A * 2 ^ C₁ + C₁ * 2 ^ b) ((p : ℝ) / q) n := by
  apply le_rateBound_of_real hq hs
  have he' : (e : ℝ) * 2 ^ s ≤ C₁ * (n + 2 ^ s) := by exact_mod_cast he
  have h1 : (e : ℝ) ≤ (C₁ : ℝ) * n / 2 ^ s + C₁ := by
    rw [← le_div_iff₀ (by positivity)] at he'
    refine he'.trans_eq ?_
    field_simp
  push_cast
  rw [← Real.rpow_natCast 2 e]
  gcongr
  exact one_le_two

/-- 3·(⌊log₂⌊log₂ n⌋⌋ + 2) ≤ 19·(sOf n + 146) for every n, also where `sOf n = 0`. (Recall `sOf n` =
3·(⌊log₂⌊log₂ n⌋⌋ − 911)/19, rounded down.) -/
theorem log2_log2_le_sOf (n : ℕ) : 3 * (Nat.log2 (Nat.log2 n) + 2) ≤ 19 * (PaddedDescent.sOf n + 146) := by
  unfold PaddedDescent.sOf
  omega

/-- A machine with finite alphabets that decides 3-SAT within t n ≤ A·2^(e n) steps, for any
exponents with e n · 2^(sOf n) ≤ C₁·(n + 2^(sOf n)), witnesses the rate statement with c = 3/19. -/
theorem inRateTM_of_mulForm (M : TM2ComputableAux Bool Bool) (hfin : ∀ k, Finite (M.tm.Γ k)) (A C₁ : ℕ) (t e : ℕ → ℕ)
    (h : DecidesTM M t) (ht : ∀ n, t n ≤ A * 2 ^ e n)
    (he : ∀ n, e n * 2 ^ PaddedDescent.sOf n ≤ C₁ * (n + 2 ^ PaddedDescent.sOf n)) : InRateTM (3 / 19) := by
  refine ⟨M, A * 2 ^ C₁ + C₁ * 2 ^ 146, hfin, h.mono fun n => (ht n).trans ?_⟩
  have := le_rateBound_of_mul_le (p := 3) (A := A) (by norm_num : 0 < 19) (log2_log2_le_sOf n) (he n)
  exact_mod_cast this

/-! ### Checks on the statement -/

/-- `rateBound` decreases when c grows. -/
theorem rateBound_anti (C : ℕ) {c c' : ℝ} (h : c' ≤ c) (n : ℕ) : rateBound C c n ≤ rateBound C c' n := by
  apply Nat.floor_le_floor
  have h1 : Real.logb 2 ((n : ℝ) + 2) ^ c' ≤ Real.logb 2 ((n : ℝ) + 2) ^ c :=
    Real.rpow_le_rpow_of_exponent_le (one_le_logb n) h
  have h2 := logb_rpow_pos n c'
  gcongr
  exact one_le_two

/-- The claim for an exponent c implies the claim for every smaller exponent c'. -/
theorem InRateTM.mono {c c' : ℝ} (h : InRateTM c) (hc : c' ≤ c) : InRateTM c' := by
  obtain ⟨M, C, hfin, hM⟩ := h
  exact ⟨M, C, hfin, hM.mono (rateBound_anti C hc)⟩

/-- «2^{o(n)} with one machine» implies `InTimeTM δ` for every δ > 0. -/
theorem SubexpTM.inTimeTM (h : SubexpTM) {δ : ℝ≥0} (hδ : 0 < δ) : InTimeTM δ := by
  obtain ⟨M, hfin, hM⟩ := h
  obtain ⟨c, hc⟩ := hM δ hδ
  exact ⟨M, c, hfin, hc⟩

/-- «2^{o(n)} with one machine» refutes the Exponential Time Hypothesis. -/
theorem SubexpTM.not_ETH_TM (h : SubexpTM) : ¬ ETH_TM := not_ETH_TM_iff.2 fun _ hδ => h.inTimeTM hδ

end Sat3
